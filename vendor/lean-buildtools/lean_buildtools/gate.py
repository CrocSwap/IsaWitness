"""Standard Lake build followed by fresh raw-body axiom closure, with no seeds."""
from __future__ import annotations
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import time
from contextlib import contextmanager

from .axiom_policy import parse_policy
from .gate_source import source_report
from .gate_contexts import check_contexts
from .proof_graph import ProofGraph


GATE_BUDGET_SECONDS = 300
FRESH_JOB_BUDGET_SECONDS = 600


def configured_budget(config):
    budget = config.get('budget_s', GATE_BUDGET_SECONDS)
    if config.get('timing_model') == 'separate_build_gate_v1' and (budget != GATE_BUDGET_SECONDS or config.get('budget_exception') is not None):
        raise ValueError('separate timing requires the standard raw gate budget without legacy exceptions')
    if budget == GATE_BUDGET_SECONDS and not isinstance(budget, bool):
        return budget
    if (config.get('package') in {'secp256k1', 'secp256k1_foundations', 'secp256k1_hash_input', 'secp256k1_hash_output', 'secp256k1_runtime', 'secp256k1_closure'} and config.get('budget_exception') == 'E12'
            and budget == 600 and not isinstance(budget, bool)):
        return budget
    raise ValueError('unapproved gate budget; E12 applies only to approved secp packages at 600s')


def configured_total_budget(config, *, fresh=True):
    budget = configured_budget(config)
    model = config.get('timing_model', 'legacy_combined_v1')
    if model not in ('legacy_combined_v1', 'separate_build_gate_v1'):
        raise ValueError('unknown gate timing model')
    return FRESH_JOB_BUDGET_SECONDS if fresh and model == 'separate_build_gate_v1' else budget


class GateTimeout(ValueError):
    pass


@contextmanager
def deadline(seconds, label="full build plus gate"):
    """One wall-clock budget, including Python work and all child commands."""
    def expired(_signum, _frame):
        raise GateTimeout(f'{label} exceeded {seconds:g} seconds')
    handler = signal.signal(signal.SIGALRM, expired)
    prior = signal.getitimer(signal.ITIMER_REAL)
    signal.setitimer(signal.ITIMER_REAL, min(seconds, prior[0]) if prior[0] else seconds)
    started = time.monotonic()
    try:
        yield
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
        signal.signal(signal.SIGALRM, handler)
        if prior[0]:
            signal.setitimer(signal.ITIMER_REAL,
                             max(0.000001, prior[0] - (time.monotonic() - started)), prior[1])


def run(cmd, project, *, env=None):
    # A new session lets timeout cleanup address precisely this command and
    # its Lean descendants, without touching other agents' builds.
    child = subprocess.Popen([str(x) for x in cmd], cwd=project, env=env,
                             start_new_session=True)
    try:
        code = child.wait()
        if code:
            raise subprocess.CalledProcessError(code, cmd)
    except BaseException:
        try:
            os.killpg(child.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        child.wait()
        raise


def inventory(project, config):
    """Explicit active source roots, recursively expanded; archive is never active."""
    project = project.resolve()
    roots = config.get('source_roots')
    if not isinstance(roots, list) or not roots:
        raise ValueError('gate.json needs nonempty source_roots (Lean files or directories)')
    src_dir = (project / config.get('src_dir', '.')).resolve()
    if not src_dir.is_relative_to(project):
        raise ValueError('src_dir escapes project')
    modules = {}
    for name in roots:
        path = (src_dir / name).resolve()
        if not path.is_relative_to(src_dir) or 'archive' in path.relative_to(project).parts:
            raise ValueError('source root escapes active project: '+name)
        if not path.exists():
            raise ValueError('missing source root: '+name)
        files = [path] if path.is_file() else sorted(path.rglob('*.lean'))
        for file in files:
            if file.suffix != '.lean' or file.is_symlink() or not file.resolve().is_relative_to(src_dir):
                raise ValueError('invalid active Lean source: '+str(file))
            if any(p in ('archive', '.lake', '.git') for p in file.relative_to(src_dir).parts):
                continue
            module = '.'.join(file.relative_to(src_dir).with_suffix('').parts)
            modules[module] = str(file.relative_to(project))
    if not modules:
        raise ValueError('active source inventory is empty')
    return modules


def check_built_inventory(project, owned):
    """Fresh default build products are the authoritative active own closure."""
    build = project/'.lake/build/lib/lean'
    built = {'.'.join(p.relative_to(build).with_suffix('').parts)
             for p in build.rglob('*.olean')}
    if built != set(owned):
        raise ValueError('gate source inventory differs from default build: '+
                         json.dumps(dict(unlisted=sorted(built-set(owned)),
                                         missing=sorted(set(owned)-built))))


def hashes(paths):
    result = {}
    for path in sorted(set(paths)):
        digest = hashlib.sha256()
        with Path(path).open('rb') as stream:
            while block := stream.read(1024*1024):
                digest.update(block)
        result[str(path)] = digest.hexdigest()
    return result


def extract(project, output, modules, metadata_only):
    output.mkdir()
    request = output/'request.json'
    request.write_text(json.dumps(dict(modules=list(modules), output=str(output/'graph.jsonl'),
                                      metadata_only=metadata_only, artifacts=[])))
    source = output/'Graph.lean'
    template = (Path(__file__).parent/'lean/AxiomGraph.lean').read_text()
    source.write_text(template+'\nrun_cmd do\n  liftIO <| BuildTools.AxiomGraph.run '+json.dumps(str(request))+'\n')
    run(['lake', 'env', 'lean', '-M12288', '-R', output, source], project)
    rows = {}; complete = False
    with (output/'graph.jsonl').open() as stream:
        for line in stream:
            row = json.loads(line)
            if complete: raise ValueError('data after graph completion')
            if row['event'] == 'module':
                if row['module'] in rows: raise ValueError('duplicate module')
                rows[row['module']] = row
            elif row['event'] == 'complete':
                complete = row['modules'] == len(rows)
    if not complete: raise ValueError('incomplete raw extraction')
    return rows


def _gate(project, output, *, config_path='gate.json', fresh=True, budget_s=None, total_budget_s=None, started_at=None, expected_config_bytes=None):
    budget_s = GATE_BUDGET_SECONDS if budget_s is None else budget_s
    total_budget_s = (FRESH_JOB_BUDGET_SECONDS if fresh else budget_s) if total_budget_s is None else total_budget_s
    started = time.monotonic() if started_at is None else started_at
    phases = []
    phase_start = started
    def phase(name):
        nonlocal phase_start
        now = time.monotonic()
        phases.append(dict(name=name, elapsed_s=now-phase_start))
        phase_start = now
    with deadline(max(0.000001, budget_s-(time.monotonic()-started)), "configuration preflight plus source scan"):
        config_file = project/config_path
        config_bytes = config_file.read_bytes()
        if expected_config_bytes is not None and config_bytes != expected_config_bytes:
            raise ValueError("gate configuration changed after timing preflight")
        config = json.loads(config_bytes)
        owned = inventory(project, config)
        policy_path = project/'AXIOMS.md'
        policy = parse_policy(policy_path.read_text() if policy_path.exists() else '')
        source = source_report(project)
        root_manifest = json.loads((project/'lake-manifest.json').read_text())
        package_name = root_manifest['name'].replace('«','').replace('»','')
        if config.get('package') != package_name:
            raise ValueError('gate package does not match Lake root package')
        result = dict(schema_version=1, mode='lake_raw_gate', status='fail', source=source,
                      fresh_own_build=fresh, modules=owned, method='fresh full-private raw bodies; cached axiom summaries unused')
        output.mkdir(parents=True, exist_ok=False)
        phase('source_scan_and_inventory')
    try:
        if source['error_count']:
            raise ValueError('source scan failed')
        # A fresh compile has the whole-job budget; scan plus raw checking
        # shares the separate gate budget. No check is omitted.
        try:
            if fresh:
                package = config.get('package')
                if not isinstance(package, str) or not package:
                    raise ValueError('gate.json needs package for the fresh own-package clean')
                run(['lake', 'clean', package], project)
            build_env = os.environ.copy()
            build_env.update(LAKE_ARTIFACT_CACHE='false', LAKE_RESTORE_ARTIFACTS='false')
            run(['lake', '--no-cache', 'build'], project, env=build_env)
        finally:
            phase('fresh_default_build' if fresh else 'incremental_default_build')
        scan_s = sum(p['elapsed_s'] for p in phases if p['name']=='source_scan_and_inventory')
        with deadline(max(0.000001, budget_s-scan_s), "source scan plus raw-body gate"):
            check_built_inventory(project, owned)
            phase('built_inventory')
            discovery = extract(project, output/'discovery', owned, True)
            if any(Path(row['path']).resolve().is_relative_to(project/'archive') for row in discovery.values()):
                raise ValueError('active closure imports archived code')
            for module in owned:
                expected = project/'.lake/build/lib/lean'/Path(*module.split('.')).with_suffix('.olean')
                if Path(discovery[module]['path']).resolve() != expected.resolve() or not expected.is_file():
                    raise ValueError('owned module did not resolve to its Lake build product: '+module)
            artifact_paths = [part for row in discovery.values() for part in row['parts']]
            before = hashes(artifact_paths)
            phase('artifact_discovery_and_hashes')
            actual = extract(project, output/'bodies', owned, False)
            if actual != discovery or hashes(artifact_paths) != before:
                raise ValueError('compiled artifacts changed during collection')
            after_source = source_report(project)
            if any(after_source[k] != source[k] for k in ('source_digest', 'policy_digest')) or config_file.read_bytes() != config_bytes:
                raise ValueError('sources or gate configuration changed during build/collection')
            phase('raw_body_collection_and_stability')
            graph = ProofGraph(output/'graph.sqlite')
            try:
                graph.load(output/'bodies/graph.jsonl')
                tools = [m for m,p in owned.items() if any(Path(p).is_relative_to(t) for t in policy.tool_roots)]
                context_file = output/'lake-executable-contexts.json'
                run(['lake', 'run', 'lean-buildtools/gate-contexts', context_file], project)
                executables = json.loads(context_file.read_text())
                if not isinstance(executables, list) or any(not isinstance(name, str) for name in executables):
                    raise ValueError('invalid native Lake executable metadata')
                result['axioms'] = check_contexts(graph, owned, executables,
                    policy=policy, tool_modules=tools,
                    boundaries=[f for f in source['findings'] if f['rule']=='implementation_boundary'])
            finally:
                graph.close()
            phase('axiom_closure')
            result['artifacts_sha256'] = before
            result['status'] = 'pass' if result['axioms']['error_count']==0 else 'fail'
    except (ValueError, OSError, subprocess.CalledProcessError) as error:
        result['error'] = str(error)
    result['phases'] = phases
    result['elapsed_s'] = time.monotonic()-started
    result['budget_schema'] = config.get('timing_model', 'legacy_combined_v1')
    result['budget_s'] = budget_s
    result['total_budget_s'] = total_budget_s
    result['budget_exception'] = config.get('budget_exception')
    result['build_elapsed_s'] = sum(p['elapsed_s'] for p in phases
        if p['name'] in ('fresh_default_build', 'incremental_default_build'))
    result['gate_elapsed_s'] = max(0.0, result['elapsed_s']-result['build_elapsed_s'])
    timed_checks = result['gate_elapsed_s'] if result['budget_schema'] == 'separate_build_gate_v1' else result['elapsed_s']
    result['within_five_minutes'] = timed_checks <= min(300, budget_s)
    result['within_10_minutes'] = result['elapsed_s'] <= 600
    result['within_budget'] = (result['gate_elapsed_s'] <= budget_s and
                              result['elapsed_s'] <= total_budget_s)
    if not result['within_budget']:
        result['status'] = 'fail'
        result['error'] = ('source scan/raw gate or complete fresh-build job exceeded its budget')
    (output/'gate.json').write_text(json.dumps(result, indent=2)+'\n')
    print(f"axiom gate {result['status']}: {result['elapsed_s']:.3f}s; {output/'gate.json'}")
    return 0 if result['status']=='pass' else 1


def gate(project, output, *, config_path='gate.json', fresh=True):
    started = time.monotonic()
    try:
        with deadline(GATE_BUDGET_SECONDS):
            config_file = project/config_path
            configuration_bytes = config_file.read_bytes() if config_file.exists() else None
            configuration = json.loads(configuration_bytes) if configuration_bytes is not None else {}
            budget_s = configured_budget(configuration)
            total_budget_s = configured_total_budget(configuration, fresh=fresh)
        with deadline(max(0.000001, total_budget_s-(time.monotonic()-started))):
            return _gate(project, output, config_path=config_path, fresh=fresh,
                         budget_s=budget_s, total_budget_s=total_budget_s, started_at=started,
                         expected_config_bytes=configuration_bytes)
    except (GateTimeout, ValueError, OSError) as error:
        # Preflight work and writing the receipt are covered too. If timeout
        # occurs outside _gate's normal error handling, still emit a failure.
        output.mkdir(parents=True, exist_ok=True)
        result = dict(schema_version=1, mode='lake_raw_gate', status='fail',
                      fresh_own_build=False, error=str(error),
                      elapsed_s=time.monotonic()-started,
                      budget_s=locals().get('budget_s', GATE_BUDGET_SECONDS),
                      within_five_minutes=False, within_budget=False)
        (output/'gate.json').write_text(json.dumps(result, indent=2)+'\n')
        print(f"axiom gate fail: {result['elapsed_s']:.3f}s; {output/'gate.json'}")
        return 1
