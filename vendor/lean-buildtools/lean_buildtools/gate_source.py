"""Read-only Lean source gate, including the complete staged Git index."""
from __future__ import annotations

from collections import defaultdict, deque
from dataclasses import dataclass
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

from .axiom_policy import Policy, parse_policy, local_path
from .lean_source import mask_noncode

IDENT = re.compile(r"«[^»]*»|[^\W\d][\w']*|\d+|[@.{}():\[\]]", re.UNICODE)
BANNED = frozenset(('bv_decide', 'native_decide', 'ofReduceBool', 'ofReduceNat', 'trustCompiler', 'sorry', 'admit'))
BOUNDARIES = frozenset(('unsafe', 'extern', 'implemented_by'))
DECLARATIONS = frozenset(('def', 'theorem', 'lemma', 'abbrev', 'opaque', 'axiom', 'instance', 'structure', 'inductive'))


def unread_scopes(config):
    entries = config.get('unread', [])
    if not isinstance(entries, list): raise ValueError('unread must be a list')
    result = []
    for entry in entries:
        if not isinstance(entry, dict) or not isinstance(entry.get('reason'), str) or not entry['reason'].strip():
            raise ValueError('unread entries need a relative path and reason')
        result.append(dict(path=local_path(entry.get('path')), reason=entry['reason'], kind='unread_source'))
    return result


def is_unread(path, entries):
    return any(Path(path).is_relative_to(e['path']) for e in entries)


def cache_inventory(config):
    entries = config.get('upstream_caches', [])
    if not isinstance(entries, list): raise ValueError('upstream_caches must be a list')
    result = []
    for entry in entries:
        if not isinstance(entry, dict) or any(not isinstance(entry.get(k),str) or not entry[k].strip()
                                             for k in ('path','owner','pin','upstream')):
            raise ValueError('upstream caches need path, owner, exact pin and upstream provenance')
        path = local_path(entry['path'])
        if not re.fullmatch(r'(?:[0-9a-fA-F]{40}|[0-9a-fA-F]{64})',entry['pin']):
            raise ValueError('upstream cache pin must be a complete commit or SHA256')
        if entry.get('never_build_from_source') is not True or entry.get('maintained') is not False:
            raise ValueError('upstream inventory requires maintained=false and never_build_from_source=true')
        if 'vendor' in [part.lower() for part in Path(path).parts]:
            raise ValueError('maintained vendor directories stay in source scope')
        result.append(dict(entry,path=path))
    return result


@dataclass
class Source:
    path: str
    owner: str
    text: str | None
    physical: Path | None = None
    fingerprint: str | None = None

    @property
    def content(self):
        if self.text is not None: return self.text
        raw = self.physical.read_bytes()
        digest = hashlib.sha256(raw).hexdigest()
        if self.fingerprint and digest != self.fingerprint:
            raise ValueError('source changed during scan: '+self.path)
        self.fingerprint = digest
        return raw.decode('utf-8')

    @property
    def sha256(self):
        return self.fingerprint or hashlib.sha256(self.content.encode()).hexdigest()


def _git(root, *args):
    p = subprocess.run(['git', '-C', str(root), *args], capture_output=True)
    if p.returncode:
        raise ValueError('cannot read staged sources: ' + p.stderr.decode(errors='replace').strip())
    return p.stdout


def staged_sources(project, owner, *, revision=None, prefix='', unread=(), caches=(), progress=None):
    """Use blob ids, not worktree content; gitlinks use their pinned commit."""
    if revision is None:
        rows = _git(project, 'ls-files', '--stage', '-z')
    else:
        rows = _git(project, 'ls-tree', '-r', '-z', revision)
    files, links = [], []
    for raw in rows.split(b'\0'):
        if not raw:
            continue
        header, name = raw.split(b'\t', 1)
        fields = header.decode().split()
        mode = fields[0]
        if revision is None:
            oid, stage = fields[1:]
            if stage != '0':
                raise ValueError('unmerged Git index; resolve it before the gate')
        else:
            oid = fields[2]
        path = os.fsdecode(name)
        if Path(path).is_absolute() or '..' in Path(path).parts:
            raise ValueError('staged source escapes project: ' + path)
        # Do not request a protected blob, even if it is already in the index.
        if is_unread(prefix + path, unread) or is_unread(prefix + path, caches): continue
        if mode == '160000':
            links.append((path, oid))
        elif path.endswith('.lean') or path == 'AXIOMS.md':
            if mode not in ('100644', '100755'):
                raise ValueError('cannot inspect staged Lean/policy symlink: ' + prefix + path)
            files.append((path, oid))
    source, metadata = [], {}
    if files:
        p = subprocess.Popen(['git', '-C', str(project), 'cat-file', '--batch'], stdin=subprocess.PIPE,
                             stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        try:
            for path, oid in files:
                p.stdin.write((oid + '\n').encode()); p.stdin.flush()
                header = p.stdout.readline().split()
                if len(header) != 3 or header[1] != b'blob':
                    raise ValueError('missing staged blob: ' + prefix + path)
                size = int(header[2]); content = p.stdout.read(size)
                if len(content) != size or p.stdout.read(1) != b'\n':
                    raise ValueError('incomplete staged blob: ' + prefix + path)
                text = content.decode('utf-8')
                if path == 'AXIOMS.md':
                    metadata[prefix + path] = text
                else:
                    source.append(Source(prefix + path, owner, text, project / path))
                    if progress:progress('index',len(source),prefix+path)
            p.stdin.close(); p.wait(timeout=10)
            if p.returncode:
                raise ValueError('Git blob reader failed')
        finally:
            if p.poll() is None:
                p.terminate(); p.wait(timeout=10)
            for stream in (p.stdin, p.stdout, p.stderr):
                if stream is not None and not stream.closed:
                    stream.close()
    for path, oid in links:
        child = project / path
        if not child.is_dir():
            raise ValueError('initialize pinned submodule before gate: ' + prefix + path)
        nested, data = staged_sources(child, owner, revision=oid, prefix=prefix + path + '/', unread=unread, caches=caches, progress=progress)
        source.extend(nested); metadata.update(data)
    return source, metadata


def worktree_sources(project, owner, *, historical=(), providers=(), scan_project=True, unread=(), caches=(), progress=None):
    roots = [(project, owner, '')] if scan_project else []
    for provider in providers:
        path = Path(provider['path']).expanduser()
        if not path.is_absolute():
            path = project / path
        roots.append((path.resolve(), provider['owner'], '@' + provider['owner'] + '/'))
    historical_paths = [(project / entry['path']).resolve() for entry in historical]
    unread_paths = [(project / entry['path']).resolve() for entry in list(unread)+list(caches)]
    excluded = set(historical_paths+unread_paths)
    def omitted(path):
        return path in excluded or any(parent in excluded for parent in path.parents)
    sources, errors, skipped_links, seen = [], [], [], set()
    for root, label, prefix in roots:
        if omitted(root): continue
        if not root.is_dir():
            errors.append(dict(path=str(root), error='missing source root')); continue
        def failed(error):
            errors.append(dict(path=error.filename, error=str(error)))
        for here, dirs, files in os.walk(root, onerror=failed, followlinks=False):
            folder = Path(here)
            retained = []
            for name in sorted(dirs):
                path = folder / name
                if name in ('.git', '.lake', '.build', '.lean-buildtools', 'archive', '__pycache__'):continue
                linked=path.is_symlink()
                real=path.resolve() if linked else path
                if omitted(real):
                    continue
                if linked:
                    skipped_links.append(str(path)); continue
                retained.append(name)
            dirs[:] = retained
            for name in sorted(files):
                if not name.endswith('.lean'):
                    continue
                path = folder / name
                real = path.resolve() if path.is_symlink() else path
                if omitted(real):
                    continue
                if not any(real.is_relative_to(p) for p, _, _ in roots):
                    errors.append(dict(path=str(path), error='Lean symlink leaves declared source roots')); continue
                if real in seen:
                    continue
                seen.add(real)
                try:
                    # A nested explicit provider owns its copied source, even when reached through the repo walk.
                    chosen = max((item for item in roots if real.is_relative_to(item[0])), key=lambda item: len(item[0].parts))
                    base, source_owner, display = chosen
                    shown = str(real.relative_to(project)) if real.is_relative_to(project) else display + str(real.relative_to(base))
                    # Keep paths/hashes, not whole vendor trees in memory.
                    # Discovery is metadata-only. The inspection pass reads and
                    # hashes each file once, keeping source memory bounded.
                    sources.append(Source(shown, source_owner, None, real))
                    if progress:progress('discover',len(sources),shown)
                except (OSError, UnicodeError) as error:
                    errors.append(dict(path=str(path), error=str(error)))
    return sources, errors, skipped_links


def _name(tokens, index):
    parts = []
    while index < len(tokens):
        value = tokens[index][0]
        if value in ('@', '{', '}', ':', '(', ')', '[', ']', '.'):
            break
        parts.append(value[1:-1] if value.startswith('«') and re.fullmatch(r"[^\W\d][\w']*", value[1:-1]) else value); index += 1
        if index >= len(tokens) or tokens[index][0] != '.':
            break
        index += 1
    return '.'.join(parts), index


def inspect(source, policy, tool):
    text = source.content
    if not (policy.boundary_locations or policy.negative_controls) and not re.search(r'\b(?:bv_decide|native_decide|ofReduceBool|ofReduceNat|trustCompiler|sorry|admit|axiom|unsafe|extern|implemented_by|skipKernelTC)\b', text):
        return [], []
    masked = mask_noncode(text)
    tokens = [(m.group(), m.start(), m.end()) for m in IDENT.finditer(masked)]
    findings, imports, namespace, scopes = [], [], '', []
    current = None
    declaration_start, declaration_names, attributes = 0, set(), []
    lines = [0]
    lines.extend(m.end() for m in re.finditer('\n', masked))
    import bisect
    def location(token):
        row = bisect.bisect_right(lines, token[1]) - 1
        return dict(path=source.path, owner=source.owner, line=row + 1, column=token[1] - lines[row] + 1)
    def qualified(name):
        if name.startswith('_root_.'):
            return name[7:]
        return '.'.join(filter(None, (namespace, name)))
    for index, token in enumerate(tokens):
        value = token[0].strip('«»')
        previous = tokens[index-1][0] if index else None
        row = bisect.bisect_right(lines, token[1]) - 1
        lead = masked[lines[row]:token[1]].strip()
        if value == '[':
            attributes.append(previous == '@' or any(attributes) or bool(re.search(r'\battribute\s*$', lead)))
        elif value == ']' and attributes:
            attributes.pop()
        modifier_prefix=re.sub(r'@\[[^\]]*\]','',lead).strip()
        command = not modifier_prefix or all(w in ('public','private','protected','meta','noncomputable','unsafe','partial','nonrec') for w in modifier_prefix.split())
        if command and value in ('namespace', 'section', 'mutual'):
            scopes.append(namespace)
            if value == 'namespace':
                name, _ = _name(tokens, index + 1); namespace = qualified(name)
        elif command and value == 'end':
            namespace = scopes.pop() if scopes else ''
            current = None
        if value == 'import':
            cursor = index + 1
            if cursor < len(tokens) and tokens[cursor][0] == 'all': cursor += 1
            first = True
            while cursor < len(tokens) and (first or '\n' not in masked[token[2]:tokens[cursor][1]]):
                name, end = _name(tokens, cursor)
                if not name: break
                imports.append(dict(module=name, **location(token)))
                cursor = end; first = False
        if value in DECLARATIONS | {'example'} and previous != '.' and index not in declaration_names:
            name, end = _name(tokens, index + 1)
            declaration_names.update(range(index+1,end))
            current = qualified(name) if name else None
            declaration_start = token[1]
        base = value.rstrip("'")
        finding = None
        if base in BANNED:
            if base == 'admit':
                if value != 'admit' or token[0].startswith('«') or index in declaration_names or previous == '.':
                    continue
                line_end = masked.find('\n', token[2])
                after = masked[token[2]:line_end if line_end>=0 else len(masked)].strip()
                # The tactic has no arguments. A named function application is
                # an ordinary term, including inside an exact/refine expression.
                if after and not after.startswith((';','<;>','|',')',']','}')):
                    continue
                if lead:
                    if not re.search(r'(?:\bby|\btry|\brepeat|\ball_goals|\bany_goals|\bfocus|<;>|;|\||=>)\s*$',lead):
                        continue
                else:
                    prior = masked[declaration_start:token[1]]
                    if not re.search(r'\bby\b',prior) or re.search(r'\b(?:exact|apply|refine|change)\s*$',prior):
                        continue
            finding = dict(rule='forbidden_proof_token', token=value, severity='error', declaration=current)
        elif value == 'axiom':
            if previous == '.' or index in declaration_names: continue
            name, _ = _name(tokens, index + 1); name = qualified(name)
            entry = policy.exceptions.get(name)
            allowed = bool(entry and policy.allowed(name, tool=tool, declaration=name))
            if entry and entry['scope'] == 'tool':
                allowed = allowed and source.path in entry['locations']
            finding = dict(rule='axiom_declaration', token=value, severity='approved' if allowed else 'error', declaration=name)
        elif value in BOUNDARIES:
            if value in ('extern','implemented_by') and (previous == '.' or not any(attributes)):
                continue
            if value == 'unsafe':
                cursor = index + 1
                if cursor < len(tokens) and tokens[cursor][0] in ('partial', 'nonrec'): cursor += 1
                if cursor >= len(tokens) or tokens[cursor][0] not in DECLARATIONS | {'initialize', 'builtin_initialize'}:
                    # Aesop's unsafe rule priority is not a declaration modifier.
                    continue
            for offset in range(index + 1, min(index + 18, len(tokens))):
                if tokens[offset][0] in DECLARATIONS:
                    name, _ = _name(tokens, offset + 1)
                    current = qualified(name) if name else current; break
            approved = any(e['name'] == current and e['location'] == source.path and value in e['tokens']
                           for e in policy.implementations)
            finding = dict(rule='implementation_boundary', token=value, severity='approved' if approved else 'review', declaration=current,
                           note='Runtime/unsafe implementation boundary; full mode checks proof dependencies and axioms.')
        elif value == 'set_option':
            name, _ = _name(tokens, index + 1)
            if name == 'debug.skipKernelTC':
                approved = any(e['location'] == source.path for e in policy.negative_controls)
                finding = dict(rule='kernel_check_option', token=name, severity='approved' if approved else 'error', declaration=current)
        if finding:
            findings.append(dict(finding, tool_module=tool, **location(token)))
    return findings, imports


def source_report(project, owner=None, *, staged=False, policy=None, config=None, sources=None, progress=None):
    project = project.resolve(); owner = owner or project.name; config = config or {}
    unread = unread_scopes(config)
    caches = cache_inventory(config)
    errors, skipped_links = [], []
    if sources is None:
        if staged:
            sources, metadata = staged_sources(project, owner, unread=unread, caches=caches, progress=progress)
            text = metadata.get('AXIOMS.md', '')
            policy = parse_policy(text) if policy is None else policy
            historical = policy.historical
            sources = [s for s in sources if not any(Path(s.path).is_relative_to(e['path']) for e in historical)]
            if config.get('source_providers'):
                external, errors, skipped_links = worktree_sources(project, owner, historical=historical,
                    providers=config['source_providers'], scan_project=False, unread=unread, caches=caches, progress=progress)
                staged_paths = {s.path for s in sources}
                sources.extend(s for s in external if s.path not in staged_paths)
        else:
            text = (project / 'AXIOMS.md').read_text() if not is_unread('AXIOMS.md', unread) and (project / 'AXIOMS.md').exists() else ''
            policy = parse_policy(text) if policy is None else policy
            sources, errors, skipped_links = worktree_sources(project, owner, historical=policy.historical,
                                                               providers=config.get('source_providers', []), unread=unread, caches=caches, progress=progress)
    policy = policy or Policy()
    sources = [s for s in sources if not is_unread(s.path, unread+caches)]
    tools = list(policy.tool_roots) + list(config.get('tool_roots', []))
    for path in tools:
        p = Path(path)
        if p.is_absolute() or '..' in p.parts or p == Path('.'):
            raise ValueError('tool roots must be explicit proper subdirectories')
        if not any(Path(location).is_relative_to(p) for location in policy.boundary_locations):
            raise ValueError('tool root has no approved tool-boundary exception location: ' + path)
    is_tool = lambda path: any(Path(path).is_relative_to(Path(prefix)) for prefix in tools)
    findings, importers, by_path = [], defaultdict(list), {s.path: s for s in sources}
    valid_sources = []
    for index,source in enumerate(sources):
        try:
            rows, imports = inspect(source, policy, is_tool(source.path))
        except (OSError,UnicodeError,ValueError) as error:
            errors.append(dict(path=source.path,error=str(error)));continue
        valid_sources.append(source)
        findings.extend(rows)
        for item in imports:
            importers[item['module']].append((source.path,item['line'],item['column']))
        if progress:progress('inspect',index+1,source.path)
    # Resolve reverse imports lazily. Copied historical module names must not
    # create a quadratic cross-product of every possible caller/target pair.
    isolated = {e['location'] for e in policy.negative_controls}
    if policy.boundary_locations or isolated:
        explicit = {m['module']: m['source'] for m in config.get('modules', []) if isinstance(m, dict)}
        alias_counts = defaultdict(int)
        for path in by_path:
            parts = Path(path).with_suffix('').parts
            for index in range(len(parts)):
                alias = '.'.join(parts[index:])
                if alias in importers:alias_counts[alias]+=1
        def callers(path, uncertain, processed):
            parts = Path(path).with_suffix('').parts
            seen = set()
            for index in range(len(parts)):
                module = '.'.join(parts[index:])
                if module in explicit and explicit[module] != path: continue
                ambiguous = uncertain or (module not in explicit and alias_counts[module]>1)
                if module in processed and (processed[module] is False or ambiguous):continue
                processed[module] = ambiguous
                for caller,line,column in importers.get(module, ()):
                    if caller not in seen:
                        seen.add(caller);yield caller,line,column,ambiguous
        parent = {path: None for path in by_path if is_tool(path) or path in policy.boundary_locations or path in isolated}
        uncertain = {path:False for path in parent};processed={}
        first_import = {}
        pending = deque(parent)
        while pending:
            path = pending.popleft()
            for caller,line,column,ambiguous in callers(path,uncertain[path],processed):
                if caller not in parent or (uncertain[caller] and not ambiguous):
                    parent[caller] = path; uncertain[caller]=ambiguous
                    first_import[caller]=(line,column); pending.append(caller)
        negative_users, todo = set(isolated), deque(isolated)
        negative_uncertain={path:False for path in isolated};negative_processed={}
        while todo:
            path=todo.popleft()
            for caller,_,_,ambiguous in callers(path,negative_uncertain[path],negative_processed):
                if caller not in negative_users or (negative_uncertain[caller] and not ambiguous):
                    negative_users.add(caller); todo.append(caller)
                    negative_uncertain[caller]=ambiguous
        for path in sorted(negative_users - isolated):
            findings.append(dict(rule='ambiguous_negative_control_import' if negative_uncertain[path] else 'imports_negative_control',
                                 severity='review' if negative_uncertain[path] else 'error', path=path,
                                 owner=by_path[path].owner, line=1, column=1,
                                 note='No Lean module may import an approved invalid negative control.'))
        for path in sorted(parent):
            if path in isolated:
                continue
            if is_tool(path):
                continue
            if path in policy.boundary_locations:
                findings.append(dict(rule='unclassified_tool_boundary', severity='error', path=path,
                                     owner=by_path[path].owner, line=1, column=1,
                                     note='Approved tool-only file needs explicit tool_roots classification.'))
                continue
            chain, cursor = [path], parent[path]
            while cursor is not None:
                chain.append(cursor); cursor = parent[cursor]
            line,column = first_import.get(path,(1,1))
            findings.append(dict(rule='ambiguous_tool_import' if uncertain[path] else 'proof_imports_tool_boundary',
                                 severity='review' if uncertain[path] else 'error', path=path,
                                 owner=by_path[path].owner, line=line, column=column,
                                 dependency_path=chain,
                                 note='Ambiguous source module alias; full gate checks the actual resolved import graph.' if uncertain[path]
                                      else 'Tool-only exceptions cannot be imported or transitively relied on by proof modules.'))
    fatal = sum(f['severity'] == 'error' for f in findings) + len(errors)
    return dict(schema_version=1, mode='source_index' if staged else 'source_worktree',
                project=str(project), owner=owner, status='source_fail' if fatal else 'source_incomplete' if unread else 'source_pass',
                scope='Source-only; not an inherited-axiom or fresh-build CLEAR result.',
                source_files=len(sources), findings=findings, errors=errors, error_count=fatal+len(unread),
                import_reference_count=sum(len(rows) for rows in importers.values()),
                source_error_count=fatal, coverage_gap_count=len(unread), coverage_gaps=unread,
                review_count=sum(f['severity'] == 'review' for f in findings),
                historical=policy.historical, skipped_directory_symlinks=skipped_links,
                upstream_caches=caches,
                exception_names=sorted(policy.exceptions), policy_digest=policy.digest,
                implementation_exception_names=sorted(e['name'] for e in policy.implementations),
                negative_control_paths=sorted(e['location'] for e in policy.negative_controls),
                source_digest=hashlib.sha256(json.dumps(sorted((s.owner, s.path, s.sha256) for s in valid_sources), ensure_ascii=True).encode()).hexdigest())
