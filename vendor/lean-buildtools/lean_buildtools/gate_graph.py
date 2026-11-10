"""One shared body closure for all owned declarations; no repeated root subgraphs."""
from collections import defaultdict, deque
import json

from .axiom_policy import Policy
from .proof_graph import conflicting_candidates, compatible_equations

KINDS = frozenset(('theorem', 'definition', 'opaque', 'axiom'))


def check_graph(graph, owned, *, policy=None, owners=None, tool_modules=(), boundaries=()):
    policy = policy or Policy(); owners = owners or {}; tools = set(tool_modules)
    modules = graph.modules()
    errors, roots = [], {}
    for module in owned:
        if module not in modules:
            errors.append(dict(kind='missing_owned_module', module=module)); continue
        for (data,) in graph.db.execute('SELECT data FROM declarations WHERE module=?', (module,)):
            row = json.loads(data)
            if row['kind'] in KINDS:
                roots[(module, row['name'])] = row
    pending = deque(name for _, name in roots)
    records, missing, ambiguous = {}, set(), {}
    while pending:
        name = pending.popleft()
        if name in records or name in missing: continue
        choices = graph.candidates(name)
        if not choices:
            missing.add(name); continue
        if conflicting_candidates(name,choices):
            ambiguous[name] = [c['module'] for c in choices]
        deps = set().union(*(set(c['dependencies']) for c in choices))
        records[name] = dict(choices[0], dependencies=sorted(deps), candidates=choices)
        pending.extend(deps)
    reverse = defaultdict(set)
    for name, row in records.items():
        for dependency in row['dependencies']: reverse[dependency].add(name)
    axioms = {name: set() for name in records}
    pending = deque()
    for name, row in records.items():
        if any(c['kind'] == 'axiom' for c in row['candidates']):
            axioms[name].add(name); pending.append(name)
    while pending:
        name = pending.popleft()
        for caller in reverse[name]:
            extra = axioms[name] - axioms[caller]
            if extra:
                axioms[caller].update(extra); pending.append(caller)
    errors.extend(dict(kind='missing_declaration', name=n) for n in sorted(missing))
    errors.extend(dict(kind='ambiguous_declaration', name=n, modules=ms) for n, ms in sorted(ambiguous.items()))
    declarations, violations = [], []
    all_axioms = sorted(set().union(*axioms.values()) if axioms else set())
    axids = {name: i for i, name in enumerate(all_axioms)}
    for (module, name), row in sorted(roots.items()):
        actual = axioms.get(name, set())
        extra = sorted(ax for ax in actual if not policy.allowed(ax, tool=module in tools, declaration=name))
        declarations.append(dict(name=name, module=module, kind=row['kind'],
                                 axioms=[axids[a] for a in sorted(actual)]))
        if extra:
            violations.append(dict(kind='unexpected_axioms', name=name, module=module, axioms=extra))
    # One reverse traversal gives a shared witness forest for all proof roots.
    # Extern/implemented_by source boundaries need an exact runtime exception;
    # unsafe/partial bodies beneath a proof always need review/approval.
    hazard = {}
    for name, row in records.items():
        if row['unsafe'] or row['partial']:
            hazard[name] = dict(kind='unsafe_or_partial_body', name=name, module=row['module'])
    for boundary in boundaries:
        name = boundary.get('declaration')
        if name and boundary['severity'] != 'approved':
            hazard[name] = dict(kind='unapproved_implementation_boundary', name=name,
                                path=boundary['path'], owner=boundary['owner'])
    parent = {name: None for name in hazard}
    pending = deque(parent)
    while pending:
        name = pending.popleft()
        for caller in reverse[name]:
            if caller not in parent:
                parent[caller] = name; pending.append(caller)
    proof_hits = []
    for (module, name), row in sorted(roots.items()):
        if row['kind'] == 'theorem' and module not in tools and name in parent:
            proof_hits.append(dict(name=name, module=module))
    if proof_hits:
        violations.append(dict(kind='proof_implementation_dependencies', roots=proof_hits,
                               witness_next={name: parent[name] for name in sorted(parent)},
                               boundaries=list(hazard.values())))
    # Enforce tool isolation on the actual compiler import DAG, including bridges.
    imports_reverse = defaultdict(set)
    for name, row in modules.items():
        for dependency in row['imports']: imports_reverse[dependency].add(name)
    reaches_tool, pending = set(tools), deque(tools)
    while pending:
        for caller in imports_reverse[pending.popleft()]:
            if caller not in reaches_tool:
                reaches_tool.add(caller); pending.append(caller)
    for module in sorted(set(owned) & (reaches_tool-tools)):
        violations.append(dict(kind='proof_module_imports_tool', module=module))
    origins = []
    for name in all_axioms:
        candidates = records[name]['candidates']
        origins.append(dict(name=name, modules=sorted({c['module'] for c in candidates}),
                            owners=sorted({owners.get(c['module'], 'UNKNOWN') for c in candidates})))
    # Share witness edges across roots instead of repeating whole paths per
    # declaration. A missing body path for a cached-only axiom is explicit.
    unexpected_names = {ax for v in violations if v['kind']=='unexpected_axioms' for ax in v['axioms']}
    witnesses = []
    for ax in sorted(unexpected_names):
        next_step = {ax: None}; pending = deque([ax])
        while pending:
            dependency = pending.popleft()
            for caller in reverse[dependency]:
                if caller not in next_step:
                    next_step[caller] = dependency; pending.append(caller)
        relevant = [dict(module=m,name=n) for m,n in roots if ax in axioms.get(n,set())]
        edges = {}
        for root in relevant:
            cursor = root['name']
            while cursor not in edges:
                edges[cursor] = next_step[cursor]
                if next_step[cursor] is None: break
                cursor = next_step[cursor]
        witnesses.append(dict(axiom=ax, roots=relevant, body_next=edges,
                              origin_modules=sorted({c['module'] for c in records.get(ax,{}).get('candidates',[])}),
                              scope='actual bodies' if relevant else 'cached summary only; no actual body path'))
    return dict(declarations=declarations, axiom_origins=origins, violations=violations,
                equation_replicas=[dict(name=n,modules=[c['module'] for c in r['candidates']],
                                       method='exact theorem identity; union of every proof body')
                                   for n,r in sorted(records.items()) if len(r['candidates'])>1 and compatible_equations(n,r['candidates'])],
                runtime_recursion_artifacts=[dict(name=n,module=r['module'],
                    classification='runtime implementation; theorem dependency checks remain enforced') for n,r in sorted(records.items())
                    if n.endswith('_unsafe_rec') and r['unsafe']],
                unexpected_axiom_witnesses=witnesses,
                errors=errors, reachable_declarations=len(records),
                owned_declarations=len(roots), error_count=len(errors)+len(violations))
