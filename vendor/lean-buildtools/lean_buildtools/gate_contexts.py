"""Check separate Lake executable environments without relaxing library checks."""
from collections import defaultdict, deque

from .gate_graph import check_graph


class GraphView:
    def __init__(self, graph, allowed):
        self.graph = graph
        self.allowed = set(allowed)
        self.db = graph.db

    def modules(self):
        return {name: row for name, row in self.graph.modules().items() if name in self.allowed}

    def candidates(self, name):
        return [row for row in self.graph.candidates(name) if row['module'] in self.allowed]


def check_contexts(graph, owned, executables=(), *, policy=None, owners=None,
                   tool_modules=(), boundaries=()):
    executables = set(executables) & set(owned)
    if not executables:
        return check_graph(graph, owned, policy=policy, owners=owners,
                           tool_modules=tool_modules, boundaries=boundaries)
    modules = graph.modules()
    libraries = set(owned) - executables

    def imports(root):
        seen, pending = set(), [root]
        while pending:
            module = pending.pop()
            if module in seen:
                continue
            if module not in modules:
                raise ValueError('missing compiled import module: '+module)
            seen.add(module)
            pending.extend(modules[module]['imports'])
        return seen

    missing = set(owned)-set(modules)
    if missing:
        raise ValueError('missing compiled owned module: '+', '.join(sorted(missing)))
    # One reverse traversal forbids hiding an executable dependency in a library.
    reverse = defaultdict(set)
    for name, row in modules.items():
        for dependency in row['imports']:
            reverse[dependency].add(name)
    reaches, pending = set(executables), deque(executables)
    while pending:
        for caller in reverse[pending.popleft()]:
            if caller not in reaches:
                reaches.add(caller); pending.append(caller)
    blocked = libraries & reaches
    if blocked:
        raise ValueError('library imports a separate executable context: '+', '.join(sorted(blocked)))
    by_path = {path: module for module, path in owned.items()} if isinstance(owned, dict) else {}
    scopes = [('library', set(modules)-executables, libraries)]
    scopes += [(name, imports(name), {name}) for name in sorted(executables)]
    reports = []
    for context, allowed, roots in scopes:
        if not roots:
            continue
        selected_boundaries = [row for row in boundaries
                               if by_path.get(row.get('path')) in allowed
                               or row.get('path') not in by_path]
        result = check_graph(GraphView(graph, allowed), roots, policy=policy, owners=owners,
                             tool_modules=set(tool_modules)&allowed,
                             boundaries=selected_boundaries)
        reports.append((context, result))

    # Preserve every owned declaration and its exact local axiom set. IDs are
    # reindexed only because each independently checked report has its own list.
    origins = {}
    for _, report in reports:
        for row in report['axiom_origins']:
            entry = origins.setdefault(row['name'], dict(name=row['name'], modules=set(), owners=set()))
            entry['modules'].update(row['modules']); entry['owners'].update(row['owners'])
    names = sorted(origins); ids = {name: index for index, name in enumerate(names)}
    output = dict(declarations=[], axiom_origins=[dict(name=name,
        modules=sorted(origins[name]['modules']), owners=sorted(origins[name]['owners'])) for name in names],
        violations=[], equation_replicas=[], runtime_recursion_artifacts=[],
        unexpected_axiom_witnesses=[], errors=[], reachable_declarations=0, owned_declarations=0,
        error_count=0, compiler_contexts=[])
    for context, report in reports:
        local = [row['name'] for row in report['axiom_origins']]
        for row in report['declarations']:
            output['declarations'].append(dict(row, context=context,
                axioms=[ids[local[index]] for index in row['axioms']]))
        for key in ['violations', 'equation_replicas', 'runtime_recursion_artifacts',
                    'unexpected_axiom_witnesses', 'errors']:
            output[key].extend(dict(row, context=context) for row in report[key])
        for key in ['reachable_declarations', 'owned_declarations', 'error_count']:
            output[key] += report[key]
        output['compiler_contexts'].append(dict(context=context,
            owned_declarations=report['owned_declarations'],
            reachable_declarations=report['reachable_declarations'], error_count=report['error_count']))
    output['reachable_count_method'] = 'sum over independently checked compiler contexts'
    return output
