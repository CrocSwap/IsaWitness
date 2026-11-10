"""Explicit, exact-name axiom exceptions; native-evaluation axioms stay forbidden."""
from __future__ import annotations

from dataclasses import dataclass, field
from datetime import date
import json
import hashlib
from pathlib import Path
import re

from .proof_graph import STANDARD_AXIOMS


def native_axiom(name):
    return '_native.' in name or name.rsplit('.', 1)[-1] in ('ofReduceBool', 'ofReduceNat', 'trustCompiler', 'sorryAx')


def local_path(value):
    if not isinstance(value, str) or not value or any(c in value for c in '\n\r\0'):
        raise ValueError('policy paths must be nonempty relative paths')
    p = Path(value)
    if p.is_absolute() or '..' in p.parts or p == Path('.'):
        raise ValueError('policy paths must stay inside the project')
    return p.as_posix()


@dataclass
class Policy:
    digest: str = ''
    exceptions: dict = field(default_factory=dict)
    boundary_locations: set = field(default_factory=set)
    tool_roots: list = field(default_factory=list)
    historical: list = field(default_factory=list)
    implementations: list = field(default_factory=list)
    negative_controls: list = field(default_factory=list)

    def allowed(self, name, *, tool=False, declaration=None):
        if native_axiom(name):
            return False
        if name in STANDARD_AXIOMS:
            return True
        entry = self.exceptions.get(name)
        return bool(entry and (entry['scope'] != 'tool' or tool) and
                    (not entry.get('declarations') or declaration in entry['declarations']))


def parse_policy(text):
    """Accept a fenced JSON policy, or an approval table with shared metadata."""
    policy = Policy(digest=hashlib.sha256(text.encode()).hexdigest())
    blocks = re.findall(r'```json\s*\n(.*?)```', text, re.S | re.I)
    if len(blocks) > 1:
        raise ValueError('AXIOMS.md must have at most one JSON policy block')
    if blocks:
        data = json.loads(blocks[0])
        if not isinstance(data, dict) or set(data) - {'exceptions', 'tool_roots', 'historical', 'implementations', 'negative_controls'}:
            raise ValueError('invalid AXIOMS.md JSON policy')
        entries = data.get('exceptions', [])
        for key in ('implementations', 'negative_controls'):
            rows = data.get(key, [])
            if not isinstance(rows, list):
                raise ValueError(key + ' must be a list')
            for row in rows:
                if not isinstance(row, dict) or any(not isinstance(row.get(k), str) or not row[k].strip()
                                                  for k in ('date', 'reason', 'removal_plan', 'approved_by')):
                    raise ValueError(key + ' needs date, reason, removal_plan and approved_by')
                date.fromisoformat(row['date'])
                entry = dict(row, location=local_path(row.get('location')))
                if key == 'implementations':
                    if not isinstance(row.get('name'), str) or not re.fullmatch(r"[\w.']+", row['name']):
                        raise ValueError('implementation exceptions need exact fully qualified names')
                    if not isinstance(row.get('tokens'), list) or not row['tokens'] or set(row['tokens']) - {'extern', 'implemented_by', 'unsafe'}:
                        raise ValueError('implementation exception tokens must be explicit implementation boundaries')
                else:
                    if row.get('token') != 'debug.skipKernelTC' or row.get('no_imports') is not True:
                        raise ValueError('negative controls only permit isolated debug.skipKernelTC fixtures with no_imports=true')
                getattr(policy, key).append(entry)
        if not isinstance(data.get('tool_roots', []), list) or not isinstance(data.get('historical', []), list):
            raise ValueError('tool_roots and historical must be lists')
        policy.tool_roots = [local_path(p) for p in data.get('tool_roots', [])]
        for entry in data.get('historical', []):
            if not isinstance(entry, dict) or entry.get('status') != 'historical; contains native axioms; not trusted':
                raise ValueError('historical entries need the explicit untrusted status')
            if not entry.get('reason') or entry.get('not_executable') is not True:
                raise ValueError('historical entries need a reason and not_executable=true')
            policy.historical.append(dict(entry, path=local_path(entry.get('path'))))
    else:
        entries = []
        shared_date = re.search(r'\b\d{4}-\d{2}-\d{2}\b', text)
        removal = re.search(r'Removal plan:\s*(.+)', text, re.I)
        approver = re.search(r'Approved by\s+(?:\*\*)?([^*,\n]+)', text, re.I)
        tool_scope = bool(re.search(r'tool[- ]boundary', text, re.I))
        table = []
        for line in text.splitlines():
            if not line.lstrip().startswith('|'):
                continue
            cells = [c.strip() for c in line.strip().strip('|').split('|')]
            if all(re.fullmatch(r'[:\- ]+', c) for c in cells):
                continue
            if not table:
                table.append([re.sub('[^a-z]', '', c.lower()) for c in cells])
                continue
            row = dict(zip(table[0], cells))
            name_field = row.get('name', row.get('nameimplementation', ''))
            names = re.findall(r'`([^`]+)`', name_field) or [name_field]
            locations = [local_path(p) for p in re.findall(r'`([^`]+)`', row.get('location', ''))]
            if names and all(n in ('unsafe', 'implemented_by', 'extern') for n in names):
                if not tool_scope or not (shared_date and removal and approver):
                    raise ValueError('implementation exceptions need explicit tool-boundary approval metadata')
                policy.boundary_locations.update(locations)
                continue
            name = names[0].split(':', 1)[0].strip() if names else ''
            if not name:
                raise ValueError('exception table entry has no name')
            entry = dict(name=name, date=row.get('date', row.get('approvaldate', shared_date.group() if shared_date else '')),
                         reason=row.get('reason', ''), removal_plan=row.get('removalplan', removal.group(1).strip() if removal else ''),
                         scope='tool' if tool_scope else 'axiom', locations=locations)
            if approver:
                entry['approved_by'] = approver.group(1).strip(' *')
            entries.append(entry)
    if not isinstance(entries, list):
        raise ValueError('exceptions must be a list')
    for original in entries:
        if not isinstance(original, dict):
            raise ValueError('exception entries must be objects')
        entry = dict(original)
        for key in ('name', 'date', 'reason', 'removal_plan', 'approved_by'):
            if not isinstance(entry.get(key), str) or not entry[key].strip():
                raise ValueError('exception needs name, date, reason, removal_plan and approved_by')
        name = entry['name']
        if not re.fullmatch(r'[\w\u00ab\u00bb.\-\']+', name) or '*' in name or name in policy.exceptions:
            raise ValueError('exception names must be unique exact declaration names')
        if name in STANDARD_AXIOMS:
            raise ValueError('standard axioms are built in, not source exception declarations: ' + name)
        if native_axiom(name):
            raise ValueError('native-evaluation and sorry axioms cannot be excepted: ' + name)
        date.fromisoformat(entry['date'])
        entry['scope'] = entry.get('scope', 'axiom')
        if entry['scope'] not in ('axiom', 'tool'):
            raise ValueError('exception scope must be axiom or tool')
        locations = entry.get('locations', [entry['location']] if 'location' in entry else [])
        if not isinstance(locations, list):
            raise ValueError('exception locations must be a list')
        entry['locations'] = [local_path(p) for p in locations]
        if 'declarations' in entry:
            names = entry['declarations']
            if not isinstance(names, list) or not names or any(not isinstance(n,str) or
                    not re.fullmatch(r"[\w\u00ab\u00bb.\-']+",n) for n in names):
                raise ValueError('declarations must be a nonempty list of exact names')
        if entry['scope'] == 'tool' and not entry['locations']:
            raise ValueError('tool-boundary exceptions need source locations')
        if entry['scope'] == 'tool':
            policy.boundary_locations.update(entry['locations'])
        policy.exceptions[name] = entry
    return policy
