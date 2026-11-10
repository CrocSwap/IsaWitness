"""Disk-backed declaration graphs; cached axiom lists are comparison data only."""
from __future__ import annotations

from collections import defaultdict, deque
import json
from pathlib import Path
import sqlite3
import re

STANDARD_AXIOMS = frozenset(("propext", "Classical.choice", "Quot.sound"))


def compatible_equations(name, choices):
    """Mirror Lean's exact theorem identity test, retaining every proof body."""
    if not re.search(r'\.(?:eq_?[0-9]+|eq_def|eq_unfold)$',name):return False
    identity=choices[0].get('equation_identity')
    return isinstance(identity,str) and bool(identity) and all(
        c['kind']=='theorem' and not c['unsafe'] and not c['partial']
        and c.get('equation_identity')==identity for c in choices)


def conflicting_candidates(name,choices):
    if len(choices)<2:return False
    if re.search(r'\.(?:eq_?[0-9]+|eq_def|eq_unfold)$',name) and any(c.get('equation_identity') is not None for c in choices):
        return not compatible_equations(name,choices)
    signature=lambda c:(c['kind'],tuple(sorted(c['dependencies'])),c['unsafe'],c['partial'])
    return any(signature(c)!=signature(choices[0]) for c in choices[1:])


class ProofGraph:
    def __init__(self, database: Path):
        self.db = sqlite3.connect(database)
        self.db.executescript("""
            CREATE TABLE modules(name TEXT PRIMARY KEY, data TEXT NOT NULL);
            CREATE TABLE declarations(name TEXT, module TEXT, data TEXT NOT NULL,
                                      PRIMARY KEY(name, module));
            CREATE INDEX declarations_module ON declarations(module);
        """)

    def close(self):
        self.db.close()

    def load(self, path: Path):
        complete = None
        counts = defaultdict(int)
        with path.open() as stream, self.db:
            for line in stream:
                if complete is not None:
                    raise ValueError("graph has data after completion marker")
                record = json.loads(line)
                event = record.get("event")
                if event == "module":
                    self.db.execute("INSERT INTO modules VALUES (?,?)",
                                    (record["module"], json.dumps(record)))
                elif event == "declaration":
                    self.db.execute("INSERT INTO declarations VALUES (?,?,?)",
                                    (record["name"], record["module"], json.dumps(record)))
                    counts[record["module"]] += 1
                elif event == "complete":
                    complete = record
                else:
                    raise ValueError("unknown graph record")
        modules = self.modules()
        if complete is None or complete["modules"] != len(modules):
            raise ValueError("incomplete module graph")
        if set(counts) - modules.keys():
            raise ValueError("declaration has no owning module")
        for name, module in modules.items():
            if counts[name] != module["declaration_count"]:
                raise ValueError("incomplete declarations for " + name)
            if set(module["imports"]) - modules.keys():
                raise ValueError("incomplete imports for " + name)

    def modules(self):
        return {name: json.loads(data) for name, data in
                self.db.execute("SELECT name,data FROM modules ORDER BY name")}

    def candidates(self, name):
        choices = [json.loads(row[0]) for row in self.db.execute(
            "SELECT data FROM declarations WHERE name=? ORDER BY module", (name,))]
        if len(choices)>1 and compatible_equations(name,choices):
            owners=[r[0] for r in self.db.execute('SELECT module FROM declarations WHERE name=?',(name.rsplit('.',1)[0],))]
            if len(owners)==1:choices.sort(key=lambda c:c['module']!=owners[0])
        return choices
