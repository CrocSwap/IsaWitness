#!/usr/bin/env python3
"""Expose generated syntax helpers using metadata scopes, with no new lines.

Run on the owned generated tree after module conversion, never upstream Sail.
All replacements are declaration metadata or existing blank lines. Runtime
declaration expressions and macro pattern/result expressions remain unchanged.
"""
import argparse
import hashlib
import json
from pathlib import Path


TARGETS = ("Sail/Attr.lean", "Sail/IntRange.lean", "Sail/Common.lean",
           "Sail/Sail.lean", "ArmFull/ArmExtrasFork.lean")


def replace_once(source, old, new):
    if new in source and old not in source:
        return source
    if source.count(old) != 1:
        raise ValueError("unexpected syntax-source layout: " + repr(old))
    return source.replace(old, new, 1)


def transform(source, rel):
    if not source.startswith("module ") and not source.startswith("module\n"):
        raise ValueError("expected modern module source: " + rel)
    result = source
    if rel == "Sail/Attr.lean":
        result = replace_once(result, "public import Lean", "public meta import Lean")
        result = replace_once(result, "@[expose] public section", "@[expose] public meta section")
    elif rel == "Sail/IntRange.lean":
        result = replace_once(result, "\n\nsyntax:max", "\nmeta section\nsyntax:max")
        result = replace_once(result, "\n\nend IntRange", "\nend\nend IntRange")
    elif rel == "Sail/Common.lean":
        result = replace_once(result, "\n\n/-\nThis notation", "\nmeta section\n/-\nThis notation")
        result = replace_once(result, "\n\ndef String.takeStr", "\nend\ndef String.takeStr")
    elif rel == "Sail/Sail.lean":
        result = replace_once(result, '\n\ninfixl:65 " +i "', '\nmeta section\ninfixl:65 " +i "')
        result = replace_once(result, 'notation:50 x ">b" y => decide (x > y)\n\n',
                              'notation:50 x ">b" y => decide (x > y)\nend\n')
        result = replace_once(result, "set_option grind.warning false\nmacro_rules",
                              "set_option grind.warning false meta section\nmacro_rules")
        result = replace_once(result, "\n\n-- This lemma replaces", "\nend\n-- This lemma replaces")
    elif rel == "ArmFull/ArmExtrasFork.lean":
        result = replace_once(result, "\n\nmacro_rules", "\nmeta section\nmacro_rules")
    else:
        raise ValueError("unsupported source: " + rel)
    if result.count("\n") != source.count("\n"):
        raise ValueError("metadata stage changed line count")
    return result


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("root", type=Path)
    ap.add_argument("--manifest", type=Path, required=True)
    a = ap.parse_args()
    root = a.root.resolve(strict=True)
    pending = []
    for rel in TARGETS:
        path = root / rel
        path.resolve(strict=True).relative_to(root)
        before = path.read_bytes()
        after = transform(before.decode(), rel).encode()
        if transform(after.decode(), rel).encode() != after:
            raise ValueError("non-idempotent metadata stage: " + rel)
        pending.append((path, after, {"path": rel,
                       "before_sha256": hashlib.sha256(before).hexdigest(),
                       "after_sha256": hashlib.sha256(after).hexdigest(),
                       "changed": before != after, "line_count_unchanged": True}))
    for path, data, row in pending:
        if row["changed"]:
            path.write_bytes(data)
    report = {"schema": "syntax-visibility-postpass-v1",
              "tool_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              "files": [p[2] for p in pending],
              "semantic_acceptance": "requires independent exact export/body/private/scope comparison"}
    a.manifest.parent.mkdir(parents=True, exist_ok=True)
    a.manifest.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"files": len(pending), "changed": sum(p[2]["changed"] for p in pending)}))


if __name__ == "__main__":
    main()
