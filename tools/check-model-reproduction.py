#!/usr/bin/env python3
"""Verify the canonical model and, on request, the built module inventory."""
import argparse
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "model/CANONICAL-SOURCES.sha256"
REVISION = ROOT / "model/REVISION.json"
SOURCE_GROUPS = (
    ("model", "ArmFull", 1560),
    ("vendor/lean-sail", "Sail", 11),
)


def sha256(path):
    with path.open("rb") as source:
        return hashlib.file_digest(source, "sha256").hexdigest()


def inventory(root, module, suffix):
    sources = set((root / module).rglob("*" + suffix))
    root_file = (root / module).with_suffix(suffix)
    if root_file.is_file():
        sources.add(root_file)
    return sources


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--built", action="store_true", help="also require all canonical modules to have built .olean files")
    args = parser.parse_args()
    rev = json.loads(REVISION.read_text())
    errors = []
    rows = {}
    for line in MANIFEST.read_text().splitlines():
        match = re.fullmatch(r"([0-9a-f]{64})  ((?:model/ArmFull|vendor/lean-sail/Sail)(?:/[A-Za-z0-9_]+)*\.lean)", line)
        if not match or match[2] in rows:
            errors.append(f"invalid or duplicate manifest record {line!r}")
            continue
        rows[match[2]] = match[1]
    if rev["source_manifest_sha256"] != sha256(MANIFEST):
        errors.append("source manifest checksum disagrees with REVISION.json")

    for name, digest in rows.items():
        source = ROOT / name
        if not source.is_file() or source.is_symlink() or sha256(source) != digest:
            errors.append(f"source identity mismatch or missing source {name}")

    for package, module, count in SOURCE_GROUPS:
        src_dir = ROOT / package
        source_rows = {name for name in rows if name.startswith(f"{package}/{module}")}
        source_files = {str(p.relative_to(ROOT)) for p in inventory(src_dir, module, ".lean")}
        if source_rows != source_files or len(source_rows) != count or rev["modules"][module] != count:
            errors.append(f"{module} source inventory differs from the {count}-module manifest")
        if args.built:
            lib = src_dir / ".lake/build/lib/lean"
            expected = {str(Path(name).relative_to(package).with_suffix(".olean")) for name in source_rows}
            artifacts = {str(p.relative_to(lib)) for p in inventory(lib, module, ".olean")}
            if artifacts != expected:
                errors.append(f"{module} built module inventory differs from the canonical source inventory")

    print(json.dumps(dict(status="FAIL" if errors else "PASS", revision=rev["proof_commit"],
                          sources=len(rows), built_modules_checked=args.built, errors=errors), indent=2))
    raise SystemExit(bool(errors))


if __name__ == "__main__":
    main()
