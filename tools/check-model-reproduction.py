#!/usr/bin/env python3
"""Check frozen model source identities and, optionally, every built artifact."""
import argparse
import hashlib
import json
from pathlib import Path

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--artifacts', action='store_true', help='require all canonical .olean hashes')
args = parser.parse_args()
root = Path(__file__).resolve().parents[1] / 'model'
manifest = json.loads((root / 'SOURCES.json').read_text())
rows = manifest['files']
errors = []
modules = {row['module'] for row in rows}
if len(rows) != 1481 or len(modules) != 1481 or manifest['modules'] != 1481:
    errors.append('manifest must contain exactly 1481 distinct model modules')
expected_sources = set()
expected_artifacts = set()
for row in rows:
    relative = Path(*row['module'].split('.')).with_suffix('.lean')
    if str(relative) != row['source'] or relative.is_absolute() or '..' in relative.parts:
        errors.append('invalid module/source mapping: ' + row['module'])
        continue
    expected_sources.add(relative.as_posix())
    source = root / relative
    if not source.is_file() or hashlib.sha256(source.read_bytes()).hexdigest() != row['source_sha256']:
        errors.append('source identity mismatch: ' + row['source'])
    if args.artifacts:
        relative_artifact = relative.with_suffix('.olean')
        expected_artifacts.add(relative_artifact.as_posix())
        artifact = root / '.lake/build/lib/lean' / relative_artifact
        if not artifact.is_file() or hashlib.sha256(artifact.read_bytes()).hexdigest() != row['canonical_olean_sha256']:
            errors.append('artifact identity mismatch or missing: ' + row['module'])
actual_sources = {str(p.relative_to(root)) for p in (root / 'ArmFull').rglob('*.lean')}
actual_sources.add('ArmFull.lean')
if actual_sources != expected_sources:
    errors.append('model source inventory differs from frozen manifest')
if args.artifacts:
    artifact_root = root / '.lake/build/lib/lean'
    actual_artifacts = {str(p.relative_to(artifact_root)) for p in artifact_root.rglob('*.olean')}
    if actual_artifacts != expected_artifacts:
        errors.append('built model module inventory differs from frozen manifest')
print(json.dumps(dict(status='FAIL' if errors else 'PASS', modules=len(rows),
                      artifacts_checked=args.artifacts, errors=errors), indent=2))
raise SystemExit(bool(errors))
