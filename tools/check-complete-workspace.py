#!/usr/bin/env python3
"""Run all four fresh owned-package gates; launch with run-cold-build.sh on GB10."""
import argparse
import json
import os
from pathlib import Path
import subprocess
import time

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output', type=Path)
args = parser.parse_args()
root = Path(__file__).resolve().parents[1]
output = (args.output or root / '.lake/validation' / str(time.time_ns())).resolve()
if output.is_relative_to(root) and not output.is_relative_to(root / '.lake'):
    parser.error('output inside the checkout must be under .lake to keep generated collectors outside source scope')
output.mkdir(parents=True, exist_ok=False)
env = dict(os.environ, LAKE_ARTIFACT_CACHE='false', LAKE_RESTORE_ARTIFACTS='false')
packages = [('lean-sail', 'vendor/lean-sail'), ('ArmFull', 'model'),
            ('ArmCertObservers', 'observers'), ('ArmCert', '.')]
started = time.monotonic()
fetch_opened = started
with (output / 'fetch-lean-sail.log').open('w') as log:
    fetch_code = subprocess.run(['sh', 'scripts/fetch-lean-sail'], cwd=root, env=env,
                                stdout=log, stderr=subprocess.STDOUT).returncode
fetch_seconds = time.monotonic() - fetch_opened
if fetch_code:
    summary = dict(status='FAIL', fetch_exit_code=fetch_code, fetch_seconds=fetch_seconds,
                   packages=[], model_artifact_check_exit=None,
                   wall_seconds=time.monotonic()-started,
                   scope='Runtime fetch failed; no Lake update/build/gate was attempted.')
    (output / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps(summary), flush=True)
    raise SystemExit(fetch_code)
print(json.dumps(dict(fetch_exit_code=0, fetch_seconds=fetch_seconds)), flush=True)
results = []
for name, relative in packages:
    opened = time.monotonic()
    with (output / (name + '.log')).open('w') as log:
        code = subprocess.run(['lake', 'update'], cwd=root / relative, env=env,
                              stdout=log, stderr=subprocess.STDOUT).returncode
        if code == 0:
            code = subprocess.run(['lake', 'run', 'gate', '--output', str(output / (name + '-gate'))],
                                  cwd=root / relative, env=env, stdout=log,
                                  stderr=subprocess.STDOUT).returncode
    row = dict(package=name, exit_code=code, wall_seconds=time.monotonic() - opened)
    results.append(row)
    print(json.dumps(row), flush=True)
    (output / 'progress.json').write_text(json.dumps(results, indent=2) + '\n')
    if code:
        break
model_check = None
if len(results) == len(packages) and all(r['exit_code'] == 0 for r in results):
    with (output / 'model-reproduction.json').open('w') as log:
        model_check = subprocess.run(['python3', 'tools/check-model-reproduction.py', '--artifacts'],
                                     cwd=root, stdout=log, stderr=subprocess.STDOUT).returncode
elapsed = time.monotonic() - started
passed = (len(results) == len(packages) and all(r['exit_code'] == 0 for r in results)
          and model_check == 0 and elapsed <= 600)
summary = dict(status='PASS' if passed else 'FAIL', fetch_exit_code=fetch_code, fetch_seconds=fetch_seconds, packages=results,
               wall_seconds=elapsed, within_600_seconds=elapsed <= 600,
               model_artifact_check_exit=model_check,
               scope='Fresh owned-package builds/gates and all canonical model hashes. For a cold measurement use a fresh source checkout without build products.')
(output / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
print(json.dumps(summary, indent=2))
raise SystemExit(not passed)
