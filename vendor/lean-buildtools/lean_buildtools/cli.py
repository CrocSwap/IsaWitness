from __future__ import annotations
import argparse
import json
from pathlib import Path
import subprocess
import time

from .gate import gate
from .gate_source import source_report


def main(argv=None):
    parser = argparse.ArgumentParser(prog='lake run lean-buildtools/<tool>')
    sub = parser.add_subparsers(dest='command', required=True)
    for name in ('gate', 'source-scan', 'profile', 'report'):
        p = sub.add_parser(name)
        p.add_argument('--project', type=Path, default=Path.cwd())
        p.add_argument('--output', type=Path)
        if name=='gate':
            p.add_argument('--config', default='gate.json')
            p.add_argument('--incremental', action='store_true', help='diagnostic: do not clean own package; no fresh-build claim')
        if name in ('profile', 'report'):
            p.add_argument('target', type=Path)
            p.add_argument('--sort', choices=['time_s', 'heartbeats_raw', 'rss_delta_bytes', 'peak_rss_bytes'], default='time_s')
        if name=='profile':
            p.add_argument('--memory', type=int, default=12288)
    args = parser.parse_args(argv)
    project = args.project.resolve()
    output = args.output.resolve() if args.output else project/'.lake'/'diagnostics'/f'{args.command}-{time.time_ns()}'
    try:
        if args.command=='gate':
            if output.is_relative_to(project/'.lake/build'):
                raise ValueError('gate output must be outside the cleaned .lake/build directory')
            return gate(project, output, config_path=args.config, fresh=not args.incremental)
        if args.command=='source-scan':
            result = source_report(project)
            if args.output:
                output.mkdir(parents=True, exist_ok=False)
                (output/'source.json').write_text(json.dumps(result,indent=2)+'\n')
            if args.output:
                print(f"source scan {result['status']}: {result['source_files']} files, {result['error_count']} errors; {output/'source.json'}")
            else:
                print(json.dumps(result,indent=2))
            return 1 if result['error_count'] else 0
        if args.command=='profile':
            from .profiling import profile
            return profile(project, args.target, output, args.memory, args.sort)
        from .profile import report
        report(args.target.resolve(), project, sort=args.sort)
        return 0
    except (OSError, ValueError, subprocess.CalledProcessError) as error:
        parser.exit(1, str(error)+'\n')
