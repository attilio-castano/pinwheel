#!/usr/bin/env python3
"""Export a JSON protocol request through the existing production Lean frontends."""
import argparse
from pathlib import Path
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('request', nargs='?', default='-',
                        help='JSON request file, or - for standard input')
    args = parser.parse_args()
    request = sys.stdin.buffer.read() if args.request == '-' else Path(args.request).read_bytes()
    return subprocess.run(['lake', 'env', 'lean', '--run', 'scripts/ProgramExport.lean'],
                          input=request, cwd=ROOT).returncode


if __name__ == '__main__':
    raise SystemExit(main())
