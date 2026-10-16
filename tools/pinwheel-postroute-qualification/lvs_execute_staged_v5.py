#!/usr/bin/env python3
"""Root-only execution of an already staged immutable native LVS control job."""
import argparse
import json
from pathlib import Path
from lvs_controls_host_v2 import spec
from dataclasses import replace


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--staged-root', type=Path, required=True)
    parser.add_argument('--native-seconds', type=int, default=600)
    args = parser.parse_args()
    out = args.staged_root.resolve()
    assert Path(__file__).resolve() == out / 'lvs_execute_staged_v5.py', 'Execute the copied immutable staged helper'
    module, job = spec(out, args.native_seconds)
    job = replace(job, command=['python3', '-B', '/work/diagnostic/lvs_controls_native_v5.py'])
    result = module.run_owned_job(job)
    print(json.dumps({'status': result['status'], 'receipt': str(out / 'report.json'),
                      'physical_acceptance_claim': False}))
    if result['status'] != 'passed':
        raise SystemExit(1)


if __name__ == '__main__':
    main()
