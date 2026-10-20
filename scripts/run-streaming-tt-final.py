#!/usr/bin/env python3
"""Run an explicitly admitted immutable postGRT detailed-route continuation."""
import argparse
import os
from pathlib import Path
import sys


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--admission',type=Path)
    parser.add_argument('--admission-sha256')
    parser.add_argument('--tag')
    parser.add_argument('--timeout-seconds',type=int,default=7200)
    parser.add_argument('--frozen-input',type=Path)
    args = parser.parse_args()
    import streaming_tt_physical as physical
    if args.frozen_input is not None:
        metadata = physical.read(physical.regular(args.frozen_input))
        physical.ROOT = Path(metadata['workspace_root']).resolve(); physical.BASE = physical.ROOT/'build/physical'
        physical.require(Path(__file__).resolve() == (args.frozen_input.parent/'inputs/producer/scripts/run-streaming-tt-final.py').resolve(),
            'Final worker must execute its frozen staged source')
    import streaming_tt_final as final
    if args.frozen_input is None:
        if args.admission is None or not args.admission_sha256 or not args.tag:
            parser.error('--admission, --admission-sha256 and --tag are required')
        path = final.prepare(args.admission,args.admission_sha256,args.tag,args.timeout_seconds)
        worker = physical.regular(path.parent/'inputs/producer/scripts/run-streaming-tt-final.py')
        os.execv(sys.executable,[sys.executable,'-B',str(worker),'--frozen-input',str(path)])
    return final.run(args.frozen_input)


if __name__ == '__main__': raise SystemExit(main())
