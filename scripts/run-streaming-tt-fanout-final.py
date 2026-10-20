#!/usr/bin/env python3
"""Prepare and re-execute one sealed native fanout-partition/reroute campaign."""
import argparse
import os
from pathlib import Path
import sys


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    for name in ('admission','export-host','proposal','plan','corners'):parser.add_argument('--'+name,type=Path)
    parser.add_argument('--admission-sha256');parser.add_argument('--tag')
    parser.add_argument('--timeout-seconds',type=int,default=7200);parser.add_argument('--frozen-input',type=Path)
    parser.add_argument('--prepare-only',action='store_true')
    args=parser.parse_args();import streaming_tt_physical as P
    if args.prepare_only and args.frozen_input is not None:parser.error('--prepare-only cannot execute a frozen worker')
    if args.frozen_input is not None:
        metadata=P.read(P.regular(args.frozen_input));P.ROOT=Path(metadata['workspace_root']).resolve();P.BASE=P.ROOT/'build/physical'
        P.require(Path(__file__).resolve()==(args.frozen_input.parent/'inputs/producer/scripts/run-streaming-tt-fanout-final.py').resolve(),
            'Fanout worker must execute its frozen staged source')
    import streaming_tt_fanout_final as worker
    if args.frozen_input is None:
        if any(getattr(args,name) is None for name in ('admission','export_host','proposal','plan','corners','admission_sha256','tag')):
            parser.error('All explicit admission/transformation inputs and fresh tag are required')
        path=worker.prepare(args.admission,args.admission_sha256,args.tag,args.timeout_seconds,args.export_host,args.proposal,args.plan,args.corners)
        if args.prepare_only:print(path,flush=True);return 0
        staged=P.regular(path.parent/'inputs/producer/scripts/run-streaming-tt-fanout-final.py')
        os.execv(sys.executable,[sys.executable,'-B',str(staged),'--frozen-input',str(path)])
    return worker.run(args.frozen_input)


if __name__=='__main__':raise SystemExit(main())
