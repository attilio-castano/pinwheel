#!/usr/bin/env python3
"""Freeze exact certified streaming TT netlist plus a local read-only PDK stage."""
import argparse
from pathlib import Path
from streaming_tt_physical import ARCHIVE, MANIFEST, prepare


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--design', required=True)
    parser.add_argument('--depth', choices=(2, 4), type=int, default=2)
    parser.add_argument('--manifest', type=Path, default=MANIFEST)
    parser.add_argument('--pdk-root', type=Path, default=ARCHIVE / 'pdk')
    parser.add_argument('--template', type=Path, default=ARCHIVE / 'upstream/tt_block_6x4_pgvdd.def')
    parser.add_argument('--optimized-admission',type=Path)
    parser.add_argument('--optimized-admission-sha256')
    args = parser.parse_args()
    if args.optimized_admission is not None:
        from streaming_tt_candidate import prepare_optimized
        if args.depth != 2 or not args.optimized_admission_sha256:
            parser.error('Optimized intake requires depth2 and an exact parent admission SHA256')
        if args.manifest != MANIFEST or args.template != ARCHIVE/'upstream/tt_block_6x4_pgvdd.def':
            parser.error('Optimized intake uses only the parent-admitted candidate and pinned official template')
        result = prepare_optimized(args.design,admission=args.optimized_admission,
            admission_sha256=args.optimized_admission_sha256,pdk=args.pdk_root)
    else:
        if args.optimized_admission_sha256: parser.error('Admission SHA256 requires --optimized-admission')
        result = prepare(args.design,depth=args.depth,manifest=args.manifest,pdk=args.pdk_root,template=args.template)
    print(result/'inputs.json')


if __name__ == '__main__': main()
