"""Root-only single full official replay with explicit6g/3600s context."""
import argparse
import json
from pathlib import Path
import streaming_8x4_closure24_official_budget as B


def main():
    q=argparse.ArgumentParser(description=__doc__);sub=q.add_subparsers(dest='mode',required=True)
    p=sub.add_parser('prepare')
    for name in ('previous-report','previous-resource','output'):p.add_argument('--'+name,type=Path,required=True)
    for name in ('verify','proposal','run'):
        p=sub.add_parser(name);p.add_argument('--plan',type=Path,required=True)
        if name=='proposal':p.add_argument('--output',type=Path,required=True)
    a=q.parse_args()
    if a.mode=='prepare':B.prepare(a.previous_report,a.previous_resource,a.output);print(B.sha(a.output/'plan.json'));return 0
    if a.mode=='verify':B.verify(a.plan);print('verified');return 0
    if a.mode=='proposal':
        B.need(not a.output.exists(),'Preserve earlier resource replay proposal');B.ORIGINAL.write(a.output,B.proposal(a.plan));return 0
    report=B.run(a.plan);print(json.dumps(dict(passed=report['passed'],executed=report['executed'])));return 0 if report['passed'] else 2

if __name__=='__main__':raise SystemExit(main())
