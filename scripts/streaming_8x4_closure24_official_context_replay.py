"""Root-only corrected-view-authority official6g full attempt."""
import argparse
import json
from pathlib import Path
import streaming_8x4_closure24_official_context as C


def main():
    q=argparse.ArgumentParser(description=__doc__);sub=q.add_subparsers(dest='mode',required=True);p=sub.add_parser('prepare')
    for name in ('prior-plan','failed-resource','output'):p.add_argument('--'+name,type=Path,required=True)
    for name in ('verify','proposal','run'):
        p=sub.add_parser(name);p.add_argument('--plan',type=Path,required=True)
        if name=='proposal':p.add_argument('--output',type=Path,required=True)
    a=q.parse_args()
    if a.mode=='prepare':C.prepare(a.prior_plan,a.failed_resource,a.output);print(C.sha(a.output/'plan.json'));return 0
    if a.mode=='verify':C.verify(a.plan);print('verified');return 0
    if a.mode=='proposal':
        C.need(not a.output.exists(),'Preserve earlier corrected context proposal');C.OLD.ORIGINAL.write(a.output,C.proposal(a.plan));return 0
    row=C.run(a.plan);print(json.dumps(dict(passed=row['passed'],executed=row['executed'])));return 0 if row['passed'] else 2

if __name__=='__main__':raise SystemExit(main())
