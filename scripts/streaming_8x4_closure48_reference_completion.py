"""Five exact unfinished FVM grids under a NEW 48h component authority."""
import argparse
import copy
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import time

sys.dont_write_bytecode=True
sys.path.insert(0,str(Path(__file__).resolve().parent))
import streaming_8x4_rc_reference_completion as BASE
import streaming_8x4_rc_reference_completion_readback as OLD_READER
import streaming_8x4_closure48_reference_context as C
P,E,W,H,F,M=BASE.P,BASE.E,BASE.W,BASE.H,BASE.F,BASE.M
ROOT,PYTHON=BASE.ROOT,BASE.PYTHON
INDICES=list(BASE.INDICES)
OUTPUT='rc-reference-completion-48-5-01'
CONTAINER='pinwheel-8x4-'+OUTPUT
NEW=('streaming_8x4_closure48_reference_completion.py','streaming_8x4_closure48_reference_context.py',
    'streaming_8x4_closure48_reference_readback.py')
snapshot,validate_snapshot,deltas,resource_feasible=BASE.snapshot,BASE.validate_snapshot,BASE.deltas,BASE.resource_feasible
jobs,validate_row=BASE.jobs,BASE.validate_row
reopen_parent=BASE.reopen_parent


def policy():
    row=copy.deepcopy(BASE.policy());row.update(schema=C.PREFIX+'policy.v1',campaign_id=C.CLOCK.CAMPAIGN,
        scope='exact original27 plus fresh indices27to31; distinct nominal TYP finite2D empirical reference component only; no G2/physical-corner/full-model/timing authority')
    return row


def sources():
    result=BASE.sources();directory=Path(__file__).parent
    names=[*NEW,'streaming_8x4_closure48_policy.py','streaming_8x4_closure48_resources.py']
    names += [Path(n).name for n in C.CLOCK.HISTORICAL]
    for name in names:result[name]=E.sha(directory/name)
    return dict(sorted(result.items()))


def expected_plan(inputs):
    old=BASE.verify(inputs/'historical-completion',C.OLD_PLAN)
    P.need(E.sha(inputs/'failed-expanded-authority.json')==BASE.FAILED,'Original failed expanded packet changed')
    row=copy.deepcopy(old);row.update(schema=C.PREFIX+'plan.v1',policy=policy(),
        original_completion_plan_sha256=C.OLD_PLAN,original_completion_was_unexecuted=True,
        source_derivation=C.derivation(BASE,OLD_READER),producer_sha256=sources(),files=W.input_files(inputs))
    return row


def prepare(baseline,output):
    baseline,output=Path(baseline).resolve(strict=True),Path(output).absolute()
    BASE.verify(baseline,C.OLD_PLAN);BASE.reopen_parent(baseline/'failed-expanded-authority.json')
    P.need(not output.exists() and output.parent.is_dir() and not output.is_symlink(), 'Fresh48 completion owner required')
    P.need(output.resolve().is_relative_to(ROOT/'build/campaigns'/C.CLOCK.CAMPAIGN),'New48 campaign preparation ownership required')
    output.mkdir();shutil.copytree(baseline,output/'historical-completion')
    shutil.copyfile(baseline/'failed-expanded-authority.json',output/'failed-expanded-authority.json')
    row=expected_plan(output);W.write(output/'plan.json',row);verify(output,E.sha(output/'plan.json'));return row


def verify(inputs,digest):
    inputs=Path(inputs)
    P.need((inputs/'plan.json').is_file() and not (inputs/'plan.json').is_symlink()
        and E.sha(inputs/'plan.json')==digest,'Completion48 plan hash differs')
    row=json.loads((inputs/'plan.json').read_text());P.need(row==expected_plan(inputs),
        'Completion48 exact old/fresh membership/source/kernel/equations differ')
    P.need(INDICES==[27,28,29,30,31] and row['selected_indices']==INDICES
        and row['selected_jobs']==[dict(index=i,**jobs(row)[i]) for i in INDICES], 'Completion48 five-call scope differs')
    return row


def proposal(inputs,digest,parent,require_fresh=True):
    inputs,parent=Path(inputs).resolve(),Path(parent).resolve();plan=verify(inputs,digest)
    P.need(parent.is_dir() and parent.is_relative_to(ROOT/'build/campaigns'/C.CLOCK.CAMPAIGN)
        and (not require_fresh or not(parent/OUTPUT).exists()), 'Fresh48 owned output required')
    old=BASE.proposal(inputs/'historical-completion',C.OLD_PLAN,parent,require_fresh=False);argv=list(old['argv'])
    pairs=[(BASE.CONTAINER,CONTAINER),
        ('type=bind,src='+str(inputs/'historical-completion')+',dst=/rc-inputs,readonly','type=bind,src='+str(inputs)+',dst=/rc-inputs,readonly'),
        ('/rc-source/'+BASE.NEW[0],'/rc-source/'+NEW[0]),(C.OLD_PLAN,digest),
        ('/rc-output-parent/'+BASE.OUTPUT,'/rc-output-parent/'+OUTPUT)]
    for before,after in pairs:
        P.need(argv.count(before)==1,'Exact48 five-token command adaptation differs');argv[argv.index(before)]=after
    return dict(schema=C.PREFIX+'command-proposal.v1',root_go_required=True,admitted=False,native_executed=False,
        qualified=False,model_qualified=False,qualified_timing=False,finite_BEM_passed=False,
        plan_path=str(inputs/'plan.json'),plan_sha256=digest,output_name=OUTPUT,container_name=CONTAINER,
        timeout_seconds=1110,policy=policy(),producer_sha256=plan['producer_sha256'],argv=argv)


# These exact old bodies execute with this module's NEW verify/policy/output
# bindings. The field kernel, its equations and validation helpers are aliases.
C.install(BASE,('dispatch_argv','one','dispatch','run'),globals())


def interrupted(signum,frame):raise InterruptedError('Signal '+str(signum))


def main():
    p=argparse.ArgumentParser(description=__doc__);sub=p.add_subparsers(dest='action',required=True)
    q=sub.add_parser('prepare');q.add_argument('--baseline',type=Path,required=True);q.add_argument('--output',type=Path,required=True)
    for action in ('verify','proposal','one','run'):
        q=sub.add_parser(action);q.add_argument('--inputs',type=Path,required=True);q.add_argument('--plan-sha256',required=True)
        if action!='verify':q.add_argument('--output',type=Path,required=True)
        if action=='one':q.add_argument('--index',type=int,required=True)
    a=p.parse_args()
    if a.action=='prepare':prepare(a.baseline,a.output);print(E.sha(a.output/'plan.json'));return 0
    if a.action=='verify':verify(a.inputs,a.plan_sha256);print('verified');return 0
    if a.action=='proposal':W.write(a.output,proposal(a.inputs,a.plan_sha256,a.output.parent/'rc-native-outputs'));return 0
    signal.signal(signal.SIGTERM,interrupted)
    result=one(a.inputs,a.plan_sha256,a.index,a.output) if a.action=='one' else run(a.inputs,a.plan_sha256,a.output)
    return 0 if result['numeric_passed' if a.action=='one' else 'passed'] else 2


if __name__=='__main__':raise SystemExit(main())
