"""Closed original27/fresh5 composite32 component; all model/corner claims false."""
import argparse
import json
import math
from pathlib import Path
import sys

sys.dont_write_bytecode=True
sys.path.insert(0,str(Path(__file__).resolve().parent))
import streaming_8x4_closure48_reference_completion as W
import streaming_8x4_closure48_reference_context as C
P,E=W.P,W.E

C.install(W.OLD_READER,('numeric_leaf','dispatch','analysis','work_state'),globals())


def resource_join(path,proposal_path,proposal,plan,report,root_go):
    inputs=Path(proposal['plan_path']).parent
    return C.resource_join(W,path,proposal_path,proposal,inputs,plan,report,root_go)


# Preserve the full original comparison/reopening body. Only its typed schema,
# the extra explicit RootGO argument and the resource-join call are adapted.
_source=C.body(W.OLD_READER,'readback').replace(C.OLD_PREFIX,C.PREFIX)
P.need(_source.count('def readback(inputs, digest, directory, resource_path, proposal_path):')==1
    and _source.count('resource_join(resource_path, proposal_path, proposal, plan, report)')==1,
    'Exact independent readback/RootGO seam differs')
_source=_source.replace('def readback(inputs, digest, directory, resource_path, proposal_path):',
    'def readback(inputs, digest, directory, resource_path, proposal_path, root_go):').replace(
    'resource_join(resource_path, proposal_path, proposal, plan, report)',
    'resource_join(resource_path, proposal_path, proposal, plan, report, root_go)')
exec(compile(_source,__file__,'exec'),globals())


def closed_authority(path):
    row=json.loads(Path(path).read_text())
    P.need(row['schema']==C.PREFIX+'independent-readback.v1','Foreign nominal reference authority')
    for item in (row['new_completion_plan'],row['execution_report'],row['command_proposal'],
        row['resource_cleanup_join']['resource_report'],row['original_failed_expanded_authority'],row['resource_cleanup_join']['root_go']):
        P.need(C.bound(item['path'])==item,'Completion48 dependency changed')
    plan=row['new_completion_plan'];actual=readback(Path(plan['path']).parent,plan['sha256'],
        Path(row['execution_report']['path']).parent,Path(row['resource_cleanup_join']['resource_report']['path']),
        Path(row['command_proposal']['path']),Path(row['resource_cleanup_join']['root_go']['path']))
    P.need(actual==row and row['composite32_reference_complete_passed'] is True,
        'Failed/incomplete48 composite cannot confer nominal reference component authority')
    return row


def main():
    p=argparse.ArgumentParser(description=__doc__)
    for name in ('inputs','directory','resource-report','command-proposal','root-go','output'):p.add_argument('--'+name,type=Path,required=True)
    p.add_argument('--plan-sha256',required=True);a=p.parse_args()
    row=readback(a.inputs,a.plan_sha256,a.directory,a.resource_report,a.command_proposal,a.root_go)
    W.W.write(a.output,row);print(json.dumps({k:row[k] for k in ('fresh5_measurement_packet_completed','composite32_reference_complete_passed','model_qualified')}))
    return 0 if row['composite32_reference_complete_passed'] else 2


if __name__=='__main__':raise SystemExit(main())
