"""HOST raw SPEF plus actual DEF-local NDR readback for all six calls."""
import argparse
import json
from pathlib import Path
import re
import sys

sys.path.insert(0,str(Path(__file__).resolve().parent))
import streaming_8x4_rc_consumer_ndr as N
import streaming_8x4_rc_consumer_readback as R


def definitions(text):
    units=re.findall(r'^\s*UNITS\s+DISTANCE\s+MICRONS\s+(\d+)\s*;',text,re.M)
    N.need(units==['1000'],'Native DEF did not retain actual1000DBU')
    blocks=re.findall(r'^\s*NONDEFAULTRULES\s+(\d+)\s*;\s*(.*?)^\s*END\s+NONDEFAULTRULES\s*$',text,re.M|re.S)
    N.need(len(blocks)==1 and blocks[0][0]=='2','Native DEF must contain exactly two block-local NDRs')
    body=blocks[0][1];matches=list(re.finditer(r'^\s*-\s+(\S+)\s+(.*?)\s*;',body,re.M|re.S));result={}
    N.need(len(matches)==2 and not re.sub(r'^\s*-\s+(\S+)\s+(.*?)\s*;','',body,flags=re.M|re.S).strip(),
        'Extra/missing native NDR rule syntax')
    for match in matches:
        name,rule=match.groups();N.need(name not in result,'Duplicate native NDR')
        tokens=rule.split();rows={};index=0
        while index<len(tokens):
            N.need(tokens[index:index+2]==['+','LAYER'] and index+5<=len(tokens),'Unsupported native NDR attributes')
            layer=tokens[index+2];N.need(tokens[index+3]=='WIDTH' and tokens[index+4].isdigit() and
                layer not in rows,'Missing/duplicate native NDR layer/width')
            width=int(tokens[index+4]);spacing=0;index+=5
            if index<len(tokens) and tokens[index]=='SPACING':
                N.need(index+1<len(tokens) and tokens[index+1].isdigit(),'Unsupported NDR spacing')
                spacing=int(tokens[index+1]);index+=2
            N.need(width>0,'Nonpositive native NDR width');rows[layer]=dict(width_dbu=width,spacing_dbu=spacing)
        N.need(set(rows)==set(N.METALS),'Native NDR lacks the complete actual routing-layer set')
        result[name]=rows
    return result


def net_bindings(text,fixture_rows):
    blocks=re.findall(r'^\s*NETS\s+(\d+)\s*;\s*(.*?)^\s*END\s+NETS\s*$',text,re.M|re.S)
    N.need(len(blocks)==1 and blocks[0][0]=='17' and len(fixture_rows)==17,'Native17-net membership differs')
    entries=list(re.finditer(r'^\s*-\s+(\S+)\s+(.*?)\s*;',blocks[0][1],re.M|re.S));actual={}
    for match in entries:
        name,body=match.groups();N.need(name not in actual,'Duplicate native consumer net')
        refs=re.findall(r'\+\s+NONDEFAULTRULE\s+(\S+)',body)
        N.need(len(refs)<=1,'Duplicate native NDR net binding');actual[name]=refs[0] if refs else None
    expected={row['name']:('WIDE_'+row['segments'][0][0] if '_wide_' in row['name'] else None) for row in fixture_rows}
    N.need(len(actual)==17 and actual==expected,'Native NDR-to-all17-net assignment differs');return actual


def native_ndr(text,witness,rows):
    actual=definitions(text);N.need(actual==witness['rules'],'Actual native NDR widths/spacings differ from exact LEF intent')
    bindings=net_bindings(text,rows)
    return dict(DBU_per_um=1000,block_local_rules=actual,net_bindings=bindings,all17_net_assignments_checked=True,
        active_widths_um={'WIDE_Metal1':'0.32','WIDE_Metal2':'0.40'},active_spacing_um='0.21',qualified=False)


def readback(inputs,plan_hash,directory):
    plan=N.verify(inputs,plan_hash);path=directory/'report.json';report=json.loads(path.read_text())
    N.need(report.get('schema')=='pinwheel.streaming-8x4-rc-consumer-DEF-NDR-execution.v1' and
        report.get('plan_sha256')==plan_hash and report.get('qualified') is False and report.get('model_qualified') is False and
        report.get('all_six_native_calls_closed') is True and report.get('consumer_policy_unchanged') is True and
        report.get('native_NDR_readback_required') is True and report.get('inputs_unchanged') is True and
        report.get('inner_report_sha256')==N.C.P.sha(directory/'native/report.json'),
        'Complete typed six-call NDR execution required')
    raw=R.readback(inputs/'consumer-inputs',plan['consumer_plan_sha256'],directory/'native')
    witness=json.loads((inputs/'NDR-witness.json').read_text());observations=[]
    for corner in ('MIN','TYP','MAX'):
        for policy in N.C.POLICIES:
            owner=directory/'native'/(corner+'-'+policy)
            before=R.regular(owner/'before.def');after=R.regular(owner/'after.def')
            N.need(before.read_bytes()==after.read_bytes(),'Native extraction changed DEF geometry/rules')
            observation=native_ndr(before.read_text(),witness,plan['fixture_rows'])
            observations.append(dict(corner=corner,policy=policy,before_DEF_sha256=N.C.P.sha(before),
                after_DEF_sha256=N.C.P.sha(after),**observation))
    N.need(raw['workflow_passed']==report['passed'] and N.verify(inputs,plan_hash)==plan,'NDR raw result/input closeout differs')
    return dict(schema='pinwheel.streaming-8x4-rc-consumer-DEF-NDR-independent-readback.v1',qualified=False,
        model_qualified=False,plan_sha256=plan_hash,execution_report_sha256=N.C.P.sha(path),
        workflow_passed=raw['workflow_passed'],all_six_native_calls_closed=True,
        all_six_actual_DEF_NDR_widths_and_net_bindings_checked=True,consumer_policy_unchanged=True,
        raw_consumer_readback=raw,native_NDR_observations=observations,
        resource_cleanup_join='Separate exact Root resource-supervisor receipt remains mandatory.')


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    for name in ('inputs','directory','output'):parser.add_argument('--'+name,type=Path,required=True)
    parser.add_argument('--plan-sha256',required=True);args=parser.parse_args()
    result=readback(args.inputs,args.plan_sha256,args.directory);N.write(args.output,result)
    print(json.dumps(dict(workflow_passed=result['workflow_passed'],model_qualified=False)))


if __name__=='__main__':main()
