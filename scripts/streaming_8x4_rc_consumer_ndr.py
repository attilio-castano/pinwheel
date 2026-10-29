"""Separate DEF-local NDR adapter over the immutable exact-unit consumer.

The frozen LEF import and six-call numerical body remain unchanged. Only two
block-local NDR declarations are added to the corrected1000DBU DEF; all route
coordinates, net references, rules, policies and tolerances stay identical.
No Native invocation is authorized by preparation or verification.
"""
import argparse
import copy
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import re
import shutil
import sys

sys.path.insert(0,str(Path(__file__).resolve().parent))
import streaming_8x4_rc_consumer_units as U

C=U.C
BASELINE_SHA='ae63e1068aa9cb1e0430d18487c727be3154a7e8773a6ffa45813718cd0dd8b6'
SOURCE_SHA='2731ee9198d7ce32a9033fd3dc35a765bc3244f7fc076962d1788d4ebf2779b6'
COMMIT='dcf36133a369abc8f3c5e5738cd4d82e4903c0e0'
METALS=('Metal1','Metal2','Metal3','Metal4','TopMetal1')
NEW_SOURCES=('streaming_8x4_rc_consumer_ndr.py','streaming_8x4_rc_consumer_ndr_readback.py')
SCHEMA='pinwheel.streaming-8x4-rc-consumer-DEF-NDR-plan.v1'


def need(value,message):C.need(value,message)


def write(path,value):
    need(not path.exists(),'Preserve existing NDR artifact');U.write(path,value)


def source_evidence(root):
    need(C.P.sha(root/'manifest.json')==SOURCE_SHA,'Exact NDR source intake changed')
    manifest=json.loads((root/'manifest.json').read_text())
    need(manifest.get('schema')=='pinwheel.streaming-8x4-rc-NDR-source-intake.v1' and
        manifest.get('openroad_commit')==COMMIT and manifest.get('native_executed') is False and
        len(manifest['files'])==5,'NDR source identity differs')
    expected={'manifest.json':SOURCE_SHA}
    for row in manifest['files']:
        name=row['name'];need(Path(name).name==name and name not in expected,'Duplicate/escaping NDR source')
        path=root/name;need(path.is_file() and not path.is_symlink(),'Missing/aliased NDR source')
        data=path.read_bytes();blob=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
        need(len(data)==row['bytes'] and C.P.sha(path)==row['sha256'] and blob==row['git_blob'],'NDR source bytes differ')
        expected[name]=row['sha256']
    need(file_inventory(root)==expected,'NDR source membership differs');return expected


def file_inventory(root):
    result={}
    for path in sorted(root.rglob('*')):
        need(not path.is_symlink(),'Aliased NDR preparation member')
        if path.is_file():result[str(path.relative_to(root))]=C.P.sha(path)
    return result


def default_widths(tech):
    need(U.lef_dbu(tech)==1000,'NDR adapter requires actual1000DBU technology')
    result={}
    for match in re.finditer(r'^LAYER\s+(\S+)\s*\n(.*?)^END\s+\1\s*$',tech,re.M|re.S):
        name,body=match.groups()
        if not re.search(r'^\s*TYPE\s+ROUTING\s*;',body,re.M):continue
        widths=re.findall(r'^\s*WIDTH\s+([0-9.]+)\s*;\s*$',body,re.M)
        need(name not in result and len(widths)==1,'Missing/duplicate actual routing-layer width')
        number=Fraction(widths[0])*1000;need(number.denominator==1 and number>0,'Nonintegral technology width')
        result[name]=int(number)
    need(tuple(result)==METALS,'Actual five-metal routing membership/order differs');return result


def declarations(tech,widths):
    defaults=default_widths(tech)
    matches=list(re.finditer(r'^NONDEFAULTRULE\s+(\S+)\s*\n(.*?)^END\s+\1\s*$',widths,re.M|re.S))
    need(len(matches)==2,'Expected exactly two intended LEF NDRs')
    rules={};expected_active={'WIDE_Metal1':('Metal1',320,210),'WIDE_Metal2':('Metal2',400,210)}
    for match in matches:
        name,body=match.groups();tokens=body.split()
        need(name in expected_active and name not in rules,'Unknown/duplicate intended NDR')
        layer,width,spacing=expected_active[name]
        need(len(tokens)==10 and tokens[:2]==['LAYER',layer] and tokens[2]=='WIDTH' and tokens[4]==';' and
            tokens[5]=='SPACING' and tokens[7]==';' and tokens[8:]==['END',layer] and
            Fraction(tokens[3])*1000==width and Fraction(tokens[6])*1000==spacing,'Intended NDR semantics changed')
        rules[name]={metal:dict(width_dbu=(width if metal==layer else defaults[metal]),
            spacing_dbu=(spacing if metal==layer else 0)) for metal in METALS}
    lines=['NONDEFAULTRULES 2 ;']
    for name,rows in rules.items():
        lines.append('- '+name)
        for metal,row in rows.items():
            text='  + LAYER '+metal+' WIDTH '+str(row['width_dbu'])
            if row['spacing_dbu']:text+=' SPACING '+str(row['spacing_dbu'])
            lines.append(text)
        lines.append(' ;')
    lines.append('END NONDEFAULTRULES')
    return '\n'.join(lines)+'\n',rules


def add_ndr(original,tech,widths):
    need(U.HEADER.findall(original)==[('UNITS DISTANCE MICRONS ','1000',' ;')] and
        len(re.findall(r'^COMPONENTS 0 ;$',original,re.M))==1 and
        not re.search(r'^NONDEFAULTRULES\b',original,re.M),'Unsupported DEF units/section or existing NDR declaration')
    block,rules=declarations(tech,widths);marker='COMPONENTS 0 ;\n'
    need(original.count(marker)==1,'Ambiguous DEF insertion point')
    fixed=original.replace(marker,block+marker,1)
    need(fixed.replace(block,'',1)==original and U.PAIR.findall(fixed)==U.PAIR.findall(original),
        'NDR declaration changed route/port/die coordinates or other bytes')
    need(re.findall(r'^NETS\s+(\d+)\s*;',original,re.M)==['17'],'Original17-net fixture changed')
    return fixed,dict(schema='pinwheel.streaming-8x4-rc-consumer-DEF-NDR-witness.v1',
        DBU_per_um=1000,block_declarations=2,rules=rules,coordinate_pairs_unchanged=len(U.PAIR.findall(original)),
        all_non_declaration_bytes_unchanged=True,all17_net_and_route_bytes_unchanged=True,
        selected_widths_and_spacings_equal_original_LEF_intent=True,
        unused_layer_widths_from_actual_technology=True,unused_layer_spacing_overrides=False,
        complete_native_DEF_NDR_readback_required=True,qualified=False)


def producer_map(old):
    result=dict(old['producer_sha256'])
    for name in NEW_SOURCES:result[name]=C.P.sha(Path(__file__).with_name(name))
    return result


def inner_plan(old,fixture,producers):
    result=copy.deepcopy(old);result['files_sha256']['fixture.def']=C.digest(fixture.encode())
    result['producer_sha256']=producers
    result['ndr_correction_scope']='Two complete block-local DEF NDR declarations only; geometry/net references/protocol/rules unchanged'
    return result


def prepare(baseline,source,failed,output):
    old=U.verify(baseline,BASELINE_SHA);need(not output.exists() and output.parent.is_dir(),'Fresh NDR owner required')
    evidence=source_evidence(source);consumer=baseline/'consumer-inputs';original=C.verify_plan(consumer,old['consumer_plan_sha256'])
    fixed,witness=add_ndr((consumer/'fixture.def').read_text(),(consumer/'tech.lef').read_text(),(consumer/'widths.lef').read_text())
    failure=json.loads((failed/'report.json').read_text());raw=(failed/'native/MIN-retained_rules/native.log').read_text()
    need(failure.get('schema')=='pinwheel.streaming-8x4-rc-consumer-units-execution.v1' and
        failure.get('plan_sha256')==BASELINE_SHA and failure.get('passed') is False and
        failure.get('all_six_native_calls_closed') is False and failure.get('inputs_unchanged') is True and
        all('undefined NONDEFAULTRULE ('+name+') referenced' in raw for name in witness['rules']) and
        'DEF parser returns an error!' in raw,'Original measured NDR failure differs')
    producers=producer_map(original);adapted=inner_plan(original,fixed,producers)
    output.mkdir();shutil.copytree(baseline,output/'baseline-unit-preparation');shutil.copytree(source,output/'source-evidence')
    inputs=output/'consumer-inputs';inputs.mkdir()
    for name in original['files_sha256']:shutil.copyfile(consumer/name,inputs/name)
    (inputs/'fixture.def').write_text(fixed);write(inputs/'plan.json',adapted);write(output/'NDR-witness.json',witness)
    failure_root=output/'failed-unit';failure_root.mkdir()
    for path,name in [(failed/'report.json','report.json'),(failed/'native/report.json','inner-report.json'),
        (failed/'native/MIN-retained_rules/native.log','native.log')]:shutil.copyfile(path,failure_root/name)
    plan=dict(schema=SCHEMA,qualified=False,model_qualified=False,native_executed=False,root_go_required=True,
        baseline_unit_plan_sha256=BASELINE_SHA,consumer_plan_sha256=C.P.sha(inputs/'plan.json'),
        source_evidence_manifest_sha256=SOURCE_SHA,producer_sha256=producers,protocol=original['protocol'],
        fixture_rows=original['fixture_rows'],native_NDR_readback_required=True,
        scope='Block-local NDR import only. Exact original17fixtures/six-corner-policy calls/numeric tolerances; no model qualification.',
        files_sha256=file_inventory(output))
    write(output/'plan.json',plan);verify(output,C.P.sha(output/'plan.json'))
    return dict(plan_sha256=C.P.sha(output/'plan.json'),native_executed=False,model_qualified=False)


def verify(base,plan_hash):
    need(C.P.sha(base/'plan.json')==plan_hash,'NDR plan identity differs');plan=json.loads((base/'plan.json').read_text())
    need(plan.get('schema')==SCHEMA and plan.get('qualified') is False and plan.get('model_qualified') is False and
        plan.get('native_executed') is False and plan.get('root_go_required') is True and
        plan.get('baseline_unit_plan_sha256')==BASELINE_SHA and plan.get('native_NDR_readback_required') is True,
        'NDR typed scope/promotion differs')
    actual=file_inventory(base);actual.pop('plan.json')
    need(actual==plan['files_sha256'],'NDR complete prepared membership/bytes changed')
    old=U.verify(base/'baseline-unit-preparation',BASELINE_SHA)
    source_evidence(base/'source-evidence');original=C.verify_plan(base/'baseline-unit-preparation/consumer-inputs',old['consumer_plan_sha256'])
    fixed,witness=add_ndr((base/'baseline-unit-preparation/consumer-inputs/fixture.def').read_text(),
        (base/'consumer-inputs/tech.lef').read_text(),(base/'consumer-inputs/widths.lef').read_text())
    producers=producer_map(original)
    need(plan['producer_sha256']==producers and plan['protocol']==original['protocol'] and plan['fixture_rows']==original['fixture_rows'] and
        plan['source_evidence_manifest_sha256']==SOURCE_SHA and
        json.loads((base/'NDR-witness.json').read_text())==witness and (base/'consumer-inputs/fixture.def').read_text()==fixed and
        C.verify_plan(base/'consumer-inputs',plan['consumer_plan_sha256'])==inner_plan(original,fixed,producers),
        'NDR correction/witness/unchanged numerical policy differs')
    for name,value in producers.items():need(C.P.sha(Path(__file__).with_name(name))==value,'NDR/frozen producer differs')
    return plan


def run(base,plan_hash,output):
    plan=verify(base,plan_hash);need(not output.exists() and output.parent.is_dir(),'Fresh NDR execution owner required')
    output.mkdir();result=dict(schema='pinwheel.streaming-8x4-rc-consumer-DEF-NDR-execution.v1',qualified=False,
        model_qualified=False,plan_sha256=plan_hash,passed=False,all_six_native_calls_closed=False,
        consumer_policy_unchanged=True,native_NDR_readback_required=True)
    try:
        inner=C.run(base/'consumer-inputs',plan['consumer_plan_sha256'],output/'native')
        result.update(passed=inner['passed'],all_six_native_calls_closed=len(inner['jobs'])==6,
            inner_report_sha256=C.P.sha(output/'native/report.json'))
    except BaseException as error:result['error']=type(error).__name__+': '+str(error)
    finally:
        result['inputs_unchanged']=verify(base,plan_hash)==plan;result['passed'] &= result['inputs_unchanged']
        write(output/'report.json',result)
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__);sub=parser.add_subparsers(dest='mode',required=True)
    p=sub.add_parser('prepare')
    for name in ('baseline','source','failed','output'):p.add_argument('--'+name,type=Path,required=True)
    for mode in ('verify','run'):
        p=sub.add_parser(mode);p.add_argument('--inputs',type=Path,required=True);p.add_argument('--plan-sha256',required=True)
        if mode=='run':p.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    value=prepare(args.baseline,args.source,args.failed,args.output) if args.mode=='prepare' else \
        verify(args.inputs,args.plan_sha256) if args.mode=='verify' else run(args.inputs,args.plan_sha256,args.output)
    print(json.dumps(value,indent=2));return 2 if args.mode=='run' and not value['passed'] else 0


if __name__=='__main__':raise SystemExit(main())
