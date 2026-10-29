"""New24 authority around the pinned complete GEN04 actual-M generator.

Only ROOT, claim schemas, and the old target/source-dependency admission are
replaced. The complete generation body (all6039 D/state,24 outputs, clock DAG,
packing/initialization/typed joins, full required theorem and private audit)
remains the exact pinned GEN04 text. Original owners and receipts stay intact.
This module prepares sources only; a separate reviewed Native driver is needed.
"""
import argparse
import difflib
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import types

sys.dont_write_bytecode = True
import streaming_8x4_final_runtime as R
import streaming_8x4_final_dependency as D
import streaming_8x4_closure24_final_authority as A
import streaming_8x4_final_m as ORIGINAL
import streaming_tt_fresh_foundation as F

ROOT = Path(__file__).resolve().parents[1]
GENERATOR_PIN = '677ea58ce9eb6057b29859f4532802ff9fd28f108a754252cc91d02e0ead4300'
GENERATOR_RELATIVE = 'final-M-generator/build/streaming-physical-development/formal-actual-M-generator-unqualified-04/generate.py'
SOURCES = ('scripts/streaming_8x4_closure24_final_m.py',
    'scripts/streaming_8x4_closure24_final_authority.py',
    'scripts/streaming_8x4_closure24_final_connectivity.py',
    'scripts/streaming_8x4_closure24_final_target.py',
    'scripts/streaming_8x4_final_m.py', 'scripts/streaming_8x4_final_authority.py',
    'scripts/streaming_8x4_final_dependency.py', 'scripts/streaming_8x4_final_runtime.py')


def bound(path): return dict(path=str(R.regular(path).resolve()),sha256=R.digest(path))


def actual_target(config, source_commit):
    authority = A.verify(config['authority']['path'])
    F.require(R.digest(config['authority']['path']) == config['authority']['sha256'] and
        authority['source_candidate_commit'] == source_commit == D.SOURCE, 'Fresh actual-M source/physical authority differs')
    report, packet = A.closed_export(config['export_report']['path'],config['export_report']['sha256'])
    F.require(authority['target'] == report['target'] and config['target_scope'] == 'final-routed-digital',
        'Actual M must target the authenticated latest completed routed state')
    F.require(authority.get('physical_candidate') == report.get('physical_candidate'),
        'Actual M mixes original and repaired candidate authority')
    native = Path(config['export_report']['path']).parent/'native/export'
    expected = dict(export_report=Path(authority['export_report']['path']),export_receipt=native/'receipt.json',
        export_inventory=native/'inventory.json',export_connectivity=native/'connectivity.json',
        semantic_state_map=Path(authority['semantic_state_map']['path']),
        physical_report=Path(authority['target']['physical_report']['path']),physical_state=Path(authority['target']['physical_state']['path']))
    for name,path in expected.items(): F.require(config[name] == bound(path), 'Actual M selected another target artifact: '+name)
    mapping = R.read(expected['semantic_state_map'])
    intake = R.read(authority['M_intake']['path']); source = intake['source_candidate']['path']
    prepared = Path(packet['request']['preparation']['path']).parent
    repeated, resized = A.map_all_state(source,prepared/'inputs/semantic-q-map.json',
        intake['original_flat_reference']['path'],intake['original_flat_semantic_map']['path'],
        expected['export_connectivity'],R.read(authority['worker_config']['path'])['corners']['typ']['path'])
    F.require(mapping['rows'] == repeated and mapping['database_sha256'] == authority['target']['actual_odb']['sha256'],
        'Independent complete semantic-state mapping differs')
    expected['actual_odb'] = Path(authority['target']['actual_odb']['path'])
    return expected,R.read(config['export_receipt']['path'])


dependency_context = ORIGINAL.dependency_context


replace_once = ORIGINAL.replace_once


def adapted_generator(payload):
    """Reuse the exact original transformation, replacing only new24 authority names."""
    text, _ = ORIGINAL.adapted_generator(payload)
    text = replace_once(text, 'import streaming_8x4_final_m as D',
        'import streaming_8x4_closure24_final_m as D')
    text = replace_once(text, "PROFILE='pinwheel.streaming-8x4-actual-target-M.v1'",
        "PROFILE='pinwheel.closure24-actual-target-M.v1'")
    text = replace_once(text, "SCHEMA='pinwheel.streaming-8x4-actual-M-generation.v1'",
        "SCHEMA='pinwheel.closure24-actual-M-generation.v1'")
    original = payload.decode()
    diff = ''.join(difflib.unified_diff(original.splitlines(keepends=True), text.splitlines(keepends=True),
        fromfile='immutable-GEN04/generate.py', tofile='fresh-closure24/generate.py'))
    return text, diff


load_generator = ORIGINAL.load_generator


def generate(authority_path, dependency_path, recovery, output):
    authority = A.verify(authority_path); dep = D.verify(dependency_path)
    output = A.C.owned(output, ROOT);F.require(not output.exists(), 'Preserve earlier complete actual-M source generation')
    commit = subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True,timeout=30).strip()
    producer = {}
    for name in SOURCES:
        data = subprocess.check_output(['git','show',commit+':'+name],cwd=ROOT,timeout=30)
        F.require(hashlib.sha256(data).hexdigest() == R.digest(ROOT/name), 'Commit fresh M producer first: '+name)
        producer[str(ROOT/name)] = R.digest(ROOT/name)
    original = R.regular(Path(recovery)/GENERATOR_RELATIVE).resolve()
    text,diff = adapted_generator(original.read_bytes()); output.mkdir(parents=True)
    owner = output/'producer';owner.mkdir(); generator=owner/'generate.py';generator.write_text(text)
    (owner/'adaptation.diff').write_text(diff)
    intake = R.read(authority['M_intake']['path'])
    config = {name:intake[name] for name in ('export_report','export_receipt','export_inventory','export_connectivity',
        'semantic_state_map')}
    config.update(source_dependency_prepared=bound(dependency_path),authority=bound(authority_path),
        physical_report=authority['target']['physical_report'],physical_state=authority['target']['physical_state'],
        target_scope='final-routed-digital',formal_producer_commit=D.FORMAL)
    config_path = output/'generation-request.json'; R.write(config_path,config)
    mroot = output/'M'; module = load_generator(generator)
    manifest,sources = module._generate(config_path,mroot)
    F.require(manifest['scope_profile'] == 'pinwheel.closure24-actual-target-M.v1' and
        manifest['all6039_state_bijection'] is True and manifest['all24_public_endpoints'] is True and
        manifest['target_scope'] == 'final-routed-digital' and len(sources) == len(manifest['m_rows']) and
        manifest['m_rows'] and manifest['stages'] and manifest['actual_database_sha256'] == authority['target']['actual_odb']['sha256'],
        'Complete actual-M generation did not retain its full scope')
    for stage in manifest['stages']:
        directory=Path(stage['out']); F.require(directory.parent==mroot,'Actual-M stage escapes fresh root');directory.mkdir(parents=True)
        for name in stage['modules']: (directory/(name+'.lean')).write_text(sources[name])
        (directory/'modules.json').write_text(json.dumps(stage['modules'],indent=2)+'\n')
        F.require(bound(directory/'modules.json') == stage['schedule'],'Actual-M complete schedule serialization differs')
    manifest['fresh_adaptation'] = dict(original=bound(original),generator=bound(generator),diff=bound(owner/'adaptation.diff'),
        producer_commit=commit,producer_sha256=producer,authority=bound(authority_path),source_N=bound(dependency_path))
    R.write(output/'generation-manifest.json',manifest)
    # Full independent rederivation is mandatory before Native; no count is
    # admitted from this staging command alone.
    R.write(output/'prepared.json',dict(schema='pinwheel.closure24-actual-M-preparation.v1',qualified=False,
        passed=True,native_executed=False,final_correspondence_proved=False,
        producer_commit=commit,source_candidate_commit=dep['source_commit'],authority=bound(authority_path),
        physical_candidate=authority['physical_candidate'],
        source_N=bound(dependency_path),generation_request=bound(config_path),generation_manifest=bound(output/'generation-manifest.json'),
        generator=bound(generator),original_generator=bound(original),adaptation_diff=bound(owner/'adaptation.diff'),
        producer_sha256=producer,all_actual_modules=len(sources),external_N_modules=len(dep['positive_import_rows']),
        complete_positive_modules=len(sources)+len(dep['positive_import_rows']),
        actual_odb=authority['target']['actual_odb'],target_scope='final-routed-digital',
        independent_rederivation_before_native_required=True,separate_private_controls_required=True,
        boundary='Complete fresh actual-M source staging with explicit historical N/F03 reuse. No Native M, private-control or physical acceptance.'))
    return output/'prepared.json'


def verify(path, *, rederive=False):
    path=R.regular(path).resolve();A.C.owned(path.parent, ROOT);record=R.read(path)
    F.require(record.get('schema')=='pinwheel.closure24-actual-M-preparation.v1' and record.get('passed') is True and
        record.get('qualified') is False and record.get('native_executed') is False and
        record.get('final_correspondence_proved') is False,'Fresh complete actual-M preparation required')
    for key in ('authority','source_N','generation_request','generation_manifest','generator','original_generator','adaptation_diff'):
        F.require(R.digest(record[key]['path'])==record[key]['sha256'],'Actual-M prepared artifact changed: '+key)
    F.require(all(R.digest(path)==pin for path,pin in record['producer_sha256'].items()),'Actual-M producer changed')
    authority=A.verify(record['authority']['path']);D.verify(record['source_N']['path'])
    F.require(record.get('physical_candidate')==authority['physical_candidate'],'Prepared actual M changed the physical candidate')
    text,diff=adapted_generator(R.regular(record['original_generator']['path']).read_bytes())
    F.require(R.regular(record['generator']['path']).read_text()==text and
        R.regular(record['adaptation_diff']['path']).read_text()==diff,'Actual-M adapter is not the exact reviewed transformation')
    manifest=R.read(record['generation_manifest']['path'])
    F.require(len(manifest['m_rows'])==record['all_actual_modules'] and record['external_N_modules']==395 and
        record['complete_positive_modules']==395+record['all_actual_modules'] and
        [row['module'] for row in manifest['m_rows']]==[name for stage in manifest['stages'] for name in stage['modules']],
        'Actual-M complete derived module inventory/order changed')
    for row in manifest['m_rows']:F.require(R.digest(row['source'])==row['source_sha256'],'Generated actual-M source changed')
    for stage in manifest['stages']:F.require(bound(stage['schedule']['path'])==stage['schedule'],'Complete actual-M schedule changed')
    if rederive:
        module=load_generator(record['generator']['path']);expected=module.derive(record['generation_request']['path'],manifest['out_root'])
        F.require(expected=={key:value for key,value in manifest.items() if key!='fresh_adaptation'},
            'Independent complete actual-M rederivation differs')
    return record,manifest


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    modes=parser.add_subparsers(dest='mode',required=True);prepare=modes.add_parser('prepare')
    for name in ('authority','source-N','recovery','output'):prepare.add_argument('--'+name,required=True,type=Path)
    check=modes.add_parser('verify');check.add_argument('--prepared',required=True,type=Path);check.add_argument('--rederive',action='store_true')
    args=parser.parse_args()
    if args.mode=='prepare':print(generate(args.authority,args.source_N,args.recovery,args.output))
    else:print(json.dumps({'all_actual_modules':verify(args.prepared,rederive=args.rederive)[0]['all_actual_modules']}))


if __name__=='__main__':main()
