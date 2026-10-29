"""Prepare a fresh official8x4 implementation from the exact proved6x4 logic.

The historical receipt stays immutable. Its selected unchanged logical payload
is revalidated by original hashes, and the new geometry/recipe has its own
versioned receipt. This command performs HOST file preparation only, never CAD.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess

from streaming_8x4_geometry import ROOT, ALLOCATION, DIE, admit, allocation_tcl, regular, require, sha

BASELINE_SHA256 = '4fc4d7a3e336cbe8a327fd7ca33bfb17ee5996ca5dacdb9f4a08a0a88b3231d5'
LOGICAL_FILES = ('design.v', 'design-original.v', 'certified.json', 'source-state.json',
                 'semantic-q-map.json', 'cost.json', 'parent-intake.json', 'optimized-worker.json', 'raw-gate.json')
SOURCE_FILES = ('scripts/streaming_8x4_geometry.py', 'scripts/streaming_8x4_prepare.py',
                'scripts/streaming_8x4_readback.py', 'scripts/streaming_8x4_run.py', 'physical/streaming_8x4/pdn.tcl',
                'physical/streaming_8x4/librelane_plugin_streaming_8x4.py',
                'physical/streaming_8x4/allocation.json', 'physical/streaming-tt.sdc',
                'tools/physical-toolchain.json', 'tools/streaming-tt-signoff.json')


def read(path):
    def pairs(rows):
        result = {}
        for key,value in rows:
            require(key not in result, 'Duplicate JSON key: ' + key)
            result[key] = value
        return result
    return json.loads(regular(path).read_text(), object_pairs_hook=pairs)


def write(path, value):
    Path(path).write_text(json.dumps(value, indent=2, allow_nan=False) + '\n')


def inventory(root):
    root = Path(root).resolve()
    result = {}
    for path in sorted(root.rglob('*')):
        require(not path.is_symlink(), 'Aliased prepared8x4 input')
        if path.is_file():
            result[str(path.relative_to(root))] = sha(path)
    return result


def validate_baseline(parent_path):
    parent_path = regular(parent_path)
    require(sha(parent_path) == BASELINE_SHA256, 'Not the exact retained balanced prephysical parent')
    parent = read(parent_path)
    require(parent.get('schema') == 'pinwheel.streaming-tt-physical-input.v2' and
            parent.get('recipe') == 'optimized_nominal_rc' and parent.get('depth') == 2 and
            parent.get('qualified') is False and parent.get('physical_acceptance_claim') is False and
            parent.get('synthesis_bypassed') is True and parent.get('candidate',{}).get('source_ff_bits') == 6039,
            'Retained prephysical parent contract differs')
    inputs = parent_path.parent / 'inputs'
    # Rehash the complete original staged input membership, including its source
    # producer. This does not execute the historical producer or change paths in it.
    require(inventory(inputs) == parent.get('input_sha256'), 'Restored complete baseline input membership/bytes differ')
    derivative = parent.get('physical_verilog_derivation',{})
    flags = ('passed', 'exact_tuple_comparison', 'all_actual_cells_and_pins', 'flatten_only',
             'flat_native_reimport', 'full_public_port_shape', 'all_ff_d_clock_reset_and_io')
    require(all(derivative.get(key) is True for key in flags) and derivative.get('semantic_ff_bits') == 6039 and
            derivative.get('source_verilog_sha256') == sha(inputs/'design-original.v') and
            derivative.get('physical_verilog_sha256') == sha(inputs/'design.v') and
            parent['candidate']['netlist_sha256'] == sha(inputs/'certified.json'),
            'Retained physical flatten/reimport contract differs')
    state = read(inputs/'source-state.json')
    qmap = read(inputs/'semantic-q-map.json')
    require(state.get('source_ff_bits') == 6039 and len(state.get('source_state',[])) == 6039 and
            qmap.get('physical_ff_bits') == 6039 and len(qmap.get('rows',[])) == 6039 and
            len({row['candidate_ff'] for row in qmap['rows']}) == 6039 and
            len({row['candidate_q'] for row in qmap['rows']}) == 6039,
            'Retained complete semantic state inventory differs')
    return parent, inputs


def recipe(config, allocation, template_name='tt_block_8x4_pgvdd.def'):
    before = json.loads(json.dumps(config))
    require(before.get('CLOCK_PERIOD') == 20 and before.get('PL_TARGET_DENSITY_PCT') == 85 and
            before.get('DIE_AREA') == [0,0,1289.28,710.64] and
            before.get('FP_DEF_TEMPLATE') == 'dir::tt_block_6x4_pgvdd.def' and
            before.get('DESIGN_NAME') == 'tt_um_pinwheel_streaming_ready_d2', 'Unsupported physical baseline recipe')
    after = dict(before, FP_DEF_TEMPLATE='dir::' + template_name,
                 DIE_AREA=[0,0,DIE[2]/1000,DIE[3]/1000], meta={'flow':'Streaming8x4Certified'})
    allowed = {'FP_DEF_TEMPLATE','DIE_AREA','meta'}
    changed = {name:dict(before=before.get(name), after=after.get(name))
               for name in sorted(set(before)|set(after)) if before.get(name) != after.get(name)}
    require(set(changed) == allowed and after['CLOCK_PERIOD'] == 20 and after['PL_TARGET_DENSITY_PCT'] == 85,
            '8x4 footprint control changes undeclared recipe settings')
    ledger = dict(schema='pinwheel.streaming-8x4-footprint-recipe.v1', baseline='balanced-d2-01',
        baseline_prepared_input_sha256=BASELINE_SHA256, baseline_core_config_sha256=hashlib.sha256(
            (json.dumps(before,sort_keys=True,separators=(',',':'))+'\n').encode()).hexdigest(),
        allocation_sha256=allocation['allocation_sha256'], template_sha256=allocation['template_sha256'],
        changes=changed, unchanged_clock_period_ns=20, unchanged_placement_target_density_pct=85,
        pdn_grid_adaptation=dict(before=dict(pitch_dbu=50000,first_center_dbu=16160),
            after=dict(pitch_dbu=49880,first_center_dbu=16400),width_dbu=2100,pair_delta_dbu=7680,
            reason='Fit complete power/ground pairs at official8x4 boundary; preserve widths/separation and >=600DBUpublic clearance.'),
        logical_payload_unchanged=True, fresh_floorplan_required=True, qualified=False, physical_acceptance=False)
    return after, ledger


def prepare(parent_path, template, pdk, pdk_tree, output):
    from streaming_tt_pdk import verify_complete_pdk
    from streaming_tt_intake import dependency_closure
    parent_path,template,pdk_tree = map(regular,(parent_path,template,pdk_tree))
    parent, old_inputs = validate_baseline(parent_path)
    geometry = admit(template)
    pdk = Path(pdk).resolve(strict=True)
    pdk_identity = verify_complete_pdk(pdk, read(ROOT/'tools/physical-toolchain.json'),
        read(ROOT/'tools/streaming-tt-signoff.json'), tree_path=pdk_tree)
    source_head = subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()
    closure = dependency_closure(ROOT,SOURCE_FILES)
    source_hashes = {}
    for name in closure['files']:
        path = regular(ROOT/name)
        committed = subprocess.check_output(['git','show',source_head+':'+name],cwd=ROOT)
        require(hashlib.sha256(committed).hexdigest() == sha(path), 'Commit8x4 producer before preparation: ' + name)
        source_hashes[name] = sha(path)
    output = Path(output).absolute()
    require(not output.exists(), 'Preserve prior8x4 preparation')
    output.mkdir(parents=True)
    inputs = output/'inputs'; inputs.mkdir()
    for name in source_hashes:
        target = inputs/'producer'/name
        target.parent.mkdir(parents=True,exist_ok=True)
        shutil.copyfile(ROOT/name,target)
        require(sha(target) == source_hashes[name], '8x4 producer snapshot differs')
    for name in LOGICAL_FILES:
        shutil.copyfile(regular(old_inputs/name), inputs/name)
    shutil.copyfile(regular(ROOT/'physical/streaming-tt.sdc'),inputs/'core.sdc')
    require(sha(inputs/'core.sdc') == parent['input_sha256']['core.sdc'], 'Original20ns SDC changed')
    shutil.copyfile(template, inputs/'tt_block_8x4_pgvdd.def')
    shutil.copyfile(ALLOCATION,inputs/'allocation.json')
    shutil.copyfile(ROOT/'physical/streaming_8x4/pdn.tcl',inputs/'pdn.tcl')
    shutil.copyfile(ROOT/'physical/streaming_8x4/librelane_plugin_streaming_8x4.py',inputs/'librelane_plugin_streaming_8x4.py')
    for name in ('streaming_8x4_geometry.py','streaming_8x4_readback.py'):
        shutil.copyfile(ROOT/'scripts'/name,inputs/name)
    (inputs/'allocation.tcl').write_text(allocation_tcl(geometry))
    config, ledger = recipe(read(old_inputs/'core.json'),geometry)
    write(inputs/'core.json',config)
    write(inputs/'seed.json',dict(nl='/work/inputs/design.v',metrics={}))
    write(inputs/'geometry-admission.json',geometry)
    write(inputs/'recipe.json',ledger)
    write(inputs/'info.yaml',dict(project=dict(top_module=config['DESIGN_NAME'],tiles='8x4',analog_pins=0,uses_3v3=False),pinout={}))
    shutil.copyfile(parent_path,inputs/'historical-parent-inputs.json')
    # Native PDK remains an explicit separate read-only mount, not an alias in
    # the staged input inventory. No shared PDK byte is modified.
    receipt = dict(schema='pinwheel.streaming-8x4-preparation.v1', prepared_utc=datetime.now(timezone.utc).isoformat(),
        producer_commit=source_head,producer_sha256=source_hashes, producer_dependency_closure=closure,
        historical_parent=dict(path=str(parent_path),sha256=sha(parent_path)),
        candidate_source_commit=parent['candidate']['source_commit'], historical_source_proof_inherited_only_for_exact_logic=True,
        synthesis_bypassed=True, logical_payload_sha256={name:sha(inputs/name) for name in LOGICAL_FILES},
        source_ff_bits=6039, clock_period_ns=20, tiles='8x4',fresh_floorplan_required=True,
        input_sha256=inventory(inputs), pdk_root=str(pdk),pdk_tree=dict(path=str(pdk_tree),sha256=sha(pdk_tree)),
        pdk_identity=pdk_identity,geometry_admission=geometry,recipe=ledger,native_executed=False,
        qualified=False,physical_acceptance=False,post_pnr_equivalence_proved=False,
        boundary='Fresh official8x4 implementation of exact retained balanced logical payload. Prephysical proof does not certify placement/CTS/repair/routing. All final proof, RC/timing, physical and official TT gates remain separate.')
    require(inventory(old_inputs) == parent['input_sha256'] and sha(parent_path) == BASELINE_SHA256,
            'Historical baseline changed during8x4 preparation')
    verify_complete_pdk(pdk,read(ROOT/'tools/physical-toolchain.json'),read(ROOT/'tools/streaming-tt-signoff.json'),tree_path=pdk_tree)
    write(output/'preparation.json',receipt)
    return receipt


def verify(output):
    from streaming_tt_pdk import verify_complete_pdk
    from streaming_tt_intake import dependency_closure
    output = Path(output).absolute()
    receipt = read(output/'preparation.json')
    require(receipt.get('schema') == 'pinwheel.streaming-8x4-preparation.v1' and
            receipt.get('tiles') == '8x4' and receipt.get('source_ff_bits') == 6039 and
            receipt.get('clock_period_ns') == 20 and receipt.get('physical_acceptance') is False and
            receipt.get('fresh_floorplan_required') is True and inventory(output/'inputs') == receipt.get('input_sha256'),
            'Prepared8x4 input contract differs')
    for name,expected in receipt['producer_sha256'].items():
        require(sha(ROOT/name) == expected, '8x4 producer changed: ' + name)
        require(sha(output/'inputs/producer'/name) == expected, '8x4 staged producer changed: ' + name)
    require(dependency_closure(ROOT,SOURCE_FILES) == receipt['producer_dependency_closure'], '8x4 producer import closure changed')
    geometry = admit(output/'inputs/tt_block_8x4_pgvdd.def',output/'inputs/allocation.json')
    require(geometry == receipt['geometry_admission'] == read(output/'inputs/geometry-admission.json') and
            (output/'inputs/allocation.tcl').read_text() == allocation_tcl(geometry), 'Staged8x4 geometry differs')
    config,ledger = read(output/'inputs/core.json'),read(output/'inputs/recipe.json')
    historical = read(output/'inputs/historical-parent-inputs.json')
    require(sha(output/'inputs/historical-parent-inputs.json') == BASELINE_SHA256 and
            receipt['recipe'] == ledger and config['CLOCK_PERIOD'] == 20 and config['DIE_AREA'] == [0,0,1724.16,710.64],
            'Staged8x4 recipe differs')
    original_config = dict(config)
    for name,row in ledger['changes'].items(): original_config[name] = row['before']
    require(recipe(original_config,geometry) == (config,ledger), '8x4 recipe ledger does not reproduce')
    for name,expected in receipt['logical_payload_sha256'].items():
        require(sha(output/'inputs'/name) == expected == historical['input_sha256'][name], '8x4 logical payload changed')
    tree = regular(receipt['pdk_tree']['path'])
    require(sha(tree) == receipt['pdk_tree']['sha256'], '8x4 PDK Git inventory changed')
    identity = verify_complete_pdk(receipt['pdk_root'],read(ROOT/'tools/physical-toolchain.json'),
        read(ROOT/'tools/streaming-tt-signoff.json'),tree_path=tree)
    require(identity == receipt['pdk_identity'], '8x4 PDK changed after preparation')
    return receipt


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='mode',required=True)
    prep = sub.add_parser('prepare')
    for name in ('parent-input','template','pdk','pdk-tree','output'): prep.add_argument('--'+name,required=True,type=Path)
    check = sub.add_parser('verify'); check.add_argument('--output',required=True,type=Path)
    args = parser.parse_args()
    result = (prepare(args.parent_input,args.template,args.pdk,args.pdk_tree,args.output) if args.mode == 'prepare' else verify(args.output))
    print(json.dumps(dict(schema=result['schema'],tiles=result['tiles'],source_ff_bits=result['source_ff_bits'],physical_acceptance=False)))


if __name__ == '__main__': main()
