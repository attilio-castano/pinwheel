#!/usr/bin/env python3
"""Check one opt-in balanced mapping of the verified PairedValidation circuit.

The source RTL, logic and state stay fixed. Both corner checks use the same
new mapped circuit. Placement coordinates guide leaf grouping; fresh physical
implementation is required before claiming any physical improvement.
"""
import argparse
from copy import deepcopy
import json
from pathlib import Path
import runpy
import shutil
import time

from mapped_buffer_balance import rebalance
from paired_mapping import CAD, MACRO, cut, metrics, timing, write
from physical_buffer_repair import _bufferless
from physical_target import path_expectations, state_and_paths
from validation_run import Commands, fresh_directory, sha

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--tag', required=True)
    parser.add_argument('--selection', type=Path, required=True)
    parser.add_argument('--physical-receipt', type=Path, required=True)
    parser.add_argument('--guidance-context', type=Path, required=True)
    args = parser.parse_args()
    out = fresh_directory(ROOT / 'build/validation', args.tag)
    run = Commands(ROOT, out, default_timeout=120)
    started = time.monotonic()
    report = dict(schema=1, status='running', commands=run.records,
                  placement_or_routing=False, variants={})
    inputs = {}
    try:
        selected = json.loads(args.selection.read_text())
        source_path = ROOT / selected['report']
        source = json.loads(source_path.read_text())
        if sha(source_path) != selected['report_sha256'] or source['status'] != 'passed' or not source['inputs_unchanged']:
            raise ValueError('Changed or unsuccessful source mapping')
        receipt = json.loads(args.physical_receipt.read_text())
        key = str(args.guidance_context.resolve().relative_to(args.physical_receipt.resolve().parent))
        if (receipt['status'] != 'completed' or not receipt['inputs_unchanged'] or
                receipt['container_state'] != 'absent' or
                receipt['artifacts_sha256'].get(key) != sha(args.guidance_context)):
            raise ValueError('Unbound or unsuccessful placement guidance')
        context = json.loads(args.guidance_context.read_text())
        source_dir = source_path.parent
        # Keep the original source audit explicit: a changed upstream implementation
        # requires a new source check, not attribution of this receipt to new RTL.
        for p, h in source['source_sha256'].items():
            if sha(ROOT / p) != h:
                raise ValueError('Changed verified source: ' + p)
        inputs.update(source['source_sha256'])
        required = [source_path, args.selection, args.physical_receipt, args.guidance_context,
                    ROOT / 'scripts/mapped_buffer_balance.py', Path(__file__).resolve(),
                    ROOT / 'test/test_mapped_buffer_balance.py']
        for rel in ['typical/readback.json', 'assembly.json', 'vectors.txt', 'chip.sv']:
            p = source_dir / rel
            if sha(p) != source['artifact_sha256'][str(p.relative_to(ROOT))]:
                raise ValueError('Changed source artifact: ' + rel)
            required.append(p)
        for p in required:
            inputs[str(p.resolve())] = sha(p)
        report['source_sha256'] = inputs
        report['source_mapping'] = dict(path=str(source_path), sha256=sha(source_path))
        report['guidance'] = dict(path=str(args.guidance_context), sha256=sha(args.guidance_context),
            database_sha256=context['database_sha256'])
        description = json.loads((source_dir / 'assembly.json').read_text())['chip']
        shutil.copyfile(source_dir / 'assembly.json', out / 'assembly.json')
        shutil.copyfile(source_dir / 'chip.sv', out / 'chip.sv')
        shutil.copyfile(source_dir / 'vectors.txt', out / 'vectors.txt')
        data = json.loads((source_dir / 'typical/readback.json').read_text())
        candidate, trees = rebalance(data, 'tt_um_pinwheel', context, fixed_cells=['memory.storage'])
        write(out / 'balanced-top.json', dict(modules={'tt_um_pinwheel':candidate['modules']['tt_um_pinwheel']}))
        write(out / 'tree-comparison.json', trees)
        report['tree_summary'] = dict(removed_buffers=len(trees['removed_buffers']),
            added_buffers=trees['distribution']['added_buffers'],
            old_maximum_levels=max(t['maximum_levels'] for t in trees['original_forests']),
            new_maximum_levels=max(t['maximum_levels'] for t in trees['balanced_forests']))
        libraries = runpy.run_path(str(ROOT / 'scripts/check-map-tile.py'))['pinned_libraries']()
        if {k:sha(v) for k,v in libraries.items()} != source['libraries_sha256']:
            raise ValueError('Changed corner libraries')
        report['libraries_sha256'] = dict(source['libraries_sha256'])

        def yosys(label, lines, reject=None):
            script = out / (label + '.ys')
            script.write_text('\n'.join(map(str,lines)) + '\n')
            return run([CAD/'yosys','-Q','-T','-s',script],label,reject=reject)

        target = json.loads((ROOT / 'physical/targets/paired.json').read_text())
        report['path_expectations'] = {}
        for corner, lib in libraries.items():
            folder = out / corner
            folder.mkdir()
            macro = source_dir / corner / 'macro.lib'
            reference_file = source_dir / corner / 'candidate-cut.json'
            for p in [macro, reference_file]:
                if sha(p) != source['artifact_sha256'][str(p.relative_to(ROOT))]:
                    raise ValueError('Changed corner source')
                inputs[str(p)] = sha(p)
            yosys(corner+'-save',[f'read_liberty -lib {lib}',f'read_liberty -lib {macro}',
                f'read_json {out}/balanced-top.json','hierarchy -check -top tt_um_pinwheel',
                'clean','check -assert',f'write_verilog -noattr -noexpr {folder}/design.v'])
            yosys(corner+'-readback',[f'read_liberty -lib {lib}',f'read_liberty -lib {macro}',
                f'read_verilog {folder}/design.v','hierarchy -check -top tt_um_pinwheel',
                'check -assert',f'write_json {folder}/readback.json'])
            saved = json.loads((folder/'readback.json').read_text())
            module = saved['modules']['tt_um_pinwheel']
            if _bufferless(module) != _bufferless(data['modules']['tt_um_pinwheel']):
                raise ValueError('Saved mapping changed nonbuffer signal identity')
            circuit, projection = cut(module, description)
            if projection != source['variants']['typical']['state_projection']:
                raise ValueError('Changed state projection')
            reference = json.loads(reference_file.read_text())['modules']['candidate']
            write(folder/'reference-cut.json',dict(modules={'reference':reference}))
            write(folder/'candidate-cut.json',dict(modules={'candidate':circuit}))

            def prove(path,label,reject=None):
                text = yosys(label,[f'read_liberty -ignore_miss_func {lib}',
                    f'read_json {folder}/reference-cut.json',f'read_json {path}',
                    'miter -equiv -flatten -make_outputs reference candidate miter',
                    'hierarchy -check -top miter','flatten','opt -full',
                    'sat -verify -prove trigger 0 -set-def-inputs miter'],reject)
                if not reject and 'SAT proof finished - no model found: SUCCESS!' not in text:
                    raise ValueError('Incomplete full mapped equivalence')
            prove(folder/'candidate-cut.json',corner+'-proof')
            if corner == 'typical':
                mutant = deepcopy(circuit)
                b = next(c for n,c in mutant['cells'].items() if n.startswith('paired_balanced_'))
                b['type']='sg13cmos5l_inv_1';b['connections']['Y']=b['connections'].pop('X')
                b['port_directions']['Y']=b['port_directions'].pop('X')
                write(folder/'negative-cut.json',dict(modules={'candidate':mutant}))
                prove(folder/'negative-cut.json','inverted-balanced-buffer-negative','proof did fail')
            _, roles = state_and_paths(module,description,target)
            observed = path_expectations(module,roles)
            if observed != source['path_expectations']['typical']:
                raise ValueError('Changed semantic path reachability')
            report['path_expectations'][corner]=observed
            measured = metrics(saved,description)
            if measured['maximum_signal_fanout'] > 8:
                raise ValueError('Saved signal fanout exceeds budget')
            report['variants'][corner]=dict(metrics=measured,state_projection=projection,
                mapped_sha256=sha(folder/'design.v'))
            shutil.copyfile(lib,folder/'cells.lib');shutil.copyfile(macro,folder/'macro.lib')
        report['coverage']=source['coverage']
        models=[Path(p) if Path(p).is_absolute() else ROOT/p for p in source['source_sha256']
                if Path(p).name in ['sg13cmos5l_stdcell.v','sg13cmos5l_udp.v',
                    MACRO+'.v','RM_IHPSG13_1P_core_behavioral_bm_bist.v']]
        if len(models)!=4:
            raise ValueError('Ambiguous validated cell/macro models')
        run([CAD/'iverilog','-g2012','-DFUNCTIONAL','-s','chip_tb','-o',out/'mapped.vvp',
             out/'typical/design.v',ROOT/'test/chip_tb.sv',*models],'mapped-compile')
        text=run([CAD/'vvp',out/'mapped.vvp','+vectors='+str(out/'vectors.txt')],'mapped-oracle')
        if f'Passed {source["coverage"]["chip"]["edges"]} independent whole-chip edges' not in text:
            raise ValueError('Incomplete pin oracle')
        timing(run,out,description,report)
        report['comparison']={}
        for corner,v in report['variants'].items():
            area=v['metrics']['total_cell_and_macro_area_um2']
            prior=source['variants'][corner]['metrics']['total_cell_and_macro_area_um2']
            report['comparison'][corner]=dict(mapped_area_delta_um2=round(area-prior,4),
                mapped_area_delta_percent=round(100*(area/prior-1),4),
                signal_electrical_pass=not any(v['cell_timing']['electrical_violations'].values()),
                setup_pass=v['cell_timing']['setup_slack_ns']>=0,
                hold_pass=v['cell_timing']['hold_slack_ns']>=0)
        report.update(status='passed',boundary='Same verified RTL and nonbuffer logic. Both corner checks use one balanced mapped circuit. SAT observes arbitrary state and SRAM responses; pin replay is finite and zero delay. Physical implementation and closed-memory refinement are separate.')
    except BaseException as e:
        report.update(status='failed',error=f'{type(e).__name__}: {e}')
        raise
    finally:
        report['source_sha256']=inputs
        report['inputs_unchanged']=all(sha(ROOT/p)==h for p,h in inputs.items())
        report['seconds']=round(time.monotonic()-started,3)
        if not report['inputs_unchanged']:
            report['status']='failed'
        report['artifact_sha256']={str(p.relative_to(ROOT)):sha(p) for p in out.rglob('*') if p.is_file()}
        write(out/'report.json',report)
        print({k:report.get(k) for k in ['status','seconds','tree_summary','comparison','error']})


if __name__=='__main__':
    main()
