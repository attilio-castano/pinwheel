#!/usr/bin/env python3
"""Replay a validated chip oracle against a completed physical flow's netlist view.

Partial physical runs are allowed and remain partial evidence. The selected NL
view may precede the final ODB/DEF: both its actual path and identity are retained.
This is zero-delay functional simulation, not timing or universal equivalence.
"""
import argparse
import json
from pathlib import Path
import re
import time

import physical_checkpoint
import physical_target
from mapped_physical import selected_mapping
from validation_run import Commands, fresh_directory, sha

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--physical-report', type=Path, required=True)
    parser.add_argument('--comparison', type=Path, required=True)
    parser.add_argument('--pdk-root', type=Path, required=True)
    parser.add_argument('--tag', required=True)
    parser.add_argument('--mapped-export', type=Path,
                        help='Verified fresh ODB export receipt for a selected mapped chip')
    args = parser.parse_args()
    started = time.monotonic()
    physical = json.loads(args.physical_report.read_text())
    design = ROOT / 'build/physical' / physical['design']
    invocation = ROOT / 'build/physical' / (physical['tag'] + '-invocation.json')
    if sha(invocation) != physical['invocation_sha256']:
        raise RuntimeError('Physical invocation changed since reporting')
    additional_inputs = []
    master = 'RM_IHPSG13_1P_64x64_c2_bm_bist'
    vector_root = args.comparison.parent
    if args.mapped_export:
        preparation = json.loads((design / 'inputs.json').read_text())
        if preparation.get('physical_target'):
            target, paths, selected, _, _ = physical_target.resolve(design / 'target.json', ROOT)
            if sha(args.comparison) != selected['selection_sha256']:
                raise RuntimeError('Pin oracle selection differs from the physical target')
            for rel, digest in preparation['files_sha256'].items():
                if sha(design / rel) != digest:
                    raise RuntimeError('Changed prepared target: ' + rel)
            master = target['macro']['master']
            additional_inputs += [design / 'target.json', ROOT / 'scripts/physical_target.py',
                                  ROOT / 'scripts/paired_mapping.py']
        else:
            paths, selected = selected_mapping(args.comparison, preparation['mapped_input']['role'], ROOT)
        mapped_report = Path(selected['report'])
        mapping = json.loads(mapped_report.read_text())
        if selected['role'] == 'paired':
            oracle = mapped_report
            vector_key = str((oracle.parent / 'vectors.txt').relative_to(ROOT))
            model_names = ['ihp-sg13cmos5l/libs.ref/sg13cmos5l_stdcell/verilog/' + n
                           for n in ['sg13cmos5l_stdcell.v', 'sg13cmos5l_udp.v']]
            comparison = dict(vectors_sha256={'vectors.txt': mapping['artifact_sha256'][vector_key]},
                compatibility=dict(cell_models_sha256={n: mapping['source_sha256'][str((args.pdk_root / n).resolve())]
                                                      for n in model_names}), coverage=mapping['coverage'])
            if sha(ROOT / 'test/chip_tb.sv') != mapping['source_sha256']['test/chip_tb.sv']:
                raise RuntimeError('Changed validated paired pin bench')
        else:
            oracle = ROOT / mapping['pin_oracle_source']['report']
            if sha(oracle) != mapping['pin_oracle_source']['sha256']:
                raise RuntimeError('Changed mapped chip pin oracle')
            comparison = json.loads(oracle.read_text())
        vector_root = oracle.parent
        expected = selected['artifacts_sha256']['netlist']
        additional_inputs += [design / 'inputs.json', mapped_report, oracle, args.mapped_export]
    else:
        comparison = json.loads(args.comparison.read_text())
        for name, digest in comparison['source_sha256'].items():
            if sha(ROOT / name) != digest:
                raise RuntimeError('Stale comparison source: ' + name)
        expected = comparison['variants']['hybrid']['artifacts']['chip']['rtl_sha256']
    if sha(design / 'design.sv') != expected:
        raise RuntimeError('Physical source is not the validated hybrid chip')
    if 'state_path' in physical:
        stage = physical_checkpoint.artifact_path(physical['state_path'], design)
        if sha(stage) != physical['state_sha256']:
            raise RuntimeError('Changed reported physical state')
    else:
        stage = design / 'runs' / physical['tag'] / physical['last_completed_step'] / 'state_out.json'
    state = json.loads(stage.read_text())
    if args.mapped_export:
        export = json.loads(args.mapped_export.read_text())
        database = physical_checkpoint.artifact_path(state['odb'], design)
        netlist = ROOT / export['netlist']
        if (export.get('status') != 'passed' or export['physical_tag'] != physical['tag'] or
                export['source_database'] != str(database.relative_to(ROOT)) or
                sha(database) != export['source_database_sha256'] or
                sha(database) != physical['artifact_sha256'].get(str(database.relative_to(ROOT))) or
                sha(netlist) != export['netlist_sha256']):
            raise RuntimeError('Changed or unmatched mapped physical database export')
        additional_inputs.append(database)
    else:
        netlist = physical_checkpoint.artifact_path(state['nl'], design)
        if sha(netlist) != physical['artifact_sha256'].get(str(netlist.relative_to(ROOT))):
            raise RuntimeError('Changed or unreported physical netlist view')
    vectors = vector_root / 'vectors.txt'
    # The comparison records its complete vector file, not only its edge count.
    if sha(vectors) != comparison['vectors_sha256']['vectors.txt']:
        raise RuntimeError('Changed independent chip vectors')
    models = []
    for name, digest in comparison['compatibility']['cell_models_sha256'].items():
        file = args.pdk_root / name
        if sha(file) != digest:
            raise RuntimeError('Changed physical cell model: ' + name)
        models.append(file)
    lock = json.loads((ROOT / 'tools/storage-macros.json').read_text())
    for name in [master + '.v', 'RM_IHPSG13_1P_core_behavioral_bm_bist.v']:
        file = ROOT / 'build/storage/macros' / name
        if sha(file) != lock['files_sha256']['verilog/' + name]:
            raise RuntimeError('Changed macro model: ' + name)
        models.append(file)
    bench = ROOT / 'test/chip_tb.sv'
    out = fresh_directory(ROOT / 'build/physical/chip-check', args.tag)
    run = Commands(ROOT, out, default_timeout=600)
    cad = ROOT / 'build/tools/oss-cad-suite/bin'
    paths = [args.physical_report, args.comparison, invocation, stage, netlist,
             design / 'design.sv', vectors, bench, *models, Path(__file__).resolve(),
             ROOT / 'scripts/physical_checkpoint.py', ROOT / 'scripts/validation_run.py',
             ROOT / 'scripts/process_group.py', ROOT / 'tools/storage-macros.json',
             cad / 'iverilog', cad / 'vvp', ROOT / 'scripts/mapped_physical.py',
             ROOT / 'scripts/tiled_chip.py', *additional_inputs]
    hashes = {str(p.resolve()): sha(p) for p in paths}

    def simulate(file, label, reject=None):
        run([cad / 'iverilog', '-g2012', '-DFUNCTIONAL', '-s', 'chip_tb', '-o', out / (label + '.vvp'),
             file, bench, *models], label + '-compile')
        return run([cad / 'vvp', out / (label + '.vvp'), '+vectors=' + str(vectors.resolve())],
                   label, reject=reject)

    log = simulate(netlist, 'implemented')
    edges = comparison['coverage']['chip']['edges']
    if f'Passed {edges} independent whole-chip edges' not in log:
        raise RuntimeError('Incomplete implemented chip trace')
    text, count = re.subn(r'\bmodule\s+tt_um_pinwheel\b', 'module pinwheel_implemented', netlist.read_text())
    if count != 1:
        raise RuntimeError('Unrecognized implementation top')
    # A wrapper changes a public bit without depending on internal net names or
    # ANSI/non-ANSI declarations. It must compile and then fail the pin oracle.
    text += '''
module tt_um_pinwheel(input clk, ena, rst_n, input [7:0] ui_in, uio_in,
  output [7:0] uo_out, uio_out, uio_oe);
  wire [7:0] uncorrupted;
  pinwheel_implemented dut(.clk(clk), .ena(ena), .rst_n(rst_n), .ui_in(ui_in),
    .uio_in(uio_in), .uo_out(uncorrupted), .uio_out(uio_out), .uio_oe(uio_oe));
  assign uo_out = uncorrupted ^ 8'h01;
endmodule
'''
    mutant = out / 'corrupt-output.v'
    mutant.write_text(text)
    simulate(mutant, 'corrupt-output', reject='CHIP before edge')
    for path in paths:
        if sha(path) != hashes[str(path.resolve())]:
            raise RuntimeError('Input changed during check: ' + str(path))
    report = dict(schema=1, status='passed', physical_tag=physical['tag'], last_completed_step=physical['last_completed_step'],
        netlist_view=str(netlist.relative_to(ROOT)), edges=edges, mutants_rejected=1,
        input_sha256=hashes, commands=run.records, elapsed_seconds=round(time.monotonic()-started, 3),
        boundary=('Zero-delay external-pin simulation of a fresh export of the final reported ODB. '
                  if args.mapped_export else 'Zero-delay external-pin simulation of the explicitly identified NL view. '
                  'A flow state can inherit this view from an earlier stage; it is not necessarily '
                  'an export of the latest ODB/DEF. ') + 'No timing simulation, sequential equivalence, '
                 'power-connectivity proof, or physical closure claim.')
    (out / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(out / 'report.json')


if __name__ == '__main__':
    main()
