#!/usr/bin/env python3
"""Check the opt-in upload lookup isolation against the retained paired RTL.

The Lean expression theorem, arbitrary-state RTL equivalence, mapped-cell
equivalence, pin traces and structural path checks are separate evidence.
Every run is create-only. No placement, routing or timing exceptions are used.
"""
import argparse
from copy import deepcopy
from datetime import datetime, timezone
import json
from pathlib import Path
import time

from paired_mapping import MACRO, cut, mapping, timing, write
from paired_vectors import core_vectors, chip_vectors
from physical_target import state_and_paths, path_expectations
from tiled_chip import state_cut
from validation_run import Commands, fresh_directory, sha

ROOT = Path(__file__).resolve().parents[1]
CAD = ROOT / 'build/tools/oss-cad-suite/bin'


def core_cut(module, description):
    """Normalize only the same six dead reserved bits admitted by paired cut."""
    view = deepcopy(module)
    live = [b for c in view['cells'].values() for bs in c['connections'].values() for b in bs]
    live += [b for p in view['ports'].values() for b in p['bits']]
    if 'x' in live or 'z' in live:
        raise ValueError('Unknown value in live core logic')
    bits = live + [b for n in view['netnames'].values() for b in n['bits']]
    fresh = max(b for b in bits if type(b) is int) + 1
    unused = []
    trimmed = []
    for slot in description['registers']:
        bs = view['netnames'][slot['name']]['bits']
        if len(bs) != slot['width']:
            if slot['name'] not in ['r_boot_b0', 'r_boot_b1', 'r_current'] or len(bs) != 30 or slot['width'] != 32:
                raise ValueError('Unexpected trimmed core state')
            # Yosys removes these unused high bits from core netnames entirely.
            # Fresh, disconnected identities let the shared cut record them as
            # pruned state; no live wire or next-state value is discarded.
            trimmed.extend([[slot['name'], k] for k in [30, 31]])
            bs.extend([fresh, fresh + 1])
            fresh += 2
        for k, b in enumerate(bs):
            if b == 'x':
                if slot['name'] not in ['r_boot_b0', 'r_boot_b1', 'r_current'] or k not in [30, 31]:
                    raise ValueError('Unexpected unknown core state coordinate')
                unused.append([slot['name'], k])
                bs[k] = fresh
                fresh += 1
    result, projection = state_cut(view, description, True)
    projection['unused_reserved_x_coordinates'] = unused
    projection['trimmed_reserved_coordinates'] = trimmed
    return result, projection


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--tag', required=True)
    parser.add_argument('--baseline-root', type=Path, required=True,
                        help='Checkout containing the frozen paired-controller receipt')
    parser.add_argument('--cell-model-dir', type=Path, required=True)
    args = parser.parse_args()
    out = fresh_directory(ROOT / 'build/validation', args.tag)
    run = Commands(ROOT, out, default_timeout=120)
    started = time.monotonic()
    report = dict(schema=1, status='running', date=datetime.now(timezone.utc).isoformat(),
                  commands=run.records, placement_or_routing=False, per_command_seconds=120)
    circt = ROOT / 'build/tools/firtool-1.159.0/bin/circt-opt'
    views = ROOT / 'build/storage/macros'
    models = [views / (MACRO + '.v'), views / 'RM_IHPSG13_1P_core_behavioral_bm_bist.v']
    cell_models = [args.cell_model_dir / n for n in ['sg13cmos5l_stdcell.v', 'sg13cmos5l_udp.v']]
    try:
        selection = ROOT / 'physical/experiments/paired-controller-results.json'
        selected = json.loads(selection.read_text())
        baseline_report = args.baseline_root / selected['report']
        if sha(baseline_report) != selected['report_sha256']:
            raise ValueError('Changed retained controller receipt')
        baseline = json.loads(baseline_report.read_text())
        if baseline['status'] != 'passed' or not baseline['inputs_unchanged']:
            raise ValueError('Retained controller did not pass')
        for model in cell_models:
            expected = {d for n, d in baseline['source_sha256'].items() if Path(n).name == model.name}
            if expected != {sha(model)}:
                raise ValueError('Cell model differs from retained validation: ' + model.name)
        sources = [ROOT / 'Pinwheel.lean', *sorted((ROOT / 'Pinwheel').rglob('*.lean')),
                   *sorted((ROOT / 'scripts').glob('*.py')),
                   *[ROOT / p for p in ['test/PairedChipEmit.lean', 'test/PairedValidationEmit.lean',
                       'test/paired_chip.sv', 'test/sram_core_tb.sv', 'test/chip_tb.sv',
                       'lean-toolchain', 'lakefile.toml', 'tools/storage-macros.json',
                       'tools/technology-library.json', 'tools/hardware-toolchain.json',
                       'tools/physical-toolchain.json', 'physical/targets/paired.json',
                       'build/loader/images.txt']],
                   selection, baseline_report, circt, *cell_models,
                   *[CAD / n for n in ['yosys', 'yosys-abc', 'iverilog', 'vvp']]]
        lock = json.loads((ROOT / 'tools/storage-macros.json').read_text())
        for rel, digest in lock['files_sha256'].items():
            path = views / Path(rel).name
            if sha(path) != digest:
                raise ValueError('Changed pinned macro view: ' + rel)
            sources.append(path)
        sources += list((ROOT / 'build/tools/ihp-cmos5l').glob('*.lib'))
        for name in ['core.sv', 'chip.sv', 'assembly.json']:
            p = baseline_report.parent / name
            key = str(p.relative_to(args.baseline_root))
            if sha(p) != baseline['artifact_sha256'][key]:
                raise ValueError('Changed baseline artifact: ' + name)
            sources.append(p)
        report['baseline_receipt'] = dict(path=str(baseline_report), sha256=sha(baseline_report))
        report['source_sha256'] = {str(p.relative_to(ROOT)) if p.is_relative_to(ROOT) else str(p): sha(p)
                                   for p in sources}
        write(out / 'inputs.json', report['source_sha256'])
        run(['lake', 'build', 'Pinwheel.Hardware.Storage.PairedValidation'], 'lean-build')
        for tag, emitter, folder in [('baseline', 'PairedChipEmit', out / 'baseline'),
                                     ('isolated', 'PairedValidationEmit', out)]:
            log = run(['lake', 'env', 'lean', '-DwarningAsError=true', '--run',
                       ROOT / ('test/' + emitter + '.lean'), folder], tag + '-emit')
            if 'standard axioms only' not in log:
                raise ValueError('Missing emitter axiom audit')
            for kind in ['core', 'chip']:
                rtl = run([circt, folder / (kind + '.mlir'), '--canonicalize', '--lower-seq-to-sv',
                           '--lower-hw-to-sv', '--hw-legalize-modules', '--export-verilog', '-o', '/dev/null'],
                          tag + '-' + kind + '-export')
                (folder / (kind + '.sv')).write_text(rtl)
        for name in ['core.sv', 'chip.sv', 'assembly.json']:
            if sha(out / 'baseline' / name) != sha(baseline_report.parent / name):
                raise ValueError('Fresh baseline differs from frozen RTL/assembly: ' + name)
        emitted = json.loads((out / 'assembly.json').read_text())
        if emitted != json.loads((out / 'baseline/assembly.json').read_text()):
            raise ValueError('Changed state or interface declaration')
        report['declared_bits'] = sum(p['width'] for p in emitted['chip']['registers'])
        text = (ROOT / 'test/PairedValidationEmit.lean').read_text()
        mutant = text.replace('\n#audit_paired_controller\n',
            '\nnamespace Pinwheel.Hardware.Storage.PairedValidation\naxiom forbidden : False\n'
            'end Pinwheel.Hardware.Storage.PairedValidation\n#audit_paired_controller\n')
        if mutant == text:
            raise ValueError('Missing axiom mutation anchor')
        (out / 'AuditNegative.lean').write_text(mutant)
        run(['lake', 'env', 'lean', out / 'AuditNegative.lean'], 'axiom-negative',
            reject='Unapproved paired controller axioms')

        def yosys(label, lines, reject=None):
            script = out / (label + '.ys')
            script.write_text('\n'.join(lines) + '\n')
            return run([CAD / 'yosys', '-Q', '-T', '-s', script], label, reject=reject)

        report['cross_implementation'] = {}
        for kind in ['core', 'chip']:
            cuts, projections = {}, {}
            top = 'pinwheel_paired_core_controller' if kind == 'core' else 'tt_um_pinwheel'
            for role, folder in [('reference', out / 'baseline'), ('candidate', out)]:
                saved = out / (kind + '-' + role + '.json')
                wrapper = '' if kind == 'core' else str(ROOT / 'test/paired_chip.sv')
                yosys(kind + '-' + role, [f'read_liberty -lib {views}/{MACRO}_typ_1p20V_25C.lib',
                    f'read_verilog -sv {folder}/{kind}.sv {wrapper}',
                    f'synth -top {top} -flatten -noabc', 'dffunmap', 'clean', 'check -assert',
                    f'write_json {saved}'])
                module = json.loads(saved.read_text())['modules'][top]
                cuts[role], projections[role] = (core_cut if kind == 'core' else cut)(module, emitted[kind])
                write(out / (kind + '-' + role + '-cut.json'), dict(modules={role: cuts[role]}))
            if projections['reference'] != projections['candidate']:
                raise ValueError('Changed state projection')

            def prove(candidate, label, reject=None):
                log = yosys(label, [f'read_json {out}/{kind}-reference-cut.json', f'read_json {candidate}',
                    'miter -equiv -flatten -make_outputs reference candidate miter',
                    'hierarchy -check -top miter', 'flatten', 'opt -full',
                    'sat -verify -prove trigger 0 -set-def-inputs miter'], reject)
                if not reject and 'SAT proof finished - no model found: SUCCESS!' not in log:
                    raise ValueError('Incomplete cross-implementation proof')
            prove(out / (kind + '-candidate-cut.json'), kind + '-equivalence')
            if kind == 'chip':
                mutant = deepcopy(cuts['candidate'])
                old = mutant['ports']['uo_out']['bits'][4]
                fresh = 1 + max(b for n in mutant['netnames'].values() for b in n['bits'] if type(b) is int)
                fresh = max(fresh, 1 + max(b for c in mutant['cells'].values()
                    for bs in c['connections'].values() for b in bs if type(b) is int))
                mutant['cells']['negative_rejection'] = dict(type='$_NOT_', hide_name=0, parameters={},
                    attributes={}, port_directions={'A': 'input', 'Y': 'output'}, connections={'A': [old], 'Y': [fresh]})
                mutant['ports']['uo_out']['bits'][4] = fresh
                mutant['netnames']['uo_out']['bits'] = list(mutant['ports']['uo_out']['bits'])
                write(out / 'rejection-negative.json', dict(modules=dict(candidate=mutant)))
                prove(out / 'rejection-negative.json', 'rejection-negative', 'proof did fail')
            report['cross_implementation'][kind] = dict(status='equivalent', state_projection=projections['candidate'],
                scope='All outputs and next-state bits for arbitrary defined inputs, registers and SRAM response pins')

        report['coverage'] = dict(core=core_vectors(out), chip=chip_vectors(out))
        (out / 'core-tb.sv').write_text((ROOT / 'test/sram_core_tb.sv').read_text().replace(
            'pinwheel_sram_core dut', 'pinwheel_paired_core dut'))
        for kind in ['core', 'chip']:
            tb = out / 'core-tb.sv' if kind == 'core' else ROOT / 'test/chip_tb.sv'
            top = 'sram_core_tb' if kind == 'core' else 'chip_tb'
            run([CAD / 'iverilog', '-g2012', '-DFUNCTIONAL', '-s', top, '-o', out / (kind + '.vvp'),
                 out / (kind + '.sv'), ROOT / 'test/paired_chip.sv', tb, *models], kind + '-compile')
            vector = out / ('core-vectors.txt' if kind == 'core' else 'vectors.txt')
            log = run([CAD / 'vvp', out / (kind + '.vvp'), '+vectors=' + str(vector)], kind + '-oracle')
            expected = f'Passed {report["coverage"][kind]["edges"]} independent ' + ('SRAM core' if kind == 'core' else 'whole-chip') + ' edges'
            if expected not in log:
                raise ValueError('Incomplete independent pin oracle')
        mapping(run, out, emitted['chip'], report)
        report['path_expectations'] = {}
        target = json.loads((ROOT / 'physical/targets/paired.json').read_text())
        for corner in ['typical', 'slow']:
            module = json.loads((out / corner / 'readback.json').read_text())['modules']['tt_um_pinwheel']
            _, roles = state_and_paths(module, emitted['chip'], target)
            paths = path_expectations(module, roles)
            report['path_expectations'][corner] = paths
            if paths['rejection_status']:
                raise ValueError('Synthesis retained an SRAM-to-rejection path')
        run([CAD / 'iverilog', '-g2012', '-DFUNCTIONAL', '-s', 'chip_tb', '-o', out / 'mapped.vvp',
             out / 'typical/design.v', ROOT / 'test/chip_tb.sv', *models, *cell_models], 'mapped-compile')
        log = run([CAD / 'vvp', out / 'mapped.vvp', '+vectors=' + str(out / 'vectors.txt')], 'mapped-oracle')
        if f'Passed {report["coverage"]["chip"]["edges"]} independent whole-chip edges' not in log:
            raise ValueError('Incomplete mapped pin replay')
        timing(run, out, emitted['chip'], report)
        report['comparison'] = {}
        for corner, v in report['variants'].items():
            area = v['metrics']['total_cell_and_macro_area_um2']
            prior = baseline['variants'][corner]['metrics']['total_cell_and_macro_area_um2']
            report['comparison'][corner] = dict(mapped_area_delta_um2=round(area-prior, 4),
                mapped_area_delta_percent=round(100*(area/prior-1), 4),
                signal_electrical_pass=not any(v['cell_timing']['electrical_violations'].values()),
                setup_pass=v['cell_timing']['setup_slack_ns'] >= 0, hold_pass=v['cell_timing']['hold_slack_ns'] >= 0)
        report['status'] = 'passed'
    except BaseException as error:
        report.update(status='failed', error=f'{type(error).__name__}: {error}')
        raise
    finally:
        report['seconds'] = round(time.monotonic()-started, 3)
        report['inputs_unchanged'] = all(sha(ROOT / n if not Path(n).is_absolute() else n) == d
                                       for n, d in report.get('source_sha256', {}).items())
        if not report['inputs_unchanged']:
            report['status'] = 'failed'
        report['artifact_sha256'] = {str(p.relative_to(ROOT)): sha(p) for p in sorted(out.rglob('*')) if p.is_file()}
        report['boundary'] = ['Lean theorem concerns the changed expression under upstream binding equations.',
            'Yosys SAT independently checks complete emitted core and package next-state/output equivalence.',
            'No complete Lean compiler or paired-controller-to-E64 refinement theorem is asserted.',
            'Functional pin replay uses zero-delay models; cell STA has no placed wires or clock tree.',
            'Structural removal of a path is not routed timing closure or physical qualification.']
        with (out / 'report.json').open('x') as stream:
            stream.write(json.dumps(report, indent=2) + '\n')
        print(json.dumps({k: report.get(k) for k in ['status', 'seconds', 'comparison', 'error']}), flush=True)
    if report['status'] != 'passed':
        raise RuntimeError('Validation-isolation checks failed')


if __name__ == '__main__':
    main()
