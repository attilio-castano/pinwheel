#!/usr/bin/env python3
"""Bounded TT boundary acceptance without the slower inherited trace oracle.

Uses the identical wrapper, compiler, 21 independent protocol peers and reset /
selection tests from check-tt-buffered.py. The complete oracle/lifecycle gate
remains a separate receipt; this smaller gate can admit a physical measurement.
"""
import argparse
import importlib.util
import json
from pathlib import Path
import subprocess
import time

from validation_run import Commands, fresh_directory, sha


ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--tag', default='local')
    parser.add_argument('--artifacts-root', type=Path, default=ROOT)
    parser.add_argument('--cad-dir', type=Path, default=ROOT / 'build/tools/oss-cad-suite/bin')
    parser.add_argument('--stronger-receipt', default='')
    args = parser.parse_args()
    spec = importlib.util.spec_from_file_location('tt_boundary_gate', ROOT / 'scripts/check-tt-buffered.py')
    common = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(common)
    out = fresh_directory(ROOT / 'build/tt-buffered', args.tag)
    run = Commands(ROOT, out)
    started = time.monotonic()
    sources = [common.WRAPPER, common.BRIDGE, Path(__file__),
        ROOT / 'scripts/check-tt-buffered.py',
        ROOT / 'physical/buffered_sram_serial_wrapper.sv',
        ROOT / 'physical/buffered_sram_memory.sv',
        *[ROOT / name for name in common.INTAKE_EXCLUSIONS]]
    report = dict(schema='pinwheel-tt-buffered-digital-v1', status='running',
        top='tt_um_pinwheel_buffered', commands=run.records,
        scope='Finite TT boundary acceptance; stronger inherited oracle/lifecycle checks are separate.',
        controller_oracle=dict(status='not_run', separate_receipt=args.stronger_receipt),
        source_sha256={str(path.relative_to(ROOT)): sha(path) for path in sources})
    try:
        report['predecessor'], report['inputs'] = common.stage_inputs(args.artifacts_root.resolve(), out)
        paths = {name: ROOT / value['path'] for name, value in report['inputs'].items()}
        gate = common.serial_gate()
        gate.CAD = args.cad_dir.resolve()
        gate.BufferedSramSerialRTL = common.TinyTapeoutRTL
        executable = out / 'tt-buffered.vvp'
        run([gate.CAD / 'iverilog', '-g2012', '-DFUNCTIONAL',
            '-s', 'tt_buffered_sram_serial_host_bridge', '-o', executable,
            paths['frontend'], paths['controller'],
            ROOT / 'physical/buffered_sram_serial_wrapper.sv',
            ROOT / 'physical/buffered_sram_memory.sv', common.WRAPPER, common.BRIDGE,
            paths[common.MACRO + '.v'], paths['RM_IHPSG13_1P_core_behavioral_bm_bist.v']],
            'tt-compile', timeout=120)
        records, annotations, report['wire_peers'] = gate.wire_cases(executable)
        del records, annotations
        report['interface'] = common.interface_cases(gate, gate.CAD, executable)
        report['parser_negative_controls'] = {}
        for name, line, reason in (
            ('numeric-long-line', '1 1 0 0 0000000000000000000000 0 0 255\n',
             'Malformed buffered SRAM serial pin input'),
            ('control-long-line', 'TT_CONTROL 0          1\n',
             'Malformed Tiny Tapeout control input'),
            ('numeric-extra-field', '1 1 0 0 0 0 0 255 1\n',
             'Malformed buffered SRAM serial pin input')):
            fixture = out / (name + '.input')
            fixture.write_text(line)
            argv = [str(gate.CAD / 'vvp'), str(executable)]
            result = subprocess.run(argv, input=line, text=True, capture_output=True,
                timeout=20, cwd=ROOT)
            log = out / (name + '.log')
            log.write_text(result.stdout + result.stderr)
            common.require(result.returncode != 0 and reason in log.read_text(),
                'Expected bridge parser rejection missing: ' + name)
            report['parser_negative_controls'][name] = dict(
                argv=argv, input=str(fixture.relative_to(ROOT)),
                log=str(log.relative_to(ROOT)), exit_code=result.returncode,
                expected_rejection=reason)
        for name, digest in {**report['source_sha256'],
                **report['predecessor']['implementation_source_sha256']}.items():
            common.require(sha(ROOT / name) == digest, 'Gate input changed during validation: ' + name)
        for name, value in report['inputs'].items():
            common.require(sha(ROOT / value['path']) == value['sha256'],
                'Staged wrapper gate input changed during validation: ' + name)
        report.update(status='passed', inputs_unchanged=True,
            elapsed_seconds=round(time.monotonic() - started, 3),
            artifact_sha256={str(path.relative_to(out)): sha(path)
                for path in sorted(out.rglob('*')) if path.is_file()},
            boundary='Finite exact-TT-port functional SRAM simulation with 21 independent SPI/JTAG/I2C peers, '
                'reset/deselect masks, clocked invalidation, reselect/reset/reupload, and bridge parser negatives. '
                'Inherited controller/lifecycle oracle is separate. No asynchronous host timing, electrical '
                'pad/macro qualification, routed timing, universal proof or package power claim.')
    except BaseException as error:
        report.update(status='failed', error=repr(error),
            elapsed_seconds=round(time.monotonic() - started, 3))
        raise
    finally:
        (out / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print('Tiny Tapeout buffered boundary gate passed: ' + str(out / 'report.json'), flush=True)


if __name__ == '__main__':
    main()
