#!/usr/bin/env python3
"""Bounded zero-delay upload-to-pins check of an explicitly selected mapped NL.

The unchanged exact-TT bridge and accepted independent SPI/JTAG/I2C peers are
reused. Only the mapped top's name is changed. Logical NLs have exact public TT
ports; supply-present NLs additionally have both VPWR/VGND tied by an adapter.
No RTL implementation, SDF, timing assertion, CAD flow or download is used.
"""
import argparse
import importlib.util
import json
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import time

import process_group
from validation_run import fresh_directory, sha


ROOT = Path(__file__).resolve().parents[1]
TOP = 'tt_um_pinwheel_buffered'
IMPLEMENTED = TOP + '_implemented'
MASTER = 'RM_IHPSG13_1P_64x64_c2_bm_bist'
PUBLIC = {'clk': ('input', ''), 'ena': ('input', ''), 'rst_n': ('input', ''),
          'ui_in': ('input', '[7:0]'), 'uio_in': ('input', '[7:0]'),
          'uo_out': ('output', '[7:0]'), 'uio_out': ('output', '[7:0]'),
          'uio_oe': ('output', '[7:0]')}
PORTS = {**PUBLIC, 'VPWR': ('inout', ''), 'VGND': ('inout', '')}
ADAPTER = '''module tt_um_pinwheel_buffered (
  input clk, ena, rst_n, input [7:0] ui_in, uio_in,
  output [7:0] uo_out, uio_out, uio_oe);
  supply1 VPWR;
  supply0 VGND;
  tt_um_pinwheel_buffered_implemented dut (
    .clk(clk), .ena(ena), .rst_n(rst_n), .ui_in(ui_in), .uio_in(uio_in),
    .uo_out(uo_out), .uio_out(uio_out), .uio_oe(uio_oe),
    .VPWR(VPWR), .VGND(VGND));
endmodule
'''
LOGICAL_ADAPTER = '''module tt_um_pinwheel_buffered (
  input clk, ena, rst_n, input [7:0] ui_in, uio_in,
  output [7:0] uo_out, uio_out, uio_oe);
  tt_um_pinwheel_buffered_implemented dut (
    .clk(clk), .ena(ena), .rst_n(rst_n), .ui_in(ui_in), .uio_in(uio_in),
    .uo_out(uo_out), .uio_out(uio_out), .uio_oe(uio_oe));
endmodule
'''
SCOPE = ('Finite exact-TT-port zero-delay functional simulation of the explicitly identified '
         'mapped NL, using vendor functional SRAM and standard-cell/UDP models. '
         'No SDF, routed timing, sequential equivalence, power-connectivity proof, '
         'electrical qualification or physical/submission closure claim. A checkpoint may '
         'inherit an earlier NL; matching the latest ODB requires a separate verified export.')


def require(condition, message):
    if not condition:
        raise ValueError(message)


def read(path):
    return json.loads(Path(path).read_text())


def write(path, value):
    Path(path).write_text(json.dumps(value, indent=2) + '\n')


def stripped(text):
    """Remove comments without moving token positions used for the one rename."""
    return re.sub(r'/\*.*?\*/|//[^\n]*',
                  lambda m: ''.join('\n' if c == '\n' else ' ' for c in m.group()),
                  text, flags=re.S)


def adapt_netlist(text):
    clean = stripped(text)
    modules = list(re.finditer(r'\bmodule\s+(\w+)', clean))
    require(len(modules) == 1 and modules[0][1] == TOP and
            len(re.findall(r'\bendmodule\b', clean)) == 1,
            'Expected one flattened mapped module named ' + TOP)
    require(not re.search(r'\b(always|initial|task|function|generate)\b', clean),
            'Behavioral or generated implementation is not a flattened mapped NL')
    require(not re.search(r'^\s*`(?!timescale\b|default_nettype\b)', clean, re.M),
            'Unexpected mapped-netlist compiler directive')
    header = re.search(r'\bmodule\s+' + TOP + r'\s*\((.*?)\)\s*;', clean, re.S)
    require(header is not None, 'Unrecognized mapped top header')
    names = [part.strip() for part in header[1].split(',')]
    require(len(names) == len(set(names)) and
            (set(names) == set(PUBLIC) or set(names) == set(PORTS)),
            'Unexpected mapped top ports; exact public TT ports with neither or both VPWR/VGND required')
    expected_ports = PUBLIC if set(names) == set(PUBLIC) else PORTS
    declarations = re.findall(r'\b(input|output|inout)\s+(?:(?:wire|reg|logic)\s+)?'
                              r'(\[\s*\d+\s*:\s*\d+\s*\])?\s*(\w+)\s*;', clean)
    declared = {name: (direction, re.sub(r'\s+', '', width))
                for direction, width, name in declarations}
    require(len(declarations) == len(expected_ports) and declared == expected_ports and
            len(re.findall(r'\b(input|output|inout)\b', clean)) == len(expected_ports),
            'Mapped port directions/widths or supply pins differ from the exact contract')
    require(not re.search(r'\.\s*(VDD|VSS)\s*\(', clean),
            'Powered-cell pNL is incompatible with the exact functional cell models')
    require(len(re.findall(r'^\s*' + MASTER + r'\s+', clean, re.M)) == 2 and
            all(re.search(r'\\engine\.memory\.storage' + str(n) + r'\s', clean)
                for n in (0, 1)), 'Expected the two buffered SRAM macro instances')
    start, end = modules[0].span(1)
    return text[:start] + IMPLEMENTED + text[end:], (LOGICAL_ADAPTER if expected_ports == PUBLIC else ADAPTER)


def verify_hashes(hashes):
    for name, digest in hashes.items():
        require(sha(Path(name)) == digest, 'Input changed during mapped check: ' + name)


def accepted_inputs(validation):
    gate = read(validation)
    require(gate.get('schema') == 'pinwheel-tt-buffered-digital-v1' and
            gate.get('status') == 'passed' and gate.get('inputs_unchanged'),
            'Passed source-bound exact-TT boundary validation is required')
    require(gate.get('wire_peers', {}).get('cases') == 21 and
            gate.get('interface', {}).get('stale_handles_invalidated'),
            'Complete independent boundary vectors and interface acceptance are required')
    hashes = {str(validation.resolve()): sha(validation)}
    for name, digest in {**gate['source_sha256'],
                         **gate['predecessor']['implementation_source_sha256']}.items():
        path = (ROOT / name).resolve()
        require(sha(path) == digest, 'Changed accepted boundary source: ' + name)
        hashes[str(path)] = digest
    return gate, hashes


def selected_state(args, hashes):
    result = {'origin': 'explicit_mapped_nl', 'latest_odb_match_established': False}
    state_database = None
    if args.get('state'):
        require(args.get('design'), '--state requires --design for container-path resolution')
        state_path, design = Path(args['state']), Path(args['design'])
        state = read(state_path)
        container_root = args.get('container_design_root', '/work/core')
        require(container_root in ('/work/core', '/work/recovery'),
                'Unsupported container design root')
        prefix = container_root + '/'
        require(isinstance(state.get('nl'), str) and state['nl'].startswith(prefix),
                'Unsupported checkpoint NL path')
        relative = Path(state['nl'][len(prefix):])
        require(not relative.is_absolute() and '..' not in relative.parts,
                'Invalid checkpoint NL path')
        selected = (design / relative).resolve()
        require(selected.is_relative_to(design.resolve()), 'Checkpoint NL is outside the prepared design')
        if not args.get('mapped_export'):
            require(selected == Path(args['netlist']).resolve(),
                    'Selected mapped NL differs from the provided checkpoint')
        hashes[str(state_path.resolve())] = sha(state_path)
        result.update(state_path=str(state_path.resolve()), state_sha256=sha(state_path),
                      nl_in_state=state['nl'], container_design_root=container_root)
        if state.get('odb') is not None:
            require(isinstance(state['odb'], str) and state['odb'].startswith(prefix),
                    'Unsupported checkpoint ODB path')
            odb_relative = Path(state['odb'][len(prefix):])
            require(not odb_relative.is_absolute() and '..' not in odb_relative.parts,
                    'Invalid checkpoint ODB path')
            state_database = (design / odb_relative).resolve()
            require(state_database.is_relative_to(design.resolve()),
                    'Checkpoint ODB is outside the prepared design')
    if args.get('mapped_export'):
        receipt_path = Path(args['mapped_export'])
        export = read(receipt_path)
        netlist = Path(args['netlist']).resolve()
        source = (ROOT / export['source_database']).resolve()
        require(export.get('status') == 'passed' and
                (ROOT / export['netlist']).resolve() == netlist and
                export['netlist_sha256'] == sha(netlist) and
                export['source_database_sha256'] == sha(source),
                'Failed, changed or unmatched fresh ODB export receipt')
        hashes[str(receipt_path.resolve())] = sha(receipt_path)
        hashes[str(source)] = sha(source)
        if state_database is not None:
            require(source == state_database, 'Exported database differs from the selected checkpoint ODB')
        result.update(origin='verified_fresh_odb_export',
                      latest_odb_match_established=state_database is not None,
                      exported_database_match_established=True,
                      export_receipt=str(receipt_path.resolve()),
                      source_database=str(source), source_database_sha256=sha(source))
    return result


def load_common():
    spec = importlib.util.spec_from_file_location('tt_mapped_boundary',
                                                ROOT / 'scripts/check-tt-buffered.py')
    common = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(common)
    return common


def command(argv, label, out, records, *, timeout=120, data=None, reject=None):
    """Children inherit the supervised worker group, including compiler children."""
    argv = list(map(str, argv))
    record = dict(label=label, argv=argv, timeout_seconds=timeout,
                  expected_failure=bool(reject))
    records.append(record)
    started = time.monotonic()
    try:
        result = subprocess.run(argv, input=data, capture_output=True, text=True,
                                cwd=ROOT, timeout=timeout)
        log = result.stdout + result.stderr
        (out / (label + '.log')).write_text(log)
        record.update(exit_code=result.returncode, seconds=round(time.monotonic()-started, 3))
        if reject:
            require(result.returncode != 0 and reject in log,
                    'Expected mapped bridge parser rejection missing: ' + label)
        else:
            require(result.returncode == 0, label + ' failed; see ' + str(out / (label + '.log')))
        print(label + ': passed', flush=True)
    except BaseException as error:
        record.update(error=type(error).__name__, seconds=round(time.monotonic()-started, 3))
        if isinstance(error, subprocess.TimeoutExpired):
            output = error.stdout or b''
            errors = error.stderr or b''
            (out / (label + '.log')).write_text(
                (output.decode(errors='replace') if isinstance(output, bytes) else output) +
                (errors.decode(errors='replace') if isinstance(errors, bytes) else errors))
        raise


def worker(plan):
    args, out = read(plan), Path(plan).parent
    report = read(out / 'report.json')
    started = time.monotonic()
    try:
        gate_receipt, hashes = accepted_inputs(Path(args['validation']))
        sources = [Path(__file__).resolve(), ROOT / 'scripts/process_group.py',
                   ROOT / 'scripts/validation_run.py', ROOT / 'tools/storage-macros.json',
                   ROOT / 'physical/experiments/buffered-sram-serial-results.json',
                   Path(args['cad_dir']) / 'iverilog', Path(args['cad_dir']) / 'vvp', Path(plan)]
        hashes.update({str(path.resolve()): sha(path) for path in sources})
        netlist = Path(args['netlist'])
        hashes[str(netlist.resolve())] = sha(netlist)
        report['selection'] = selected_state(args, hashes)
        report['netlist'] = dict(path=str(netlist.resolve()), sha256=sha(netlist))
        accepted = read(ROOT / 'physical/experiments/buffered-sram-serial-results.json')
        models = []
        for name in ('sg13cmos5l_stdcell.v', 'sg13cmos5l_udp.v'):
            path = Path(args['pdk_root']) / 'ihp-sg13cmos5l/libs.ref/sg13cmos5l_stdcell/verilog' / name
            expected = accepted['frozen_source_sha256']['build/buffered-hardware/pdk/' + name]
            require(sha(path) == expected, 'Changed accepted functional cell model: ' + name)
            models.append(path)
        lock = read(ROOT / 'tools/storage-macros.json')
        for name in (MASTER + '.v', 'RM_IHPSG13_1P_core_behavioral_bm_bist.v'):
            path = Path(args['macro_root']) / name
            require(sha(path) == lock['files_sha256']['verilog/' + name],
                    'Changed vendor functional SRAM model: ' + name)
            models.append(path)
        hashes.update({str(path.resolve()): sha(path) for path in models})
        staged = out / 'inputs'
        staged.mkdir()
        inputs = {}
        for path in [netlist, *models, ROOT / 'physical/tt_buffered_sram_serial_host_bridge.sv']:
            target = staged / path.name
            require(not target.exists(), 'Input filename collision: ' + path.name)
            shutil.copyfile(path, target)
            require(sha(target) == hashes[str(path.resolve())], 'Input changed while staging: ' + str(path))
            inputs[path.name] = dict(path=str(target.resolve()), sha256=sha(target),
                                     source=str(path.resolve()))
        mapped, adapter = adapt_netlist((staged / netlist.name).read_text())
        derived, adapter_path = out / 'mapped-renamed.v', out / 'tt-power-adapter.sv'
        derived.write_text(mapped)
        adapter_path.write_text(adapter)
        report.update(input_sha256=hashes, staged_inputs=inputs,
                      validation_receipt=str(Path(args['validation']).resolve()),
                      validation_receipt_sha256=sha(Path(args['validation'])),
                      transformation=dict(operation='Replace the sole module identifier only; '
                                          'adapter preserves named public TT connections.' +
                                          (' Both declared supplies are tied VPWR=1 and VGND=0.'
                                           if adapter == ADAPTER else ' Logical export declares no supply ports.'),
                                          port_presentation='public_plus_supplies' if adapter == ADAPTER else 'public_only',
                                          original_top=TOP, derived_top=IMPLEMENTED,
                                          renamed_netlist_sha256=sha(derived), adapter_sha256=sha(adapter_path)))
        derived_hashes = {str(derived): sha(derived), str(adapter_path): sha(adapter_path),
                          **{item['path']: item['sha256'] for item in inputs.values()}}
        write(out / 'report.json', report)
        executable = out / 'mapped.vvp'
        cad = Path(args['cad_dir'])
        command([cad / 'iverilog', '-g2012', '-DFUNCTIONAL',
                 '-s', 'tt_buffered_sram_serial_host_bridge', '-o', executable,
                 derived, adapter_path, staged / 'tt_buffered_sram_serial_host_bridge.sv',
                 *[staged / path.name for path in models]],
                'mapped-compile', out, report['commands'])
        write(out / 'report.json', report)
        if not args['compile_only']:
            common = load_common()
            gate = common.serial_gate()
            gate.CAD = cad
            gate.BufferedSramSerialRTL = common.TinyTapeoutRTL
            records, annotations, report['wire_peers'] = gate.wire_cases(executable)
            del records, annotations
            require(report['wire_peers'] == gate_receipt['wire_peers'],
                    'Mapped independent peer results differ from the accepted TT boundary')
            write(out / 'report.json', report)
            report['interface'] = common.interface_cases(gate, cad, executable)
            require(report['interface'] == gate_receipt['interface'],
                    'Mapped public interface results differ from accepted TT boundary')
            report['parser_negative_controls'] = {}
            for label, line, reason in (
                    ('numeric-long-line', '1 1 0 0 0000000000000000000000 0 0 255\n',
                     'Malformed buffered SRAM serial pin input'),
                    ('control-long-line', 'TT_CONTROL 0          1\n',
                     'Malformed Tiny Tapeout control input'),
                    ('numeric-extra-field', '1 1 0 0 0 0 0 255 1\n',
                     'Malformed buffered SRAM serial pin input')):
                (out / (label + '.input')).write_text(line)
                command([cad / 'vvp', executable], label, out, report['commands'],
                        timeout=20, data=line, reject=reason)
                report['parser_negative_controls'][label] = dict(expected_rejection=reason)
        verify_hashes({**hashes, **derived_hashes})
        report.update(status='compile_only_passed' if args['compile_only'] else 'passed',
                      inputs_unchanged=True, worker_elapsed_seconds=round(time.monotonic()-started, 3),
                      controller_oracle='Not rerun; the separate accepted RTL receipt covers inherited oracle/lifecycle.')
    except BaseException as error:
        report.update(status='failed', error=repr(error),
                      worker_elapsed_seconds=round(time.monotonic()-started, 3))
        raise
    finally:
        write(out / 'report.json', report)


def supervise(argv, out, timeout):
    """Bound the whole worker and clean its group on every exit, even normal exits."""
    process = subprocess.Popen(list(map(str, argv)), cwd=ROOT, stdout=subprocess.PIPE,
                               stderr=subprocess.PIPE, text=True, start_new_session=True)
    timed_out = False
    try:
        stdout, stderr = process.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        timed_out = True
        stdout, stderr, stopped = process_group._stop(process, 1)
    except BaseException as error:
        stdout, stderr, stopped = process_group._stop(process, 1)
        (out / 'worker.log').write_text(stdout + stderr)
        error.worker_supervision = dict(exit_code=process.returncode, timed_out=False,
                                       process_group=process.pid, process_group_stopped=stopped,
                                       timeout_seconds=timeout, cleanup_grace_seconds=1)
        raise
    else:
        # vvp and compiler descendants intentionally inherit this one group.
        # Reap any remaining owned descendants after a worker failure as well.
        stdout, stderr, stopped = process_group._stop(process, 1)
    (out / 'worker.log').write_text(stdout + stderr)
    return dict(exit_code=process.returncode, timed_out=timed_out,
                process_group=process.pid, process_group_stopped=stopped,
                timeout_seconds=timeout, cleanup_grace_seconds=1)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--netlist', type=Path, required=True)
    parser.add_argument('--validation', type=Path, required=True)
    parser.add_argument('--pdk-root', type=Path, default=ROOT / 'build/physical/pdk')
    parser.add_argument('--macro-root', type=Path, required=True)
    parser.add_argument('--cad-dir', type=Path, default=ROOT / 'build/tools/oss-cad-suite/bin')
    parser.add_argument('--state', type=Path)
    parser.add_argument('--design', type=Path)
    parser.add_argument('--container-design-root', choices=('/work/core', '/work/recovery'),
                        default='/work/core', help='Exact container prefix used by the selected checkpoint')
    parser.add_argument('--mapped-export', type=Path)
    parser.add_argument('--tag', required=True)
    parser.add_argument('--timeout-seconds', type=int, default=900)
    parser.add_argument('--compile-only', action='store_true', help='Adapter/model preflight; no upload-to-pins acceptance')
    args = parser.parse_args()
    if not 1 <= args.timeout_seconds <= 900:
        parser.error('--timeout-seconds must be between 1 and 900')
    if args.state and not args.design:
        parser.error('--state requires --design')
    started = time.monotonic()
    out = fresh_directory(ROOT / 'build/tt-buffered/netlist', args.tag)
    report = dict(schema='pinwheel-tt-buffered-netlist-v1', status='running',
                  scope=SCOPE, top=TOP, compile_only=args.compile_only,
                  inputs_unchanged=False, commands=[])
    write(out / 'report.json', report)
    plan = {name: str(value.resolve()) if isinstance(value, Path) else value
            for name, value in vars(args).items()}
    write(out / 'plan.json', plan)
    previous_term = signal.getsignal(signal.SIGTERM)

    def interrupt(signum, frame):
        # Another termination request must not interrupt owned-group cleanup.
        signal.signal(signal.SIGTERM, signal.SIG_IGN)
        raise KeyboardInterrupt('signal ' + str(signum))

    signal.signal(signal.SIGTERM, interrupt)
    try:
        budget = args.timeout_seconds - (time.monotonic()-started)
        require(budget > 0, 'Overall mapped-check budget exhausted before worker launch')
        result = supervise([sys.executable, Path(__file__).resolve(), '--worker', out / 'plan.json'],
                           out, budget)
        report = read(out / 'report.json')
        report['supervision'] = result
        if result['timed_out']:
            report.update(status='timed_out', inputs_unchanged=False,
                          error='Overall mapped-check execution budget exhausted')
        elif not result['process_group_stopped']:
            report.update(status='failed', error='Owned worker process-group termination is unconfirmed')
        elif result['exit_code'] != 0:
            report.update(status='failed', error=report.get('error', 'Mapped worker failed'))
    except BaseException as error:
        report = read(out / 'report.json')
        report.update(status='interrupted' if isinstance(error, KeyboardInterrupt) else 'failed',
                      error=repr(error), inputs_unchanged=False)
        if hasattr(error, 'worker_supervision'):
            report['supervision'] = error.worker_supervision
        raise
    finally:
        try:
            report['elapsed_seconds'] = round(time.monotonic()-started, 3)
            report['artifact_sha256'] = {str(path.relative_to(out)): sha(path)
                                        for path in sorted(out.rglob('*'))
                                        if path.is_file() and path.name != 'report.json'}
            write(out / 'report.json', report)
        finally:
            signal.signal(signal.SIGTERM, previous_term)
    print(str(out / 'report.json'), flush=True)
    return 0 if report['status'] in ('passed', 'compile_only_passed') else 1


if __name__ == '__main__':
    if len(sys.argv) == 3 and sys.argv[1] == '--worker':
        worker(Path(sys.argv[2]))
    else:
        sys.exit(main())
