#!/usr/bin/env python3
"""Finite upload-to-pins gate through the exact Tiny Tapeout wrapper.

Reuse the accepted emitted frontend/controller only after checking their
retained receipt hashes and current implementation inputs. Independent serial
and SPI/JTAG/I2C peers observe only public pins. This does not rerun the core's
proof gates, qualify CDC/electrical timing, or establish physical readiness.
"""
import argparse
import importlib.util
import json
import os
from pathlib import Path
import select
import shutil
import time

from buffered_engine import BufferedBlock, BufferedInstruction, BufferedProgram
from buffered_hardware_synthesis import CAD
from buffered_peers import BufferedSPIPeer
from buffered_reactive_hardware import compact_spi
from buffered_sram_serial import BufferedSramSerialHost, BufferedSramSerialTransport
from buffered_sram_serial_rtl import BufferedSramSerialRTL
from pinwheel_buffers import TransferError
from validation_run import Commands, fresh_directory, sha


ROOT = Path(__file__).resolve().parents[1]
WRAPPER = ROOT / 'physical/tt_um_pinwheel_buffered.sv'
BRIDGE = ROOT / 'physical/tt_buffered_sram_serial_host_bridge.sv'
MACRO = 'RM_IHPSG13_1P_64x64_c2_bm_bist'
INTAKE_EXCLUSIONS = {
    'Pinwheel.lean': 'Aggregate library entry has additional proof imports; exporters import their implementation modules directly.',
    'scripts/check-foundation.py': 'Independent foundation-suite orchestration is not an emitted implementation or peer input.',
    'scripts/install-physical-pdk.py': 'Physical PDK download orchestration is not an emitted implementation or functional peer input.',
}


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def serial_gate():
    spec = importlib.util.spec_from_file_location('tt_serial_gate',
        ROOT / 'scripts/check-buffered-sram-serial.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


class TinyTapeoutRTL(BufferedSramSerialRTL):
    """The existing pin backend, plus clock-free TT reset/selection controls."""
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.ena = 1
        self.control_records = []

    def control(self, *, ena, rst_n):
        require(type(ena) is int and ena in (0, 1) and
            type(rst_n) is int and rst_n in (0, 1), 'Invalid Tiny Tapeout control')
        require(self.device is None, 'Detach the protocol peer before cancelling execution')
        require(not self._closed, 'Tiny Tapeout backend is closed')
        self.process.stdin.write(f'TT_CONTROL {ena} {rst_n}\n'.encode())
        self.process.stdin.flush()
        deadline = time.monotonic() + self.timeout_seconds
        while True:
            while b'\n' not in self.buffer:
                remaining = deadline - time.monotonic()
                if remaining <= 0 or not select.select([self.process.stdout], [], [], remaining)[0]:
                    raise TimeoutError('Tiny Tapeout control transition did not answer')
                data = os.read(self.process.stdout.fileno(), 65536)
                require(bool(data), 'Tiny Tapeout bridge exited: ' + '\n'.join(self.log))
                self.buffer.extend(data)
            raw, _, self.buffer = self.buffer.partition(b'\n')
            line = raw.decode(errors='replace')
            self.log.append(line)
            if line.startswith('TT_CONTROL '):
                values = list(map(int, line.split()[1:]))
                require(len(values) == 5 and values[:2] == [ena, rst_n] and
                    all(0 <= n < 256 for n in values[2:]), 'Malformed Tiny Tapeout control receipt')
                if not ena or not rst_n:
                    require(values[2:] == [0, 0, 0], 'Inactive Tiny Tapeout outputs are not zero')
                self.ena = ena
                record = dict(cycle=self.cycle, ena=ena, rst_n=rst_n,
                    uo_out=values[2], uio_out=values[3], uio_oe=values[4])
                self.control_records.append(record)
                return record


def stage_inputs(artifacts_root, out):
    manifest_path = ROOT / 'physical/experiments/buffered-sram-serial-results.json'
    accepted = json.loads(manifest_path.read_text())
    require(accepted['status'] == 'passed', 'Serial predecessor is not accepted')
    # Bind implementation and independent peer inputs, without claiming a fresh
    # proof run. New wrapper/check files are bound separately by this report.
    implementation = {name: digest for name, digest in accepted['frozen_source_sha256'].items()
        if (name.startswith(('Pinwheel/', 'scripts/')) and
            name not in INTAKE_EXCLUSIONS) or name in
            ('test/BufferedSramExport.lean',
             'test/BufferedSramSerialExport.lean', 'physical/buffered_sram_memory.sv',
             'physical/buffered_sram_serial_wrapper.sv')}
    for name, digest in implementation.items():
        require(sha(ROOT / name) == digest, 'Changed accepted implementation input: ' + name)
    serial_report_path = artifacts_root / accepted['reports']['hardware']['path']
    require(sha(serial_report_path) == accepted['reports']['hardware']['sha256'],
        'Changed retained serial predecessor report')
    serial_report = json.loads(serial_report_path.read_text())
    require(serial_report['status'] == 'passed' and not serial_report['smoke'],
        'Incomplete retained serial predecessor report')
    sram_manifest_path = ROOT / 'physical/experiments/buffered-sram-results.json'
    sram_manifest = json.loads(sram_manifest_path.read_text())
    sram_report_path = artifacts_root / sram_manifest['reports']['hardware']['path']
    require(sha(sram_report_path) == sram_manifest['reports']['hardware']['sha256'],
        'Changed retained controller predecessor report')
    source_paths = dict(
        frontend=serial_report_path.parent / 'frontend.sv',
        controller=sram_report_path.parent / 'core.sv',
        oracle=serial_report_path.parent / 'controller-oracle')
    for name, path in source_paths.items():
        key = str(path.relative_to(artifacts_root))
        expected = accepted.get('accepted_artifact_sha256', {}).get(key)
        if expected is None:
            expected = accepted.get('preserved_predecessor_sha256', {}).get(key)
        require(expected is not None and sha(path) == expected,
            'Unpinned retained emitted artifact: ' + name)
    lock = json.loads((ROOT / 'tools/storage-macros.json').read_text())
    for name in (MACRO + '.v', 'RM_IHPSG13_1P_core_behavioral_bm_bist.v'):
        path = artifacts_root / 'build/storage/macros' / name
        require(sha(path) == lock['files_sha256']['verilog/' + name],
            'Changed functional SRAM model: ' + name)
        source_paths[name] = path
    staged = out / 'inputs'
    staged.mkdir()
    inputs = {}
    for name, source in source_paths.items():
        target = staged / source.name
        shutil.copy2(source, target)
        inputs[name] = dict(path=str(target.relative_to(ROOT)), sha256=sha(target),
            retained_path=str(source))
    return dict(manifest_sha256=sha(manifest_path),
        serial_report_sha256=sha(serial_report_path),
        controller_report_sha256=sha(sram_report_path),
        implementation_source_sha256=implementation,
        source_intake_exclusions={name: dict(reason=reason,
            accepted_sha256=accepted['frozen_source_sha256'][name], current_sha256=sha(ROOT / name))
            for name, reason in INTAKE_EXCLUSIONS.items()},
        boundary='Hash-matched retained emitted RTL and current frozen implementation; no fresh proof run.'), inputs


def interface_cases(gate, cad, executable):
    with TinyTapeoutRTL(cad / 'vvp', executable, record_limit=0) as rtl:
        host = BufferedSramSerialHost(BufferedSramSerialTransport(rtl))
        host.initialize()
        loop = BufferedProgram((), schedule=BufferedBlock((
            BufferedInstruction('checked', finish=0, levels=7, enabled=7),)),
            idle_levels=7, idle_enabled=7,
            declared_tx_bits=0, declared_rx_bits=0, max_rx_bits=0)
        stale = host.load(loop)
        owner = stale.submit(tx=b'')
        require(rtl.snapshot.busy == 1 and rtl.snapshot.enabled == 7 and
            rtl.snapshot.levels == 7, 'Active all-output reset/selection witness missing')
        before = rtl.cycle
        deselected = rtl.control(ena=0, rst_n=1)
        require(rtl.cycle == before, 'Selection mask test advanced the core clock')
        rtl.tick(csn=1, sck=0, mosi=0)
        reselected = rtl.control(ena=1, rst_n=1)
        require(reselected['uo_out'] == reselected['uio_out'] == reselected['uio_oe'] == 0,
            'Clocked deselection failed to invalidate active execution')
        status = host.initialize()
        require(not status['valid'] and not status['busy'] and not status['retained'],
            'Reselect/reset left a committed program or owner')
        for operation in (lambda: stale.submit(tx=b''), owner.read):
            try:
                operation()
            except TransferError:
                pass
            else:
                raise RuntimeError('Reset left a stale local program or owner handle usable')
        loaded = host.load(compact_spi(1))
        peer = BufferedSPIPeer(b'\x96', b'\xa6', 4, 1)
        rtl.device = peer
        result = loaded.run(tx=b'\x96', timeout_polls=10)
        require(result.payload == b'\xa6', 'Fresh upload after reselect did not produce wire reply')
        peer_result = peer.check(result.raw_rx_bits)
        rtl.device = None
        rtl.tick(csn=1, sck=0, mosi=0)
        active = host.load(loop)
        active.submit(tx=b'')
        require(rtl.snapshot.busy and rtl.snapshot.enabled == 7,
            'Active reset witness missing')
        before = rtl.cycle
        reset = rtl.control(ena=1, rst_n=0)
        require(rtl.cycle == before, 'Reset mask test advanced the core clock')
        rtl.tick(csn=1, sck=0, mosi=0, initialize=1)
        released = rtl.control(ena=1, rst_n=1)
        require(released['uo_out'] == released['uio_out'] == released['uio_oe'] == 0,
            'Clocked reset failed to invalidate active execution')
        host.initialize()
        gate.raw_request(rtl, gate.encode_request(51, command=0))
        require(rtl.snapshot.ready, 'Held-receipt deselect witness missing')
        held = rtl.control(ena=0, rst_n=1)
        rtl.tick(csn=1, sck=0, mosi=0)
        rtl.control(ena=1, rst_n=1)
        after = host.initialize()
        require(not after['valid'] and not after['busy'] and not after['retained'] and
            not rtl.snapshot.ready, 'Reselect/reset did not clear held serial receipt')
        return dict(physical_edges=rtl.cycle, immediate_deselect_mask=deselected,
            reselect_after_invalidation=reselected, immediate_reset_mask=reset,
            reset_after_invalidation=released, held_receipt_deselect_mask=held,
            fresh_upload_after_reselect=peer_result,
            stale_handles_invalidated=True, controls=rtl.control_records,
            contract='Immediate output mask; synchronous invalidation; selection requires reset and fresh upload. SRAM retention is not assumed.')


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--tag', default='local')
    parser.add_argument('--artifacts-root', type=Path, default=ROOT)
    parser.add_argument('--cad-dir', type=Path, default=CAD)
    args = parser.parse_args()
    out = fresh_directory(ROOT / 'build/tt-buffered', args.tag)
    run = Commands(ROOT, out)
    started = time.monotonic()
    report = dict(schema='pinwheel-tt-buffered-digital-v1', status='running',
        top='tt_um_pinwheel_buffered', commands=run.records,
        source_sha256={str(path.relative_to(ROOT)): sha(path) for path in (
            WRAPPER, BRIDGE, Path(__file__),
            ROOT / 'physical/buffered_sram_serial_wrapper.sv',
            ROOT / 'physical/buffered_sram_memory.sv',
            *[ROOT / name for name in INTAKE_EXCLUSIONS])})
    try:
        report['predecessor'], report['inputs'] = stage_inputs(args.artifacts_root.resolve(), out)
        paths = {name: ROOT / value['path'] for name, value in report['inputs'].items()}
        gate = serial_gate()
        gate.CAD = args.cad_dir.resolve()
        gate.BufferedSramSerialRTL = TinyTapeoutRTL
        executable = out / 'tt-buffered.vvp'
        run([gate.CAD / 'iverilog', '-g2012', '-DFUNCTIONAL',
            '-s', 'tt_buffered_sram_serial_host_bridge', '-o', executable,
            paths['frontend'], paths['controller'],
            ROOT / 'physical/buffered_sram_serial_wrapper.sv',
            ROOT / 'physical/buffered_sram_memory.sv', WRAPPER, BRIDGE,
            paths[MACRO + '.v'], paths['RM_IHPSG13_1P_core_behavioral_bm_bist.v']],
            'tt-compile', timeout=120)
        records, annotations, report['wire_peers'] = gate.wire_cases(executable)
        report['wire_oracle'] = gate.trace_oracle(run, out, paths['oracle'], records,
            annotations, 'tt-wire')
        del records, annotations
        records, annotations, report['protocol_lifecycle'] = gate.protocol_cases(executable)
        report['protocol_oracle'] = gate.trace_oracle(run, out, paths['oracle'], records,
            annotations, 'tt-lifecycle')
        del records, annotations
        report['interface'] = interface_cases(gate, gate.CAD, executable)
        for name, digest in report['source_sha256'].items():
            require(sha(ROOT / name) == digest, 'Wrapper gate source changed during validation: ' + name)
        for name, value in report['inputs'].items():
            require(sha(ROOT / value['path']) == value['sha256'],
                'Staged wrapper gate input changed during validation: ' + name)
        report.update(status='passed', inputs_unchanged=True,
            elapsed_seconds=round(time.monotonic() - started, 3),
            artifact_sha256={str(path.relative_to(out)): sha(path)
                for path in sorted(out.rglob('*')) if path.is_file()},
            boundary='Finite exact-TT-port functional SRAM simulation, independently reconstructed serial receipts, '
                'independent SPI/JTAG/I2C peers, reset/deselect output masks and clocked invalidation. '
                'No new universal proof, asynchronous host timing, electrical pad/macro qualification, routed timing or package power claim.')
    except BaseException as error:
        report.update(status='failed', error=repr(error),
            elapsed_seconds=round(time.monotonic() - started, 3))
        raise
    finally:
        (out / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print('Tiny Tapeout buffered digital gate passed: ' + str(out / 'report.json'), flush=True)


if __name__ == '__main__':
    main()
