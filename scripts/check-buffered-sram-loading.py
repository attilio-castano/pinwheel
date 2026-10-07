#!/usr/bin/env python3
"""Source-pinned initialized loading/typed execution gate; no CAD is needed.

The Lean witnesses begin with independent poisoned physical/reference banks.
Python contributes strict canonical SPI/JTAG/I2C image admission, rather than
an unproved universal source compiler claim. Retain each uniquely named run.
"""
import argparse
import hashlib
import json
import re
import shutil
import subprocess
import time
from pathlib import Path

from buffered_counted_hardware import compact_jtag, compact_spi
from buffered_engine import BufferedEngine, BufferedWireSimulation
from buffered_i2c import buffered_i2c_read, register_read_tx
from buffered_i2c_peer import BufferedI2CReadPeer
from buffered_peers import BufferedJTAGPeer, BufferedSPIPeer
from buffered_sram_hardware import BufferedSramHardwareImage, lower_sram
from pinwheel_buffers import TransferSlot

ROOT = Path(__file__).resolve().parents[1]
REPORT_PREFIX = 'BUFFERED_SRAM_LOADING_REPORT='


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def source_files():
    paths = [ROOT / name for name in (
        'Pinwheel.lean', 'lean-toolchain', 'lakefile.toml', 'lake-manifest.json',
        'test/BufferedSramLoading.lean', 'test/ProofAudit.lean',
        'scripts/check-buffered-sram-loading.py', 'scripts/buffered_sram_hardware.py',
        'scripts/buffered_shared_branches.py', 'scripts/buffered_reactive_hardware.py',
        'scripts/buffered_counted_hardware.py', 'scripts/buffered_hardware.py',
        'scripts/buffered_engine.py', 'scripts/buffered_i2c.py',
        'scripts/pinwheel_buffers.py', 'scripts/pad_io.py', 'scripts/buffered_i2c_peer.py',
        'scripts/buffered_peers.py', 'scripts/jtag_peers.py', 'scripts/pad_peers.py',
        'scripts/pinwheel_host.py')]
    return sorted(set(paths + list((ROOT / 'Pinwheel').rglob('*.lean'))))


class RecordedEngine(BufferedEngine):
    def __init__(self, *args, **kwargs):
        self.raw_inputs = []
        super().__init__(*args, **kwargs)

    def step(self, raw_inputs):
        self.raw_inputs.append(raw_inputs)
        super().step(raw_inputs)


def canonical_fixtures():
    spi_tx, spi_rx = b'\x96\xa5\x3c\xc3', b'\xa6\x9b\x42\xe1'
    jtag_tx, jtag_rx = 0x13cc3, 0x142e1
    programs = [
        ('spi', compact_spi(4, 4), spi_tx, spi_rx, BufferedSPIPeer(spi_tx, spi_rx, 4, 1)),
        ('jtag', compact_jtag(17, 4), jtag_tx.to_bytes(3, 'little'),
         jtag_rx.to_bytes(3, 'little'), BufferedJTAGPeer(jtag_tx, jtag_rx, 17, 4, 1)),
        ('i2c', buffered_i2c_read(1, 4, 32), register_read_tx(0x53, 0xa6), b'\x96',
         BufferedI2CReadPeer(0x53, 0xa6, b'\x96', phase_cycles=4))]
    fixtures = []
    images = []
    rejected = []
    wire_reports = []
    for name, program, tx, rx, peer in programs:
        lowered = lower_sram(program)
        image = BufferedSramHardwareImage.from_bytes(lowered.to_bytes())
        if image.to_bytes() != lowered.to_bytes():
            raise RuntimeError('Canonical source/image round trip changed bytes')
        for field in ('words', 'controls', 'branch_indices', 'branch_table'):
            values = dict(words=image.words, controls=image.controls,
                          branch_indices=image.branch_indices, branch_table=image.branch_table)
            mutant = list(values[field])
            mutant[0] ^= 1
            values[field] = tuple(mutant)
            try:
                BufferedSramHardwareImage(**values, program_key=image.program_key, source=program)
            except ValueError:
                rejected.append(dict(protocol=name, field=field, rejected=True))
            else:
                raise RuntimeError(f'Tampered canonical {name} {field} was admitted')
        tx_bits = image.encode_tx(tx)
        slot = TransferSlot(tx_capacity_bits=32, rx_capacity_bits=32)
        identity = slot.begin(program.key, tx_bits, image.rx_reservation_bits)
        engine = RecordedEngine(slot, identity, program,
                                initial_first_sample=3, initial_second_sample=3)
        wire = BufferedWireSimulation(engine, peer)
        completion = wire.run(3000)
        peer_report = (peer.check(completion.rx_bits, timeout=False) if name == 'i2c'
                       else peer.check(completion.rx_bits))
        if (completion.outcome != 'complete' or image.decode_rx(completion.rx_bits) != rx
                or completion.tx_consumed_bits != image.tx_bits):
            raise RuntimeError(f'{name}: source/independent wire peer capture differs')
        raw_rx = sum(int(bit) << index for index, bit in enumerate(completion.rx_bits))
        wire_reports.append(dict(protocol=name, complete=True, execution_edges=wire.cycle,
            rx_bits=len(completion.rx_bits), tx_consumed_bits=completion.tx_consumed_bits,
            peer=peer_report))
        fixtures.append(dict(name=name, words=list(image.words), controls=list(image.controls),
            branch_indices=list(image.branch_indices), branch_table=list(image.branch_table),
            virtual_span=image.virtual_span, idle_levels=image.idle_levels,
            idle_enabled=image.idle_enabled, tx_bits=image.tx_bits,
            rx_reservation_bits=image.rx_reservation_bits, max_edges=3000,
            tx_data=sum(int(bit) << index for index, bit in enumerate(tx_bits)),
            raw_inputs=engine.raw_inputs, expected_phase=5, expected_rx_data=raw_rx,
            expected_rx_length=len(completion.rx_bits),
            expected_tx_consumed=completion.tx_consumed_bits))
        images.append((name, image))
    return fixtures, images, rejected, wire_reports


def parse_stats(output):
    matches = [line[len(REPORT_PREFIX):] for line in output.splitlines()
               if line.startswith(REPORT_PREFIX)]
    if len(matches) != 1:
        raise RuntimeError('Missing unique initialized loading witness report')
    stats = json.loads(matches[0])
    if stats['cases'] != 15 or stats['negativeWitnesses'] != 15:
        raise RuntimeError('Expected six directed and nine source-bound independently seeded cases')
    if stats['negativePremiseWitnesses'] != 3:
        raise RuntimeError('Expected initialized coverage and response premise counterexamples')
    if stats['sourceResultChecks'] != 9:
        raise RuntimeError('Expected nine successful source/independent peer retained-result checks')
    if any(stats[field] <= 0 for field in ('edges', 'coreChecks', 'outputChecks',
                                         'knownRowChecks', 'dictionaryChecks', 'entryChecks',
                                         'candidateChecks', 'residentPremiseChecks', 'ordinaryBoundaries')):
        raise RuntimeError('Initialized loader/execution checks were omitted')
    return stats


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--tag', default='local')
    args = parser.parse_args()
    if not re.fullmatch(r'[A-Za-z0-9_-]+', args.tag):
        parser.error('Use letters, numbers, hyphens or underscores in tags')
    if shutil.which('lake') is None:
        raise RuntimeError('Pinned Lean toolchain and lake are required')
    out = ROOT / 'build' / 'buffered-sram-loading' / args.tag
    if out.exists():
        raise RuntimeError('Choose a fresh tag to retain earlier evidence')
    sources = source_files()
    hashes = {str(p.relative_to(ROOT)): sha(p) for p in sources}
    out.mkdir(parents=True)
    started = time.monotonic()
    commands = []

    def run(command, label):
        result = subprocess.run(list(map(str, command)), cwd=ROOT,
                                capture_output=True, text=True, timeout=1200)
        log = result.stdout + result.stderr
        (out / f'{label}.log').write_text(log)
        commands.append(dict(label=label, command=list(map(str, command)), exit_code=result.returncode))
        if result.returncode:
            raise RuntimeError(f'{label} failed:\n{log}')
        print(f'{label}: {log.strip()[-1200:]}', flush=True)
        return log

    report = dict(schema='pinwheel-buffered-sram-loading-gate-v1', passed=False,
        source_sha256=hashes, commands=commands,
        boundary='Initialized actual typed SRAM controller/macro loader and binary resident execution; '
                 'finite canonical source-image witnesses. Does not prove universal source lowering, '
                 'universal emission/native evaluation, serial command-to-core refinement, '
                 'physical SRAM/CDC/address timing or chip qualification.')
    try:
        version = run(['lake', 'env', 'lean', '--version'], 'version').strip()
        expected = (ROOT / 'lean-toolchain').read_text().strip().split(':v')[-1]
        if not re.search(r'Lean \(version ' + re.escape(expected) + r'(?:,|\s)', version):
            raise RuntimeError(f'Expected Lean {expected}, got {version}')
        report['lean'] = version
        fixtures, images, rejected, wire_reports = canonical_fixtures()
        fixture_path = out / 'fixtures.json'
        fixture_path.write_text(json.dumps(dict(schema='pinwheel-buffered-sram-loading-fixtures-v1',
            fixtures=fixtures), indent=2) + '\n')
        for name, image in images:
            (out / f'{name}-source-image.json').write_bytes(image.to_bytes())
        report['source_images'] = [dict(protocol=name, image_key=image.key,
            program_key=image.program_key, physical_rows=len(image.words),
            virtual_span=image.virtual_span, distinct_branches=image.distinct_branches)
            for name, image in images]
        report['source_admission_mutations'] = rejected
        report['source_wire_witnesses'] = wire_reports
        run(['lake', 'build', 'Pinwheel:static'], 'build-static')
        audit = run(['lake', 'env', 'lean', '-DwarningAsError=true', 'test/ProofAudit.lean'], 'axiom-audit')
        if 'standard axioms only' not in audit:
            raise RuntimeError('Whole-library standard axiom audit did not report success')
        interpreted = run(['lake', 'env', 'lean', '-DwarningAsError=true', '--run',
            'test/BufferedSramLoading.lean', fixture_path], 'interpreted')
        stats = parse_stats(interpreted)
        library = out / 'libpinwheel_Pinwheel.a'
        library.write_bytes((ROOT / '.lake/build/lib/libpinwheel_Pinwheel.a').read_bytes())
        c = out / 'loading.c'
        executable = out / 'loading'
        run(['lake', 'env', 'lean', '-DwarningAsError=true', '-c', c,
             'test/BufferedSramLoading.lean'], 'native-c')
        run(['lake', 'env', 'leanc', '-O3', '-o', executable, c, library], 'native-link')
        native = run([executable, fixture_path], 'native')
        if parse_stats(native) != stats:
            raise RuntimeError('Native/interpreted initialized loading checks differ')
        report['witnesses'] = stats
        report['native_interpreted_same_stats'] = True
        for path in sources:
            if sha(path) != hashes[str(path.relative_to(ROOT))]:
                raise RuntimeError(f'Source changed during validation: {path}')
        report['inputs_unchanged'] = True
        report['passed'] = True
    finally:
        report['elapsed_seconds'] = round(time.monotonic()-started, 3)
        report['artifact_sha256'] = {str(p.relative_to(ROOT)): sha(p)
            for p in sorted(out.rglob('*')) if p.is_file() and p.name != 'report.json'}
        (out / 'report.json').write_text(json.dumps(report, indent=2)+'\n')
    print(f'Initialized SRAM loading gate passed: {out / "report.json"}', flush=True)


if __name__ == '__main__':
    main()
