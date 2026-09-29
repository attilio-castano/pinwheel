#!/usr/bin/env python3
"""Check bounded SPI transactions and existing protocols on resolved package pads."""
import argparse
from dataclasses import asdict, replace
import hashlib
import json
from pathlib import Path
import time

from host_demo import compiler_images, demonstrate
from pad_io import PAD_MAP
from pad_peers import SPIPeer, spi_result_bytes, require
from pinwheel_host import Host, PAIRED_FORMAT
from pinwheel_sim import Simulation
from validation_run import Commands, fresh_directory, sha

ROOT = Path(__file__).resolve().parents[1]


class SPIReplyMismatch(RuntimeError):
    def __init__(self, case, expected):
        self.case, self.expected = case, list(expected)
        super().__init__(case['name'] + ': SPI resolved-wire reply mismatch: ' +
                         repr(case['decoded_wire_bytes']))


def collapse_capture_slots(program):
    """A canonical but wrong program: every enabled capture overwrites slot zero."""
    words, changed = [], 0
    for word in program.words:
        for offset in (29, 35):
            if word & (1 << offset):
                changed += int(bool(word & (15 << (offset + 2))))
                word &= ~(15 << (offset + 2))
        words.append(word)
    require(changed > 0, 'SPI corruption fixture has no nonzero capture slots')
    return replace(program, words=tuple(words))


def payload_bytes(payload, count):
    if type(payload) is not int or not 0 <= payload < 1 << (8 * count):
        raise ValueError('SPI fixture payload exceeds its declared byte count')
    return tuple(payload.to_bytes(count, 'big'))


def fixture_metadata(data, images):
    entries = json.loads(data)
    if not isinstance(entries, list) or not entries:
        raise ValueError('SPI fixture metadata must be a nonempty list')
    fields = {'name', 'mode', 'byte_count', 'half_cycles', 'tx_payload', 'rx_payload',
              'sample_slots', 'transfer_cycles'}
    names = set()
    for item in entries:
        if not isinstance(item, dict) or set(item) != fields or not isinstance(item['name'], str):
            raise ValueError('Unsupported SPI fixture metadata schema')
        if any(type(item[key]) is not int for key in fields - {'name'}):
            raise ValueError('SPI fixture fields must be integers')
        count, half = item['byte_count'], item['half_cycles']
        if count not in (1, 2) or item['mode'] not in range(4) or not 1 <= half <= 256:
            raise ValueError('SPI fixture mode/count/period out of range')
        if item['sample_slots'] != 8 * count or item['transfer_cycles'] != (16 * count + 1) * half:
            raise ValueError('SPI fixture capture/timing metadata inconsistent')
        payload_bytes(item['tx_payload'], count)
        payload_bytes(item['rx_payload'], count)
        if item['name'] in names:
            raise ValueError('Duplicate SPI fixture name')
        names.add(item['name'])
    if names != set(images):
        raise ValueError('SPI fixture image/metadata names differ')
    return entries


def run_spi_cases(simulation, images, metadata, out, certify, *, tco=0):
    host = Host(simulation, image_format=PAIRED_FORMAT)
    host.reset()
    cases = []
    for item in metadata:
        name, count = item['name'], item['byte_count']
        program = replace(images[name], image_format=PAIRED_FORMAT)
        simulation.device = None
        certify(name, program)
        program.write(out / (name + '.json'))
        host.upload(program)
        tx = payload_bytes(item['tx_payload'], count)
        rx = payload_bytes(item['rx_payload'], count)
        peer = SPIPeer(item['mode'], tx, rx, item['half_cycles'], tco=tco)
        simulation.device = peer
        host.start()
        result = host.read_result(timeout_cycles=item['transfer_cycles'] + 1024, consume=False)
        decoded = spi_result_bytes(result.samples, count)
        require(result.outcome == 5 and not result.overrun and not result.rejected,
                name + ': unexpected result outcome/flags: ' + repr(result))
        retained = host.read_result(timeout_cycles=0, consume=False)
        require(retained == result, name + ': retained result changed')
        wire = peer.check()
        host.consume()
        require(not host.result_status() & 1, name + ': consumption did not release result')
        case = dict(name=name, result=asdict(result), decoded_wire_bytes=list(decoded),
                    retained_twice=True, consumed=True, **wire)
        simulation.device = None
        if decoded != rx:
            raise SPIReplyMismatch(case, rx)
        cases.append(case)
    return dict(cases=cases, edges=host.edges, frames=host.frames)


def reset_active_spi(simulation, images, metadata, out, certify):
    item = next(entry for entry in metadata if entry['name'] == 'spi-mode0-2bytes')
    source = replace(images[item['name']], image_format=PAIRED_FORMAT)
    simulation.device = None
    host = Host(simulation, image_format=PAIRED_FORMAT)
    host.reset()
    name = 'spi-active-rst-n'
    certify(name, source)
    source.write(out / (name + '.json'))
    host.upload(source)
    peer = SPIPeer(item['mode'], payload_bytes(item['tx_payload'], 2),
                   payload_bytes(item['rx_payload'], 2), item['half_cycles'])
    simulation.device = peer
    host.start()
    require(host.page(0) & 1, 'Reset control did not reach an active SPI transfer')
    require(peer.selected and len(peer.bits) < 16, 'Reset control must interrupt an incomplete SPI transaction')
    before = dict(sampled_bits=len(peer.bits), selected=True)
    # An interrupted transaction has no normal CS hold/framing obligation.
    simulation.device = None
    host.reset()
    require(not host.page(0) & 1, 'rst_n did not stop the SPI engine')
    require(host.result_status() == 0x10 and host.page(1) == 0 and host.page(2) == 0,
            'rst_n did not clear the result mailbox and flags')
    require(simulation.pins.enabled == 0, 'rst_n did not release protocol output pads')
    recovery_name = 'spi-after-active-rst-n'
    recovery = run_spi_cases(simulation, {recovery_name: source},
                            [dict(item, name=recovery_name)], out, certify)
    return dict(boundary='external rst_n through Host.reset', interrupted=before,
                engine_stopped=True, mailbox_cleared=True, outputs_released=True,
                recovery=recovery)


def capture(path, destination):
    data = Path(path).read_bytes()
    destination.write_bytes(data)
    return data, hashlib.sha256(data).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--tag', required=True)
    parser.add_argument('--matrix', action='store_true', help='Include the bounded timing/payload matrix')
    args = parser.parse_args()
    out = fresh_directory(ROOT / 'build/host', args.tag)
    sources = [ROOT / 'Pinwheel.lean', *sorted((ROOT / 'Pinwheel').rglob('*.lean')),
        ROOT / 'lakefile.toml', ROOT / 'lake-manifest.json', ROOT / 'lean-toolchain',
        *[ROOT / 'test' / name for name in ('Loader.lean', 'SPITransactions.lean',
            'PairedValidationEmit.lean', 'paired_chip.sv', 'host_bridge.sv')],
        *[ROOT / 'scripts' / name for name in ('check-spi-capabilities.py', 'pinwheel_host.py',
            'pinwheel_sim.py', 'host_demo.py', 'pad_io.py', 'pad_peers.py', 'paired_execution.py',
            'paired_image_certificate.py', 'execution-vectors.py', 'validation_run.py', 'process_group.py')],
        ROOT / 'tools/storage-macros.json']
    hashes = {str(path.relative_to(ROOT)): sha(path) for path in sources}
    cad = ROOT / 'build/tools/oss-cad-suite/bin'
    circt = ROOT / 'build/tools/firtool-1.159.0/bin/circt-opt'
    models = [ROOT / 'build/storage/macros' / name for name in
              ('RM_IHPSG13_1P_512x64_c2_bm_bist.v', 'RM_IHPSG13_1P_core_behavioral_bm_bist.v')]
    lock = json.loads((ROOT / 'tools/storage-macros.json').read_text())
    # Fail before building if an external tool or SRAM model is unavailable.
    tools = {str(path.relative_to(ROOT)): sha(path.resolve()) for path in (circt, cad / 'iverilog', cad / 'vvp')}
    model_hashes = {}
    for path in models:
        require(sha(path) == lock['files_sha256']['verilog/' + path.name], 'Unpinned macro model ' + path.name)
        model_hashes[path.name] = sha(path)
    started = time.monotonic()
    run = Commands(ROOT, out, default_timeout=600)
    run(['lake', 'build', 'Pinwheel', 'Pinwheel.Compile.SPITransaction'], 'build')
    run(['lake', 'env', 'lean', '-DwarningAsError=true', '--run', 'test/SPITransactions.lean', out], 'compile-spi-programs')
    image_bytes, image_digest = capture(out / 'images.txt', out / 'spi-images.txt')
    metadata_bytes, metadata_digest = capture(out / 'metadata.json', out / 'spi-metadata.json')
    captured_inputs = {'spi-images.txt': image_digest, 'spi-metadata.json': metadata_digest}
    images = compiler_images(image_bytes)
    metadata = fixture_metadata(metadata_bytes, images)
    require({(item['mode'], item['byte_count']) for item in metadata} ==
            {(mode, count) for mode in range(4) for count in (1, 2)} and len(metadata) == 8,
            'Basic SPI fixture must cover all four modes with one and two bytes')
    if args.matrix:
        matrix_bytes, matrix_digest = capture(out / 'matriximages.txt', out / 'spi-matrix-images.txt')
        matrix_meta, matrix_meta_digest = capture(out / 'matrixmetadata.json', out / 'spi-matrix-metadata.json')
        captured_inputs.update({'spi-matrix-images.txt': matrix_digest,
                                'spi-matrix-metadata.json': matrix_meta_digest})
        matrix_images = compiler_images(matrix_bytes)
        matrix = fixture_metadata(matrix_meta, matrix_images)
        require(not set(images) & set(matrix_images), 'Matrix fixture names overlap basic cases')
        images.update(matrix_images)
        metadata.extend(matrix)
    run(['lake', 'env', 'lean', '-DwarningAsError=true', '--run', 'test/Loader.lean'], 'compile-legacy-programs')
    legacy_bytes, legacy_digest = capture(ROOT / 'build/loader/images.txt', out / 'legacy-images.txt')
    captured_inputs['legacy-images.txt'] = legacy_digest
    run(['lake', 'env', 'lean', '-DwarningAsError=true', '--run', 'test/PairedValidationEmit.lean', out], 'emit')
    mlir = out / 'chip.mlir'
    mlir_digest = sha(mlir)
    rtl = run([circt, mlir, '--canonicalize', '--lower-seq-to-sv', '--lower-hw-to-sv',
               '--hw-legalize-modules', '--export-verilog', '-o', '/dev/null'], 'export')
    design = out / 'design.sv'
    design.write_text(rtl)
    rtl_digest = sha(design)
    executable = out / 'host.vvp'
    run([cad / 'iverilog', '-g2012', '-DFUNCTIONAL', '-s', 'host_bridge', '-o', executable,
         design, ROOT / 'test/host_bridge.sv', ROOT / 'test/paired_chip.sv', *models], 'compile-simulation')
    executable_digest = sha(executable)
    certificates = []

    def certify(name, source):
        from paired_execution import compile_e64
        from paired_image_certificate import render
        image = compile_e64(source.words, (source.idle_levels, source.idle_enabled), source.last)
        path = out / (name + '-certificate.lean')
        path.write_text(render(name.replace('-', '_'), source.words, source.last,
                              (source.idle_levels, source.idle_enabled), image, source.upload_words()))
        certificate_digest = sha(path)
        log = run(['lake', 'env', 'lean', '-DwarningAsError=true', path], name + '-certificate')
        require(sha(path) == certificate_digest, 'Certificate changed during kernel check: ' + path.name)
        require('Paired image certificate: kernel checked; standard axioms only.' in log, 'Missing image certificate audit')
        certificates.append(dict(program=name, path=path.name, sha256=certificate_digest,
                                 populated_positions=source.last + 1,
                                 canonical_records=len(set(source.words))))

    with Simulation(cad / 'vvp', executable) as simulation:
        spi = run_spi_cases(simulation, images, metadata, out, certify)
        reset_control = reset_active_spi(simulation, images, metadata, out, certify)
        # These compile and upload normally, including fresh kernel certificates.
        # The independent protocol result decoder must reject the wrong captures.
        baseline = next(item for item in metadata if item['name'] == 'spi-mode0-1byte')
        timing_name = baseline['name'] + '-peer-tco1'
        timing_control = run_spi_cases(simulation, {timing_name: images[baseline['name']]},
                                       [dict(baseline, name=timing_name)], out, certify, tco=1)
        negatives = []
        for suffix, program, tco in [('collapsed-capture-slots', collapse_capture_slots(images[baseline['name']]), 0),
                                     ('late-peer', images[baseline['name']], 2)]:
            name = baseline['name'] + '-' + suffix
            item = dict(baseline, name=name)
            try:
                run_spi_cases(simulation, {name: program}, [item], out, certify, tco=tco)
            except SPIReplyMismatch as error:
                negatives.append(dict(status='rejected_as_expected', reason=suffix,
                                      expected_wire_bytes=error.expected, **error.case))
            else:
                raise RuntimeError('Independent decoder accepted SPI negative: ' + suffix)
        simulation.device = None
        legacy = demonstrate(simulation, compiler_images(legacy_bytes), out,
                             image_format=PAIRED_FORMAT, certify=certify)
    for path in sources:
        require(sha(path) == hashes[str(path.relative_to(ROOT))], 'Source changed during capability run: ' + str(path))
    for path, digest in tools.items():
        require(sha((ROOT / path).resolve()) == digest, 'Tool changed during capability run: ' + path)
    for path in models:
        require(sha(path) == model_hashes[path.name], 'SRAM model changed during capability run')
    for path, digest in ((mlir, mlir_digest), (design, rtl_digest), (executable, executable_digest)):
        require(sha(path) == digest, 'Generated artifact changed during capability run: ' + path.name)
    for certificate in certificates:
        require(sha(out / certificate['path']) == certificate['sha256'],
                'Certificate changed after kernel check: ' + certificate['path'])
    for name, digest in captured_inputs.items():
        require(sha(out / name) == digest, 'Captured input changed after consumption: ' + name)
    report = dict(schema=1, status='passed', candidate='five-pad-digital', backend='paired-validation',
        A_accepted=False, physical_evidence_reused=False, cad_seconds=0,
        pad_map=PAD_MAP, clock_assumption_ns=20, source_sha256=hashes, tools_sha256=tools,
        macro_models_sha256=model_hashes, rtl_sha256=rtl_digest, mlir_sha256=mlir_digest,
        executable_sha256=executable_digest,
        spi_images_sha256=image_digest, spi_metadata_sha256=metadata_digest,
        legacy_images_sha256=legacy_digest, spi=spi, reset_control=reset_control,
        captured_inputs_sha256=captured_inputs,
        timing_contract_control=timing_control,
        negative_spi=negatives, legacy=legacy,
        image_certificates=certificates, commands=run.records,
        elapsed_seconds=round(time.monotonic() - started, 3),
        boundary='Resolved digital package-pad simulation with pinned behavioral SRAM models. '
                 'Separate candidate from retained physical A; no board, analog timing, SRAM qualification or physical acceptance claim.')
    if args.matrix:
        report.update(matrix_images_sha256=matrix_digest, matrix_metadata_sha256=matrix_meta_digest)
    (out / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(dict(status='passed', candidate=report['candidate'],
                         spi_cases=len(spi['cases']), legacy_cases=len(legacy['cases']),
                         rejected_spi_negatives=len(negatives),
                         image_certificates=len(certificates)), indent=2))
    print(out / 'report.json')


if __name__ == '__main__':
    main()
