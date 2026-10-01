#!/usr/bin/env python3
"""Compile programs, upload them to actual RTL, and read retained chip results.

The default demo runs all examples on one unchanged chip. `run` accepts an
explicitly formatted JSON program for the selected backend. The paired backend
kernel-checks each canonical E64 image before sending its 290 upload words.
"""
import argparse
from dataclasses import asdict
import hashlib
import json
from pathlib import Path
import re
import time

from host_demo import compiler_images, demonstrate
from pinwheel_host import Host, Program, LEGACY_FORMAT, PAIRED_FORMAT
from pinwheel_sim import Simulation
from pad_io import PAD_MAP
from validation_run import Commands, fresh_directory, sha

ROOT = Path(__file__).resolve().parents[1]


def capture_input(path, destination):
    """Keep parsing, the retained copy and its digest bound to the same bytes."""
    data = path.read_bytes()
    destination.write_bytes(data)
    return data, hashlib.sha256(data).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action', choices=['demo', 'run'])
    parser.add_argument('--tag', required=True)
    parser.add_argument('--backend', choices=['hybrid', 'reference', 'paired', 'paired-validation', 'paired-stream'], default='hybrid')
    parser.add_argument('--program', type=Path)
    parser.add_argument('--incoming', type=lambda n: int(n, 0), default=3)
    parser.add_argument('--timeout-cycles', type=int, default=100_000)
    args = parser.parse_args()
    if (args.action == 'run') != (args.program is not None):
        parser.error('run requires --program; demo uses the compiler examples')
    if not 0 <= args.incoming < 4 or args.timeout_cycles < 0:
        parser.error('incoming must be 0..3 and timeout-cycles nonnegative')
    out = fresh_directory(ROOT / 'build/host', args.tag)
    paired = args.backend in ('paired', 'paired-validation', 'paired-stream')
    image_format = PAIRED_FORMAT if paired else LEGACY_FORMAT
    started = time.monotonic()
    program = program_digest = None
    captured_inputs = {}
    if args.program is not None:
        program_bytes, program_digest = capture_input(args.program, out / 'program.json')
        program = Program.from_bytes(program_bytes)
        captured_inputs['program.json'] = program_digest
        if program.image_format != image_format:
            raise ValueError('Program image format does not match --backend')
    sources = [ROOT / 'Pinwheel.lean', *sorted((ROOT / 'Pinwheel').rglob('*.lean')), ROOT / 'lakefile.toml',
        ROOT / 'lake-manifest.json',
        ROOT / 'lean-toolchain', ROOT / 'test/Loader.lean', ROOT / 'test/ChipEmit.lean',
        ROOT / 'test/SramChipEmit.lean', ROOT / 'test/sram_chip.sv', ROOT / 'test/host_bridge.sv',
        ROOT / 'test/PairedChipEmit.lean', ROOT / 'test/paired_chip.sv',
        ROOT / 'test/PairedValidationEmit.lean',
        ROOT / 'tools/storage-macros.json',
        *[ROOT / 'scripts' / n for n in ['pinwheel-host.py', 'pinwheel_host.py',
           'pinwheel_sim.py', 'host_demo.py', 'pad_io.py', 'pad_peers.py', 'validation_run.py', 'process_group.py',
           'paired_execution.py', 'paired_image_certificate.py', 'execution-vectors.py']]]
    if args.backend == 'paired-stream':
        sources += [ROOT/'test/PairedStreamEmit.lean',ROOT/'tools/hardware-toolchain.json',
                    ROOT/'scripts/protocol_tool_closure.py']
    hashes = {str(p.relative_to(ROOT)): sha(p) for p in sources}
    run = Commands(ROOT, out, default_timeout=600)
    lean_version = None
    if args.backend == 'paired-stream':
        lean_version = run(['lake','env','lean','--version'],'lean-version').strip()
        version = (ROOT/'lean-toolchain').read_text().strip().split(':v')[-1]
        if not re.search(r'Lean \(version '+re.escape(version)+r'(?:,|\s)',lean_version):
            raise RuntimeError('Lean version differs from the pinned paired-stream toolchain')
    emitter = 'sram_chip_emit' if args.backend == 'hybrid' else 'chip_emit'
    run(['lake', 'build', 'Pinwheel', *([] if paired else [emitter])], 'build')
    run(['lake', 'env', 'lean', '-DwarningAsError=true', '--run', 'test/Loader.lean'], 'compile-programs')
    images_bytes, images_digest = capture_input(ROOT / 'build/loader/images.txt', out / 'compiler-images.txt')
    captured_inputs['compiler-images.txt'] = images_digest
    if paired:
        source = {'paired-validation':'test/PairedValidationEmit.lean',
                  'paired-stream':'test/PairedStreamEmit.lean'}.get(args.backend,'test/PairedChipEmit.lean')
        run(['lake', 'env', 'lean', '-DwarningAsError=true', '--run', source, out], 'emit')
    else:
        run([ROOT / '.lake/build/bin' / emitter, out], 'emit')
    circt = ROOT / 'build/tools/firtool-1.159.0/bin/circt-opt'
    cad = ROOT / 'build/tools/oss-cad-suite/bin'
    closure = None
    if args.backend == 'paired-stream':
        from protocol_tool_closure import ProtocolToolClosure
        closure = ProtocolToolClosure(ROOT,circt,cad/'iverilog',cad/'vvp')
    tool_hashes = {str(path.relative_to(ROOT)): sha(path.resolve())
                   for path in (closure.files if closure else (circt, cad / 'iverilog', cad / 'vvp'))}
    mlir = out / {'hybrid': 'hybrid-chip.mlir', 'paired': 'chip.mlir', 'paired-validation': 'chip.mlir', 'paired-stream': 'chip.mlir',
                  'reference': 'chip-twoport-result.mlir'}[args.backend]
    mlir_digest = sha(mlir)
    rtl = run([circt, mlir, '--canonicalize', '--lower-seq-to-sv', '--lower-hw-to-sv',
        '--hw-legalize-modules', '--export-verilog', '-o', '/dev/null'], 'export')
    design = out / 'design.sv'
    design.write_text(rtl)
    rtl_digest = sha(design)
    extra, defines = [], []
    models = {}
    if args.backend in ('hybrid', 'paired', 'paired-validation', 'paired-stream'):
        lock = json.loads((ROOT / 'tools/storage-macros.json').read_text())
        size = 512 if paired else 64
        names = [f'RM_IHPSG13_1P_{size}x64_c2_bm_bist.v', 'RM_IHPSG13_1P_core_behavioral_bm_bist.v']
        for name in names:
            path = ROOT / 'build/storage/macros' / name
            if sha(path) != lock['files_sha256']['verilog/' + name]:
                raise RuntimeError('Unpinned macro simulation model: ' + name)
            models[name] = sha(path)
        defines = ['-DFUNCTIONAL', '-DSRAM_HYBRID']
        extra = [ROOT / ('test/paired_chip.sv' if paired else 'test/sram_chip.sv'),
                 *[ROOT / 'build/storage/macros' / name for name in names]]
    executable = out / 'host.vvp'
    run([cad / 'iverilog', *(['-B',closure.backend] if closure else []), '-g2012', *defines, '-s', 'host_bridge', '-o', executable,
         design, ROOT / 'test/host_bridge.sv', *extra], 'compile-simulation')
    executable_digest = sha(executable)
    if closure:
        closure.check_executable(executable)
    certificates = []

    def certify(name, source):
        from paired_execution import compile_e64
        from paired_image_certificate import render
        image = compile_e64(source.words, (source.idle_levels, source.idle_enabled), source.last)
        path = out/(name+'-certificate.lean')
        path.write_text(render(name.replace('-', '_'), source.words, source.last,
            (source.idle_levels, source.idle_enabled), image, source.upload_words()))
        certificate_digest = sha(path)
        log = run(['lake', 'env', 'lean', '-DwarningAsError=true', path], name+'-certificate')
        if sha(path) != certificate_digest:
            raise RuntimeError('Certificate changed during kernel check: ' + path.name)
        if 'Paired image certificate: kernel checked; standard axioms only.' not in log:
            raise RuntimeError('Missing paired image certificate audit')
        certificates.append(dict(program=name, path=path.name, sha256=certificate_digest))

    with Simulation(cad / 'vvp', executable) as simulation:
        if args.action == 'demo':
            result = demonstrate(simulation, compiler_images(images_bytes), out, image_format=image_format,
                                 certify=certify if paired else None)
        else:
            if paired:
                certify('program', program)
            simulation.incoming = args.incoming
            host = Host(simulation, image_format=image_format)
            host.reset()
            host.upload(program)
            host.start()
            result = dict(result=asdict(host.read_result(timeout_cycles=args.timeout_cycles)),
                          image_format=image_format,
                          program_sha256=program_digest, program_snapshot='program.json',
                          edges=host.edges, frames=host.frames)
    result.setdefault('pad_map', PAD_MAP)
    for path in sources:
        if sha(path) != hashes[str(path.relative_to(ROOT))]:
            raise RuntimeError(f'Source changed during demonstration: {path}')
    for path, digest in ((mlir, mlir_digest), (design, rtl_digest), (executable, executable_digest)):
        if sha(path) != digest:
            raise RuntimeError('Generated artifact changed during demonstration: ' + path.name)
    for certificate in certificates:
        if sha(out / certificate['path']) != certificate['sha256']:
            raise RuntimeError('Certificate changed after kernel check: ' + certificate['path'])
    for path, digest in tool_hashes.items():
        if sha((ROOT / path).resolve()) != digest:
            raise RuntimeError('Tool changed during demonstration: ' + path)
    for name, digest in models.items():
        if sha(ROOT / 'build/storage/macros' / name) != digest:
            raise RuntimeError('SRAM model changed during demonstration: ' + name)
    for name, digest in captured_inputs.items():
        if sha(out / name) != digest:
            raise RuntimeError('Captured input changed after consumption: ' + name)
    if closure:
        if run(['lake','env','lean','--version'],'lean-version-closeout').strip() != lean_version:
            raise RuntimeError('Lean version changed during paired-stream demonstration')
        closure.closeout()
    report = dict(backend=args.backend, action=args.action, source_sha256=hashes,
        image_certificates=certificates,
        rtl_sha256=rtl_digest, mlir_sha256=mlir_digest, executable_sha256=executable_digest,
        macro_models_sha256=models,
        tools_sha256=tool_hashes,
        compiled_images_sha256=images_digest, compiled_images_snapshot='compiler-images.txt', commands=run.records,
        captured_inputs_sha256=captured_inputs,
        elapsed_seconds=round(time.monotonic() - started, 3), **result,
        boundary='Interactive host transactions on one unchanged RTL chip. Protocol peers inspect only '
                 'external pins. No FPGA/board, analog timing, SRAM refinement or physical closure claim.')
    if closure:
        report['bundled_tool_closure'] = closure.identity()
        report['lean_version'] = lean_version
        report['lean_version_unchanged'] = True
        report['stream_channel'] = 'One-shot demo/run with supervisor disabled; streaming requires explicit Host API.'
    (out / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items() if k in ['backend', 'cases', 'result', 'edges',
          'frames', 'upload_time_ms_at_assumed_clock', 'elapsed_seconds']}, indent=2))
    print(out / 'report.json')


if __name__ == '__main__':
    main()
