#!/usr/bin/env python3
"""Compile programs, upload them to actual RTL, and read retained chip results.

The default demo runs all examples on one unchanged chip. `run` accepts an
exported pinwheel-e64-v1 JSON image and constant external input levels.
"""
import argparse
from dataclasses import asdict
import hashlib
import json
from pathlib import Path
import time

from host_demo import compiler_images, demonstrate
from pinwheel_host import Host, Program
from pinwheel_sim import Simulation
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
    parser.add_argument('--backend', choices=['hybrid', 'reference'], default='hybrid')
    parser.add_argument('--program', type=Path)
    parser.add_argument('--incoming', type=lambda n: int(n, 0), default=3)
    parser.add_argument('--timeout-cycles', type=int, default=100_000)
    args = parser.parse_args()
    if (args.action == 'run') != (args.program is not None):
        parser.error('run requires --program; demo uses the compiler examples')
    if not 0 <= args.incoming < 4 or args.timeout_cycles < 0:
        parser.error('incoming must be 0..3 and timeout-cycles nonnegative')
    out = fresh_directory(ROOT / 'build/host', args.tag)
    started = time.monotonic()
    program = program_digest = None
    if args.program is not None:
        program_bytes, program_digest = capture_input(args.program, out / 'program.json')
        program = Program.from_bytes(program_bytes)
    sources = [*sorted((ROOT / 'Pinwheel').rglob('*.lean')), ROOT / 'lakefile.toml',
        ROOT / 'lean-toolchain', ROOT / 'test/Loader.lean', ROOT / 'test/ChipEmit.lean',
        ROOT / 'test/SramChipEmit.lean', ROOT / 'test/sram_chip.sv', ROOT / 'test/host_bridge.sv',
        *[ROOT / 'scripts' / n for n in ['pinwheel-host.py', 'pinwheel_host.py',
           'pinwheel_sim.py', 'host_demo.py', 'validation_run.py', 'process_group.py']]]
    hashes = {str(p.relative_to(ROOT)): sha(p) for p in sources}
    run = Commands(ROOT, out, default_timeout=600)
    emitter = 'sram_chip_emit' if args.backend == 'hybrid' else 'chip_emit'
    run(['lake', 'build', 'Pinwheel', emitter], 'build')
    run(['lake', 'env', 'lean', '-DwarningAsError=true', '--run', 'test/Loader.lean'], 'compile-programs')
    images_bytes, images_digest = capture_input(ROOT / 'build/loader/images.txt', out / 'compiler-images.txt')
    run([ROOT / '.lake/build/bin' / emitter, out], 'emit')
    circt = ROOT / 'build/tools/firtool-1.159.0/bin/circt-opt'
    cad = ROOT / 'build/tools/oss-cad-suite/bin'
    mlir = out / ('hybrid-chip.mlir' if args.backend == 'hybrid' else 'chip-twoport-result.mlir')
    rtl = run([circt, mlir, '--canonicalize', '--lower-seq-to-sv', '--lower-hw-to-sv',
        '--hw-legalize-modules', '--export-verilog', '-o', '/dev/null'], 'export')
    design = out / 'design.sv'
    design.write_text(rtl)
    extra, defines = [], []
    models = {}
    if args.backend == 'hybrid':
        lock = json.loads((ROOT / 'tools/storage-macros.json').read_text())
        names = ['RM_IHPSG13_1P_64x64_c2_bm_bist.v', 'RM_IHPSG13_1P_core_behavioral_bm_bist.v']
        for name in names:
            path = ROOT / 'build/storage/macros' / name
            if sha(path) != lock['files_sha256']['verilog/' + name]:
                raise RuntimeError('Unpinned macro simulation model: ' + name)
            models[name] = sha(path)
        defines = ['-DFUNCTIONAL', '-DSRAM_HYBRID']
        extra = [ROOT / 'test/sram_chip.sv',
                 *[ROOT / 'build/storage/macros' / name for name in names]]
    executable = out / 'host.vvp'
    run([cad / 'iverilog', '-g2012', *defines, '-s', 'host_bridge', '-o', executable,
         design, ROOT / 'test/host_bridge.sv', *extra], 'compile-simulation')
    with Simulation(cad / 'vvp', executable) as simulation:
        if args.action == 'demo':
            result = demonstrate(simulation, compiler_images(images_bytes), out)
        else:
            simulation.incoming = args.incoming
            host = Host(simulation)
            host.reset()
            host.upload(program)
            host.start()
            result = dict(result=asdict(host.read_result(timeout_cycles=args.timeout_cycles)),
                          program_sha256=program_digest, program_snapshot='program.json',
                          edges=host.edges, frames=host.frames)
    for path in sources:
        if sha(path) != hashes[str(path.relative_to(ROOT))]:
            raise RuntimeError(f'Source changed during demonstration: {path}')
    report = dict(backend=args.backend, action=args.action, source_sha256=hashes,
        rtl_sha256=sha(design), mlir_sha256=sha(mlir), macro_models_sha256=models,
        tools_sha256={str(p.relative_to(ROOT)): sha(p.resolve()) for p in [circt, cad / 'iverilog', cad / 'vvp']},
        compiled_images_sha256=images_digest, compiled_images_snapshot='compiler-images.txt', commands=run.records,
        elapsed_seconds=round(time.monotonic() - started, 3), **result,
        boundary='Interactive host transactions on one unchanged RTL chip. Protocol peers inspect only '
                 'external pins. No FPGA/board, analog timing, SRAM refinement or physical closure claim.')
    (out / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items() if k in ['backend', 'cases', 'result', 'edges',
          'frames', 'upload_time_ms_at_assumed_clock', 'elapsed_seconds']}, indent=2))
    print(out / 'report.json')


if __name__ == '__main__':
    main()
