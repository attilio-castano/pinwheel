#!/usr/bin/env python3
"""Reproducible early CMOS5L mapping. ABC delay is NOT routed timing or full STA."""
import hashlib
import json
import re
import runpy
import shutil
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT/'build/technology'


def run(args, log):
    result = subprocess.run(list(map(str, args)), cwd=ROOT, text=True, capture_output=True)
    text = result.stdout+result.stderr
    (OUT/log).write_text(text)
    if result.returncode: raise RuntimeError(f'Failed {args}\n{text}')
    return text


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT/'report.json').unlink(missing_ok=True)
    manifest = json.loads((ROOT/'tools/hardware-toolchain.json').read_text())
    library_manifest = json.loads((ROOT/'tools/technology-library.json').read_text())
    for item in library_manifest['files']:
        path = ROOT/'build/tools/ihp-cmos5l'/item['name']
        if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != item['sha256']:
            raise RuntimeError('Missing/mismatched library; run scripts/install-technology-library.py')
    yosys = ROOT/'build/tools'/manifest['packages']['oss-cad-suite']['directory']/'bin/yosys'
    circt = ROOT/'build/tools'/manifest['packages']['circt']['directory']/'bin/circt-opt'
    lake = shutil.which('lake')
    if not lake: raise RuntimeError('Pinned Lean must be on PATH')
    run([lake, 'build', 'Pinwheel.Hardware.Reactive.Emit', 'Pinwheel.Hardware.Loader.Emit'], 'build.log')
    run([lake, 'env', 'lean', '--run', 'test/ReactiveCore.lean'], 'baseline-emit.log')
    run([lake, 'env', 'lean', '--run', 'test/Loader.lean'], 'atomic-emit.log')
    designs = {'indexed': ('build/reactive-core/indexed.mlir', 'pinwheel_reactive_indexed', 5695),
               'atomic-indexed': ('build/loader/atomic.mlir', 'pinwheel_atomic_indexed', 11353)}
    (OUT/'abc.constr').write_text('set_driving_cell sg13cmos5l_buf_2\nset_load 10\n')
    metrics, rtl_hashes = {}, {}
    for name, (source, top, expected_ff) in designs.items():
        rtl = run([circt, ROOT/source, '--canonicalize', '--lower-seq-to-sv', '--lower-hw-to-sv',
                   '--hw-legalize-modules', '--export-verilog', '-o', '/dev/null'], f'{name}-export.log')
        (OUT/f'{name}.sv').write_text(rtl)
        rtl_hashes[name] = hashlib.sha256(rtl.encode()).hexdigest()
        metrics[name] = {}
        for corner, libname in [('typical', 'sg13cmos5l_stdcell_typ_1p20V_25C.lib'),
                                ('slow', 'sg13cmos5l_stdcell_slow_1p08V_125C.lib')]:
            lib = ROOT/'build/tools/ihp-cmos5l'/libname
            key = f'{name}-{corner}'
            # Preserve FF boundaries: ABC maps combinational logic only, so its delay excludes setup/clk-to-Q.
            script = '\n'.join([f'read_verilog -sv {OUT}/{name}.sv', f'hierarchy -check -top {top}',
                f'synth -top {top} -noabc', f'dfflibmap -liberty {lib}',
                f'abc -liberty {lib} -constr {OUT}/abc.constr -D 10000',
                f'read_liberty -lib {lib}', 'clean', 'check -assert', f'stat -liberty {lib}',
                f'write_json {OUT}/{key}-netlist.json', ''])
            (OUT/f'{key}.ys').write_text(script)
            log = run([yosys, '-Q', '-T', '-s', OUT/f'{key}.ys'], f'{key}.log')
            area = re.findall(r'Chip area for module.*?:\s*([\d.]+)', log)
            sequential = re.findall(r'of which used for sequential elements:\s*([\d.]+)', log)
            # Multiple sizing steps print delays; use the last stime result.
            delays = re.findall(r'ABC RESULTS:.*?Delay\s*=\s*([\d.]+)', log)
            if not delays: delays = re.findall(r'ABC:.*?Delay\s*=\s*([\d.]+)', log)
            if not (area and sequential and delays): raise RuntimeError(f'Missing area/delay in {key}.log')
            cells = json.loads((OUT/f'{key}-netlist.json').read_text())['modules'][top]['cells']
            ff = sum(c['type'].startswith('sg13cmos5l_df') for c in cells.values())
            if ff != expected_ff: raise RuntimeError(f'Unexpected mapped FF count in {key}: {ff}')
            metrics[name][corner] = dict(standard_cell_area_um2=float(area[-1]), sequential_area_um2=float(sequential[-1]),
                                        abc_combinational_delay_ps=float(delays[-1]), mapped_cells=len(cells), flip_flops=ff,
                                        library=libname)
            print(f'{key}: area {area[-1]} um^2, ABC combinational delay {delays[-1]} ps.', flush=True)
    paths = sorted((ROOT/'Pinwheel').rglob('*.lean')) + [ROOT/p for p in [
        'test/ReactiveCore.lean', 'test/Loader.lean', 'scripts/check-technology.py',
        'scripts/install-technology-library.py', 'tools/technology-library.json', 'tools/hardware-toolchain.json', 'lean-toolchain']]
    hashes = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
    report = dict(metrics=metrics, source_sha256=hashes, rtl_sha256=rtl_hashes,
                  library_manifest=library_manifest,
                  versions=dict(yosys=run([yosys, '-V'], 'yosys-version.log').strip(),
                                circt=run([circt, '--version'], 'circt-version.log').strip()),
                  constraints=dict(driving_cell='sg13cmos5l_buf_2', output_load_fF=10, abc_target_ps=10000),
                  boundary='Separately mapped corners; standard-cell sum and ABC combinational estimates only. No floorplan, placement, routing, parasitics, clock tree, pads, SRAM macros or full STA. Not a frequency/fit sign-off.')
    (OUT/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    print('Wrote build/technology/report.json', flush=True)


if __name__ == '__main__': main()
