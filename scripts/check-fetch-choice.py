#!/usr/bin/env python3
"""Screen a proved fetch or command-decoder topology using independent traces and full-core mapping."""
import argparse
import hashlib
import json
import re
import runpy
import shutil
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / 'build/successor-fetch'
ORACLE = ROOT / 'build/storage/small-dense-cached'
TOP = 'pinwheel_atomic_small_dense_cached'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('variant', choices=['late-index', 'late-record', 'command-split'])
    parser.add_argument('--tag', default='initial')
    args = parser.parse_args()
    if not args.tag.replace('-', '').replace('_', '').isalnum():
        parser.error('Use letters, numbers, hyphens or underscores in tags')
    out = BASE / f'{args.variant}-{args.tag}'
    if out.exists():
        raise RuntimeError('Choose a new tag to preserve earlier experiment evidence')
    contract_path = ROOT / 'build/contracts/report.json'
    contract = json.loads(contract_path.read_text())
    required = ['Pinwheel.Hardware.Storage.FetchChoice.' + n for n in
                ['fetch_correct', 'step_same', 'observe_same', 'refinement', 'completeRefinement', 'trace_correct']]
    if args.variant == 'command-split':
        required = ['Pinwheel.Hardware.Storage.CommandSplit.' + n for n in
                    ['expression_correct', 'adapted_small', 'commit_structure', 'start_structure',
                     'component_same', 'trace_correct']]
    if not set(required).issubset(contract['audited_declarations']):
        raise RuntimeError('Run the expanded timed-contract proof audit first')
    for name, expected in contract['source_sha256'].items():
        if sha(ROOT / name) != expected:
            raise RuntimeError(f'Stale proof receipt: {name}')
    baseline = json.loads((ROOT / 'test/timed-contracts-baseline.json').read_text())
    for name, expected in baseline['oracle_sha256'].items():
        if sha(ORACLE / name) != expected:
            raise RuntimeError(f'Changed oracle fixture: {name}')
    mapping_path = ORACLE / 'report.json'
    mapping = json.loads(mapping_path.read_text())
    if mapping['rtl_sha256'] != baseline['rtl_sha256']:
        raise RuntimeError('Mapped baseline RTL differs from the fixed reference')
    if sha(ROOT / 'build/physical/core/design.sv') != baseline['rtl_sha256']:
        raise RuntimeError('Port-comparison reference is not the fixed baseline')
    library = json.loads((ROOT / 'tools/technology-library.json').read_text())
    for item in library['files']:
        if sha(ROOT / 'build/tools/ihp-cmos5l' / item['name']) != item['sha256']:
            raise RuntimeError('Technology library identity changed')
    lake = shutil.which('lake')
    if not lake:
        raise RuntimeError('Put the pinned Lean toolchain on PATH')
    out.mkdir(parents=True)

    def run(command, label, reject=False):
        result = subprocess.run(list(map(str, command)), cwd=ROOT, text=True, capture_output=True)
        log = result.stdout + result.stderr
        (out / label).write_text(log)
        if reject:
            if not result.returncode or 'LOADER edge' not in log:
                raise RuntimeError(f'Mutation not detected; inspect {out / label}')
        elif result.returncode:
            raise RuntimeError(f'Command failed; inspect {out / label}')
        return log

    emitter = 'CommandSplitEmit' if args.variant == 'command-split' else 'FetchChoiceEmit'
    run([lake, 'env', 'lean', '--run', f'test/{emitter}.lean'], 'emit.log')
    shutil.copyfile(BASE / args.variant / 'candidate.mlir', out / 'candidate.mlir')
    circt = ROOT / 'build/tools/firtool-1.159.0/bin/circt-opt'
    suite = ROOT / 'build/tools/oss-cad-suite/bin'
    rtl = run([circt, out / 'candidate.mlir', '--canonicalize', '--lower-seq-to-sv',
               '--lower-hw-to-sv', '--hw-legalize-modules', '--export-verilog', '-o', '/dev/null'], 'export.log')
    (out / 'design.sv').write_text(rtl)

    oracle = runpy.run_path(str(ROOT / 'scripts/loader-vectors.py'))
    m = oracle['Atomic']()
    m.edge(init=1)
    words = [oracle['pack'](dict(kind=2, levels=p+1, enabled=3, terminal=63,
                               entry=61, finish=2, sample=15, yes=1-p, no=p)) for p in range(2)]
    m.load('consecutive-live-input-branches', words, 1)
    m.edge(command=5)
    for n in range(128):
        incoming = n % 4
        expected_pc = m.s[1] ^ (incoming >> 1)
        m.edge(incoming=incoming, command=n % 7 + 1, data=(1 << 64)-1)
        if m.s[0] != 3 or m.s[1] != expected_pc or m.s[6] >> 15 != (incoming & 1):
            raise RuntimeError('Independent one-cycle branch expectation failed')
        if m.gates != [0, 0, 0, 1]:
            raise RuntimeError('Busy host command was not rejected')
    vectors = (ORACLE / 'vectors.txt').read_text() + ''.join(' '.join(map(str, row))+'\n' for row in m.rows)
    (out / 'vectors.txt').write_text(vectors)
    tb = (ORACLE / 'tb.sv').read_text().replace('build/storage/small-dense-cached/vectors.txt',
                                               str((out / 'vectors.txt').relative_to(ROOT)))
    (out / 'tb.sv').write_text(tb)
    compile_command = [suite / 'iverilog', '-g2012', '-s', 'loader_tb', '-o', out / 'sim.vvp',
                       out / 'design.sv', out / 'tb.sv']
    run(compile_command, 'compile.log')
    simulation = run([suite / 'vvp', out / 'sim.vvp'], 'simulation.log')
    print(simulation.strip(), flush=True)
    mutant, count = re.subn(r'(\bwire\s+fetch_choice_condition\s*=\s*)([^;]+);',
                            lambda m: m[1]+'~('+m[2]+');', rtl)
    mutation = 'branch-selection'
    if args.variant == 'command-split':
        # Remove only the rejection mux, leaving the raw push command intact.
        mutant, count = re.subn(r"\(command == 3'h2\s*& ~\(.*?\)\s*\? 3'h6\s*: command\)",
                                'command', rtl, flags=re.S)
        mutation = 'capacity-rejection-bypass'
    if count != 1:
        raise RuntimeError(f'Expected one {mutation} mutation anchor; found {count}')
    (out / 'mutant.sv').write_text(mutant)
    run([out / 'mutant.sv' if p == out / 'design.sv' else p for p in compile_command], 'mutant-compile.log')
    run([suite / 'vvp', out / 'sim.vvp'], 'mutant.log', reject=True)
    label = f'fetch-{args.variant}-{args.tag}'
    run(['python3', ROOT / 'scripts/check-physical-netlist.py', out / 'design.sv',
         '--label', label, '--vectors', out / 'vectors.txt'], 'ports.log')
    port_receipt = ROOT / f'build/physical/{label}-check/report.json'
    print(f'{mutation} mutation rejected; all defined baseline output bits match.', flush=True)

    (out / 'abc.constr').write_text('set_driving_cell sg13cmos5l_buf_2\nset_load 10\n')
    metrics = {}
    for corner, libname in [('typical', 'sg13cmos5l_stdcell_typ_1p20V_25C.lib'),
                            ('slow', 'sg13cmos5l_stdcell_slow_1p08V_125C.lib')]:
        lib = ROOT / 'build/tools/ihp-cmos5l' / libname
        script = '\n'.join([f'read_verilog -sv {out}/design.sv', f'hierarchy -check -top {TOP}',
                            f'synth -top {TOP} -noabc', f'dfflibmap -liberty {lib}',
                            f'abc -liberty {lib} -constr {out}/abc.constr -D 10000',
                            f'read_liberty -lib {lib}', 'clean', 'check -assert', f'stat -liberty {lib}',
                            f'write_json {out}/{corner}.json', ''])
        (out / f'{corner}.ys').write_text(script)
        log = run([suite / 'yosys', '-Q', '-T', '-s', out / f'{corner}.ys'], f'{corner}.log')
        cells = json.loads((out / f'{corner}.json').read_text())['modules'][TOP]['cells']
        ff = sum(c['type'].startswith('sg13cmos5l_df') for c in cells.values())
        if ff != mapping['metrics'][corner]['flip_flops']:
            raise RuntimeError('Candidate unexpectedly changed the register count')
        metrics[corner] = dict(standard_cell_area_um2=float(re.findall(r'Chip area for module.*?:\s*([\d.]+)', log)[-1]),
                               abc_combinational_delay_ps=float(re.findall(r'ABC(?: RESULTS)?:.*?Delay\s*=\s*([\d.]+)', log)[-1]),
                               flip_flops=ff, cells=len(cells))
        print(args.variant, corner, metrics[corner], flush=True)
    sources = sorted((ROOT / 'Pinwheel').rglob('*.lean')) + [Path(__file__).resolve(),
              ROOT / f'test/{emitter}.lean', ROOT / 'scripts/check-physical-netlist.py',
              ROOT / 'scripts/loader-vectors.py', ROOT / 'scripts/reactive-core-vectors.py',
              ROOT / 'scripts/execution-vectors.py', ROOT / 'tools/technology-library.json',
              ROOT / 'tools/hardware-toolchain.json']
    report = dict(variant=args.variant, tag=args.tag, metrics=metrics, baseline_metrics=mapping['metrics'],
                  oracle_simulation=simulation, port_comparison=json.loads(port_receipt.read_text()),
                  mutation_rejected=mutation, additional_branch_edges=128,
                  source_sha256={str(p.relative_to(ROOT)): sha(p) for p in sources},
                  artifact_sha256={str(p.relative_to(ROOT)): sha(p) for p in
                                   [out / 'design.sv', out / 'candidate.mlir', out / 'vectors.txt',
                                    out / 'tb.sv', out / 'abc.constr', contract_path, mapping_path, port_receipt]},
                  versions=dict(yosys=run([suite / 'yosys', '-V'], 'yosys-version.log').strip(),
                                circt=run([circt, '--version'], 'circt-version.log').strip()),
                  boundary='Full-core standard-cell sums and separately mapped ABC combinational delay estimates. '
                           'No extracted STA, physical fit, or emitter/CIRCT proof. Same-edge structural proof '
                           'and independent RTL checks are separate evidence.')
    (out / 'report.json').write_text(json.dumps(report, indent=2)+'\n')


if __name__ == '__main__':
    main()
