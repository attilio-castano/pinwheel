#!/usr/bin/env python3
"""Compare a bounded shared-branch bank with the accepted inline reactive bank.

Same clock/owned-result contract; a separately admitted 16-descriptor target.
Mapped cell area and gate depth are structural screens, not physical timing.
"""
import argparse
from collections import Counter
from copy import deepcopy
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import sys
import time
import types

from buffered_hardware_synthesis import CAD, compile_rtl, stage_pdk, synthesize
from buffered_reactive_hardware_rtl import BufferedReactiveRTL, replay_vectors
from buffered_shared_branches import BufferedSharedBranchesHost
from validation_run import Commands, fresh_directory, sha

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location('inline_reactive_gate',
    ROOT / 'scripts/check-buffered-reactive-hardware.py')
BASE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(BASE)
TOP = 'pinwheel_buffered_shared_branches'
BRIDGE = ROOT / 'physical/buffered_shared_branches_host_bridge.sv'
STORAGE = dict(rows=[(f'r_row{k}', 92) for k in range(64)],
    branches=[(f'r_branch{k}', 56) for k in range(16)],
    row_coverage=[('r_written', 64)], branch_coverage=[('r_branch_written', 16)],
    tx=[('r_tx_data', 32)], rx=[('r_rx_data', 32)])


def convert_request(original):
    """Independent first-use interning of raw descriptors, including bad words.

    Insert a full table before each case's first row; the old directed fixtures
    contain at most three distinct descriptors. Preserve original input history
    after insertion and every independently specified edge expectation.
    """
    cases = []
    for old in original['cases']:
        values = tuple(dict.fromkeys(v['command'].get('branch', 0)
            for v in old['vectors'] if v['command'].get('command') == 1))
        BASE.require(len(values) <= 16, 'Command fixture exceeds branch-table capacity')
        table = values + (0,) * (16 - len(values))
        index = {value: k for k, value in enumerate(values)}
        vectors, checks, translated = [], [], {}
        inserted = False
        for k, vector in enumerate(old['vectors']):
            v = deepcopy(vector)
            if v['command'].get('command') == 1:
                if not inserted:
                    for address, branch in enumerate(table):
                        vectors.append(dict(command=dict(command=6, address=address,
                            branch=branch), raw_inputs=v['raw_inputs']))
                        checks.append(dict(edge=len(vectors)-1,
                            state=dict(rejected=0, pending=1, valid=0, busy=0, retained=0)))
                    inserted = True
                v['command']['branch'] = index[v['command'].get('branch', 0)]
            translated[k] = len(vectors)
            vectors.append(v)
        checks += [dict(edge=translated[c['edge']], state=deepcopy(c['state']))
                   for c in old['checks']]
        cases.append(dict(name=old['name'], vectors=vectors, checks=checks))
    return dict(schema='pinwheel-buffered-shared-branches-input-v1', cases=cases)


def upload_cases():
    """Joint upload epochs, rejected mutations and stale coverage witnesses."""
    result = []
    def case(name):
        vectors, checks = [], []
        def edge(raw=3, expect=None, **command):
            vectors.append(dict(command=command, raw_inputs=raw))
            if expect is not None:
                checks.append(dict(edge=len(vectors)-1, state=expect))
        edge(initialize=1)
        result.append(dict(name=name, vectors=vectors, checks=checks))
        return edge
    for order in ('table-first', 'row-first'):
        edge = case('joint-generation-' + order)
        if order == 'row-first':
            edge(command=1, word=3, expect=dict(pending=1, valid=0, rejected=0))
        for k in range(15):
            edge(command=6, address=k, branch=0, expect=dict(pending=1, rejected=0))
        if order == 'table-first':
            edge(command=1, word=3)
        edge(command=2, count=1, virtual_span=1,
             expect=dict(valid=0, pending=1, rejected=1, generation=0))
        edge(command=6, address=15)
        edge(command=2, count=1, virtual_span=1,
             expect=dict(valid=1, pending=0, rejected=0, generation=1))
        # A new table-first epoch must clear old row coverage; a row-first epoch
        # must clear old table coverage. Neither can commit stale stored bytes.
        if order == 'table-first':
            for k in range(16): edge(command=6, address=k)
        else:
            edge(command=1, word=3)
        edge(command=2, count=1, virtual_span=1,
             expect=dict(valid=0, pending=1, rejected=1, generation=1))
        if order == 'table-first': edge(command=1, word=3)
        else:
            for k in range(16): edge(command=6, address=k)
        edge(command=2, count=1, virtual_span=1,
             expect=dict(valid=1, pending=0, rejected=0, generation=2))
        # Immediate COMMIT -> START still enters the first row on that edge.
        edge(command=3, expected_generation=2,
             expect=dict(phase=5, mode=2, retained=1, transfer=1))
        edge(command=6, address=0, branch=4,
             expect=dict(rejected=1, retained=1, phase=5, valid=1))
        edge(command=4, expected_generation=2, expected_transfer=1)
        edge(command=3, expected_generation=2,
             expect=dict(rejected=0, phase=5, transfer=2))
    edge = case('compact-upload-range-rejections')
    for fields in (dict(command=6, address=16), dict(command=6, address=63),
                   dict(command=1, branch=16), dict(command=1, branch=1 << 55)):
        edge(**fields, expect=dict(rejected=1, pending=0, valid=0, generation=0))
    # An active WAIT must reject table and row writes before any storage effect.
    edge = case('active-table-write-rejection')
    for k in range(16): edge(command=6, address=k)
    edge(command=1, word=5 | (1 << 46) | (255 << 47))
    edge(command=1, address=1, word=3)
    edge(command=2, count=2, virtual_span=2)
    edge(raw=0); edge(raw=0)
    edge(raw=0, command=3, expected_generation=1, expect=dict(phase=2, busy=1))
    edge(raw=0, command=6, branch=4, expect=dict(rejected=1, phase=2, busy=1))
    edge(raw=0, command=1, word=3, expect=dict(rejected=1, phase=2, busy=1))
    edge(raw=1); edge(raw=1)
    edge(raw=1, expect=dict(phase=5, mode=2, retained=1, rx_length=0))
    edge = case('full-dictionary-last-reference')
    edge(command=6, address=0, branch=0)
    for k in range(1, 16):
        virtual = k + 1 if k < 15 else 1
        endpoint = (virtual << 1) | (1 << 11)
        edge(command=6, address=k, branch=1 | (endpoint << 6))
    edge(command=1, address=0, word=6, branch=15)
    edge(command=1, address=1, word=3, branch=0)
    edge(command=2, count=2, virtual_span=2)
    edge(command=3, expected_generation=1, expect=dict(phase=3, pc=0, virtual_pc=0))
    edge(expect=dict(phase=5, mode=2, retained=1, tx_consumed=0, rx_length=0))
    return result


def check_export(request, exported):
    BASE.require(exported.get('schema') == 'pinwheel-buffered-shared-branches-vectors-v1',
                 'Wrong shared-branch export schema')
    normalized = dict(exported, schema='pinwheel-buffered-reactive-hardware-vectors-v1')
    return BASE.check_export(request, normalized)


def wire_gate(executable, full=False):
    # Reuse independent resolved-pad peers, source engine and sampler FIFO;
    # change only the explicitly versioned host, not global baseline state.
    namespace = dict(BASE.wire_gate.__globals__, BufferedReactiveHardwareHost=BufferedSharedBranchesHost)
    run = types.FunctionType(BASE.wire_gate.__code__, namespace,
                             BASE.wire_gate.__name__, BASE.wire_gate.__defaults__)
    report = run(executable, full)
    report['uploaded_program_bits'] = sum(image['uploaded_bits'] for image in report['program_images'])
    report['uploaded_branch_records'] = 16 * len(report['program_images'])
    return report


def native_export(run, out, request):
    source = 'test/BufferedSharedBranchesExport.lean'
    run(['lake', 'build', 'Pinwheel:static'], 'native-library')
    run(['lake', 'env', 'lean', '-DwarningAsError=true', '-c', out / 'export.c', source], 'native-c')
    library = out / 'libpinwheel_Pinwheel.a'
    library.write_bytes((ROOT / '.lake/build/lib/libpinwheel_Pinwheel.a').read_bytes())
    compiler = run(['lake', 'env', 'leanc', '--version'], 'native-compiler').strip()
    executable = out / 'export'
    run(['lake', 'env', 'leanc', '-O3', '-o', executable, out / 'export.c', library], 'native-link')
    names = {'joint-generation-table-first', 'first-entry-second-input-selected',
             'reference-branch-loop-environment-19'}
    small = dict(schema=request['schema'], cases=[c for c in request['cases'] if c['name'] in names])
    BASE.require(len(small['cases']) == len(names), 'Missing native parity cases')
    path = out / 'parity-input.json'
    path.write_text(json.dumps(small, indent=2) + '\n')
    interpreted, native = out / 'interpreted', out / 'native'
    run(['lake', 'env', 'lean', '-DwarningAsError=true', '--run', source, path, interpreted], 'interpreter-parity')
    run([executable, path, native], 'native-parity')
    for name in ('vectors.json', 'core.mlir', 'assembly.json'):
        BASE.require((interpreted / name).read_bytes() == (native / name).read_bytes(),
                     'Native/interpreted exporter differs: ' + name)
    run([executable, out / 'input.json', out], 'export')
    return dict(compiler=compiler, cases=len(small['cases']),
        edges=sum(len(c['vectors']) for c in small['cases']),
        byte_identical=['vectors.json', 'core.mlir', 'assembly.json'],
        library_sha256=sha(library), executable_sha256=sha(executable), c_sha256=sha(out / 'export.c'),
        boundary='Finite interpreter/native parity; no universal native compiler or emitter proof.')


def structural_depth(data, top):
    """Count actual saved-netlist logic levels and sink pins, excluding clocks."""
    module = data['modules'][top]
    roots = {bit for p in module['ports'].values() if p['direction'] == 'input' for bit in p['bits']}
    drivers, loads, next_bits = {}, Counter(), []
    for cell in module['cells'].values():
        if cell['type'] == '$scopeinfo': continue
        pins, directions = cell['connections'], cell['port_directions']
        BASE.require(set(pins) == set(directions), 'Missing saved cell pin direction')
        inputs = [bit for pin, bits in pins.items() if directions[pin] == 'input'
                  and pin not in ('C', 'CLK', 'RESET_B') for bit in bits]
        outputs = [bit for pin, bits in pins.items() if directions[pin] == 'output' for bit in bits]
        loads.update(inputs)
        if cell['type'].startswith(('$_DFF', 'sg13cmos5l_df')):
            roots.update(outputs); next_bits.extend(pins['D'])
        else:
            for bit in outputs:
                BASE.require(type(bit) is int and bit not in drivers, 'Aliased combinational driver')
                drivers[bit] = inputs
    BASE.require(not set(drivers) & roots, 'Multiple input/state drivers')
    depths, visiting = {}, set()
    def depth(bit):
        if bit in depths: return depths[bit]
        if bit in roots or bit in ('0', '1'): return 0
        BASE.require(bit in drivers and bit not in visiting, 'Undriven signal or combinational cycle')
        visiting.add(bit)
        depths[bit] = 1 + max(map(depth, drivers[bit]), default=0)
        visiting.remove(bit)
        return depths[bit]
    for bit in drivers: depth(bit)
    public = {name: max(map(depth, p['bits']), default=0)
              for name, p in module['ports'].items() if p['direction'] == 'output'}
    return dict(next_state_depth=max(map(depth, next_bits), default=0), public_output_depth=public,
        maximum_data_signal_fanout=max((n for bit, n in loads.items() if type(bit) is int), default=0),
        boundary='Saved-cell logic levels and sink pins; no wire delay or electrical timing.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--tag', required=True)
    parser.add_argument('--pdk-root', type=Path)
    parser.add_argument('--smoke', action='store_true', help='Development wire subset; not full acceptance')
    args = parser.parse_args()
    out = fresh_directory(ROOT / 'build/buffered-shared-branches', args.tag)
    run = Commands(ROOT, out, default_timeout=1800)
    started = time.monotonic()
    report = dict(schema='pinwheel-buffered-shared-branches-results-v1', status='running',
        target='pinwheel-buffered-shared-branches32-v1', smoke=args.smoke, commands=run.records)
    try:
        pdk = stage_pdk(pdk_root=args.pdk_root)
        baseline = ROOT / 'physical/experiments/buffered-reactive-hardware-results.json'
        old = json.loads(baseline.read_text())
        baseline_report = ROOT / 'build/buffered-reactive-hardware/buffered-reactive-hardware-02/report.json'
        report['baseline_manifest_sha256'] = sha(baseline)
        report['baseline_report_sha256'] = sha(baseline_report)
        BASE.require(report['baseline_report_sha256'] ==
                     old['reports']['hardware']['sha256'], 'Changed accepted baseline report')
        old_report = json.loads(baseline_report.read_text())
        BASE.require(old_report['status'] == 'passed', 'Baseline hardware report did not pass')
        for name in ('Pinwheel/Hardware/Buffered/Reactive.lean', 'Pinwheel/Hardware/Buffered/ReactiveEmit.lean'):
            BASE.require(sha(ROOT / name) == old_report['source_sha256'][name], 'Inline core changed')
        sources = [ROOT / name for name in ('Pinwheel.lean', 'lean-toolchain', 'lakefile.toml',
            'lake-manifest.json', 'tools/technology-library.json', 'tools/hardware-toolchain.json',
            'physical/buffered_shared_branches_host_bridge.sv')]
        sources += sorted((ROOT / 'Pinwheel').rglob('*.lean'))
        sources += sorted((ROOT / 'test').glob('*.lean')) + sorted((ROOT / 'test').glob('test_*.py'))
        sources += sorted((ROOT / 'scripts').glob('*.py'))
        sources += [BASE.CIRCT, *[CAD / n for n in ('yosys', 'yosys-abc', 'iverilog', 'vvp')],
            *[CAD.parent / 'libexec' / n for n in ('yosys', 'yosys-abc', 'iverilog', 'vvp', 'ivl', 'ivlpp', 'realpath')],
            Path(pdk['library']), *map(Path, pdk['models']), CAD.parent / 'share/yosys/simcells.v']
        report['source_sha256'] = hashes = {str(p.relative_to(ROOT)): sha(p) for p in sources}
        tools = [BASE.CIRCT, *[CAD / n for n in ('yosys', 'yosys-abc', 'iverilog', 'vvp')],
            *[CAD.parent / 'libexec' / n for n in ('yosys', 'yosys-abc', 'iverilog', 'vvp', 'ivl', 'ivlpp', 'realpath')]]
        for tool in tools:
            name = str(tool.relative_to(ROOT))
            BASE.require(hashes[name] == old_report['source_sha256'][name], 'Comparison tool changed: ' + name)
        report['tools_match_baseline'] = True
        version = run(['lake', 'env', 'lean', '--version'], 'lean-version').strip()
        expected = (ROOT / 'lean-toolchain').read_text().strip().split(':v')[-1]
        BASE.require(bool(re.search(r'Lean \(version ' + re.escape(expected) + r'(?:,|\s)', version)),
                     'Lean version differs from repository pin')
        report['lean'] = version
        run(['lake', 'build'], 'build')
        audit = run(['lake', 'env', 'lean', '-DwarningAsError=true', 'test/ProofAudit.lean'], 'audit')
        counts = re.search(r'Pinwheel audit: (\d+) declarations, (\d+) theorems;', audit)
        BASE.require(counts is not None, 'Missing whole-library axiom audit')
        report['audit'] = dict(declarations=int(counts[1]), theorems=int(counts[2]))
        for suite in ('BufferedSharedBranches', 'BufferedSharedBranchesMemo', 'BufferedFetchDeadline'):
            output = run(['lake', 'env', 'lean', '-DwarningAsError=true', '--run', f'test/{suite}.lean'], suite)
            if suite == 'BufferedSharedBranchesMemo':
                counts = re.search(r'(\d+) fixtures; (\d+) Expr.bind evaluations; (\d+) byte-identical emitter comparisons', output)
                BASE.require(counts is not None, 'Missing memoized adapter parity counts')
                report['memo_adaptation'] = dict(fixtures=int(counts[1]), evaluations=int(counts[2]),
                    byte_identical_emitter_comparisons=int(counts[3]),
                    boundary='Finite executable adapter/Expr.bind and safe/native emitter parity; no universal native rewrite proof.')
        model = json.loads(run(['lake', 'env', 'lean', '-DwarningAsError=true', '--run',
                               'test/BufferedExport.lean'], 'model-export'))
        request = convert_request(BASE.command_cases(model))
        request['cases'] += upload_cases()
        (out / 'input.json').write_text(json.dumps(request, indent=2) + '\n')
        report['native_export'] = native_export(run, out, request)
        exported = json.loads((out / 'vectors.json').read_text())
        report['command_expectations'] = check_export(request, exported)
        assembly = json.loads((out / 'assembly.json').read_text())
        report['declared_state_bits'] = sum(r['width'] for r in assembly['registers'])
        BASE.require(report['declared_state_bits'] == 7183, 'Shared-bank declared geometry changed')
        text = run([BASE.CIRCT, out / 'core.mlir', '--canonicalize', '--lower-seq-to-sv',
            '--lower-hw-to-sv', '--hw-legalize-modules', '--export-verilog', '-o', '/dev/null'], 'circt')
        source = out / 'core.sv'; source.write_text(text)
        emitted = compile_rtl(run, out, source, 'emitted', bridge=BRIDGE,
                               testbench='buffered_reactive_host_bridge')
        report['emitted_control'] = BASE.replay_gate(emitted, exported)
        report['emitted_wire'] = wire_gate(emitted, full=not args.smoke)
        # Corrupt one row's dictionary reference in a branch-bearing fixture.
        mutation = deepcopy(exported)
        chosen = next(c for c in mutation['cases'] if c['name'] == 'reference-branch-loop-environment-19')
        row = next(v for v in chosen['vectors'] if v['command'].get('command') == 1 and
                   v['command'].get('address') == 0)
        row['command']['branch'] ^= 1
        try: BASE.replay_gate(emitted, mutation)
        except RuntimeError as error:
            BASE.require('public state mismatch' in str(error), 'Branch-index mutant failed outside state comparison')
        else: raise RuntimeError('Wrong branch-table reference was accepted')
        report['branch_index_mutation_rejected'] = True
        report['synthesis'] = synthesize(run, out, source, pdk_root=args.pdk_root,
            top=TOP, storage=STORAGE, bridge=BRIDGE, testbench='buffered_reactive_host_bridge')
        report['comparison'] = {}
        for variant, artifact in report['synthesis']['variants'].items():
            gate = Path(artifact['executable'])
            artifact['control_replay'] = BASE.replay_gate(gate, exported)
            artifact['wire_replay'] = wire_gate(gate)
            candidate = json.loads(Path(artifact['netlist_json']).with_name('readback.json').read_text())
            prior_path = Path(old_report['synthesis']['variants'][variant]['netlist_json']).with_name('readback.json')
            prior = json.loads(prior_path.read_text())
            old_artifact = old_report['synthesis']['variants'][variant]
            BASE.require(sha(Path(old_artifact['netlist_verilog'])) == old_artifact['netlist_sha256'], 'Changed baseline netlist')
            BASE.require(sha(prior_path) == old_artifact['readback_sha256'], 'Changed baseline readback')
            record = dict(baseline_metrics=old_artifact['metrics'], candidate_metrics=artifact['metrics'],
                baseline_depth=structural_depth(prior, 'pinwheel_buffered_reactive'),
                candidate_depth=structural_depth(candidate, TOP), baseline_readback_sha256=sha(prior_path))
            if variant == 'typical':
                BASE.require(old_report['synthesis']['pdk']['files_sha256'] == report['synthesis']['pdk']['files_sha256'],
                             'Technology pins differ between storage candidates')
                record['area_ratio'] = artifact['metrics']['standard_cell_area_um2'] / old_artifact['metrics']['standard_cell_area_um2']
            report['comparison'][variant] = record
        report['python'] = {}
        for label, flags in (('python', []), ('python-optimized', ['-O'])):
            output = run([sys.executable, *flags, '-B', '-m', 'unittest', 'discover', '-s', 'test', '-p', 'test_*.py'], label)
            count = re.search(r'Ran (\d+) tests', output)
            skipped = re.search(r'skipped=(\d+)', output)
            BASE.require(count is not None, 'Missing Python regression count')
            report['python'][label] = dict(total=int(count[1]), skipped=int(skipped[1]) if skipped else 0)
        for name, digest in hashes.items(): BASE.require(sha(ROOT / name) == digest, 'Frozen input changed: ' + name)
        report.update(status='passed', inputs_unchanged=True, elapsed_seconds=round(time.monotonic()-started, 3),
            boundary='Separate 16-descriptor combinational bank, shared reactive core, local mapped-state equations, '
            'finite commands and SPI/JTAG/I2C wire witnesses; arbitrary-state saved mapping checks. '
            'No full loader/refinement proof, synchronous SRAM implementation, serial package, routed timing or physical qualification.')
        report['artifact_sha256'] = {str(p.relative_to(out)): sha(p) for p in out.rglob('*')
            if p.is_file() and p.name != 'report.json'}
    except BaseException as error:
        report.update(status='failed', error=str(error)); raise
    finally:
        (out / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print('Shared branch storage gate passed: ' + str(out / 'report.json'), flush=True)


if __name__ == '__main__':
    main()
