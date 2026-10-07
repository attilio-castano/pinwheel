#!/usr/bin/env python3
"""Check the opt-in buffered SRAM controller and its pinned macro binding.

Saved-state SAT compares the emitted controller with its mapped artifacts for
arbitrary Q inputs. Closed-loop typed/RTL replays establish finite availability
witnesses separately. Macro footprints are geometry, not routed chip timing.
"""
import argparse
from copy import deepcopy
import importlib.util
import json
from pathlib import Path
import re
import sys
import time
import types

from buffered_engine import BufferedBlock, BufferedEngine, BufferedInstruction, BufferedProgram
from buffered_hardware_synthesis import CAD, stage_pdk, synthesize
from buffered_shared_branches import lower_shared_branches
from buffered_shared_branches_export import supervise, strict_json
from buffered_sram_hardware import (DECLARED_CONTROLLER_STATE_BITS, FORMAT,
    BufferedSramHardwareHost)
from pinwheel_buffers import TransferSlot
from validation_run import Commands, fresh_directory, sha

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location('shared_sram_predecessor_gate',
    ROOT / 'scripts/check-buffered-shared-branches.py')
SHARED = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(SHARED)
BASE = SHARED.BASE
TOP = 'pinwheel_buffered_shared_branches_sram'
CONTROLLER = TOP + '_controller'
MEMORY = ROOT / 'physical/buffered_sram_memory.sv'
WRAPPER = ROOT / 'physical/buffered_sram_wrapper.sv'
BRIDGE = ROOT / 'physical/buffered_sram_host_bridge.sv'
MACRO = 'RM_IHPSG13_1P_64x64_c2_bm_bist'
VIEWS = ROOT / 'build/storage/macros'
CORE_MODEL = VIEWS / 'RM_IHPSG13_1P_core_behavioral_bm_bist.v'
STORAGE = dict(metadata=[(f'r_metadata{k}', 28) for k in range(64)],
    branches=[(f'r_branch{k}', 56) for k in range(16)],
    row_coverage=[('r_written', 64)], branch_coverage=[('r_branch_written', 16)],
    tx=[('r_tx_data', 32)], rx=[('r_rx_data', 32)], start=[('r_start_word', 64)])


def oracle_subset(expected, request):
    cases = expected.get('cases')
    BASE.require(type(cases) is list, 'Missing independent oracle cases')
    names = [c.get('name') for c in cases]
    BASE.require(len(names) == len(set(names)), 'Duplicate independent oracle case')
    by_name = {c['name']: c for c in cases}
    wanted = [c['name'] for c in request['cases']]
    BASE.require(all(n in by_name for n in wanted), 'Missing independent oracle case')
    return dict(schema=expected['schema'], cases=[by_name[n] for n in wanted])


def check_export(request, exported, expected):
    """Check independent partial expectations and every frozen public field."""
    report = SHARED.check_export(request, exported)
    oracle = oracle_subset(expected, request)
    BASE.require(strict_json(exported) == strict_json(oracle),
                 'Closed-loop SRAM public vectors differ from the independent shared-bank oracle')
    report['all_public_field_comparisons'] = report['edges'] * len(BASE.STATE_WIDTHS)
    return report


def accepted_baseline():
    manifest = ROOT / 'physical/experiments/buffered-shared-branches-results.json'
    accepted = json.loads(manifest.read_text())
    receipt = accepted['reports']['hardware']
    path = ROOT / receipt['path']
    BASE.require(sha(path) == receipt['sha256'], 'Changed accepted shared-bank report')
    report = json.loads(path.read_text())
    BASE.require(accepted['status'] == report['status'] == 'passed' and not report['smoke'],
                 'Shared-bank predecessor is not full acceptance')
    for name, digest in accepted['accepted_artifact_sha256'].items():
        BASE.require(sha(ROOT / name) == digest, 'Changed accepted predecessor artifact: ' + name)
    for name in ('Pinwheel/Hardware/Buffered/Reactive.lean',
                 'Pinwheel/Hardware/Buffered/SharedBranches.lean',
                 'Pinwheel/Hardware/Buffered/SharedBranchProofs.lean',
                 'scripts/buffered_shared_branches.py', 'scripts/check-buffered-shared-branches.py'):
        BASE.require(sha(ROOT / name) == report['source_sha256'][name],
                     'Predecessor implementation changed: ' + name)
    directory = path.parent
    return accepted, report, directory, dict(manifest_sha256=sha(manifest),
        report_path=receipt['path'], report_sha256=sha(path),
        artifact_files=len(accepted['accepted_artifact_sha256']))


def macro_views():
    lock = json.loads((ROOT / 'tools/storage-macros.json').read_text())
    selected = [f'verilog/{MACRO}.v',
        'verilog/RM_IHPSG13_1P_core_behavioral_bm_bist.v', f'lef/{MACRO}.lef',
        f'lib/{MACRO}_typ_1p20V_25C.lib']
    paths = [VIEWS / Path(name).name for name in selected]
    for name, path in zip(selected, paths, strict=True):
        BASE.require(sha(path) == lock['files_sha256'][name], 'Unpinned SRAM view: ' + name)
    lef = paths[2].read_text()
    sizes = re.findall(r'\bSIZE\s+([\d.]+)\s+BY\s+([\d.]+)', lef)
    BASE.require(len(sizes) == 1, 'Ambiguous pinned macro geometry')
    width, height = map(float, sizes[0])
    return paths, dict(macro=MACRO, copies=2, width_um=width, height_um=height,
        macro_footprint_um2=round(2 * width * height, 4),
        source_sha256={str(p.relative_to(ROOT)): sha(p) for p in paths},
        boundary='Two pinned 64x64 macro footprints; no halo, clock tree, routing or electrical qualification.')


def directed_cases():
    """Additional source-engine witnesses for uninterrupted branch deadlines."""
    cases = []
    for trial in range(4):
        vectors, checks = [], []
        def edge(raw=3, expect=None, **command):
            vectors.append(dict(command=command, raw_inputs=raw))
            if expect is not None:
                checks.append(dict(edge=len(vectors) - 1, state=expect))
        program = BufferedProgram((), schedule=BufferedBlock(tuple(
            BufferedInstruction('checked', levels=k+1, enabled=7,
                terminal_capture=(trial % 2, 0), finish=(0, (k+1) % 3, (k+2) % 3))
            for k in range(3))), declared_tx_bits=0, declared_rx_bits=0, max_rx_bits=0)
        image = lower_shared_branches(program)
        edge(initialize=1)
        for k, branch in enumerate(image.branch_table): edge(command=6, address=k, branch=branch)
        for k, (word, control, ref) in enumerate(zip(image.words, image.controls,
                image.branch_indices, strict=True)):
            edge(command=1, address=k, word=word, control=control, branch=ref)
        edge(command=2, count=3, virtual_span=3)
        slot = TransferSlot(tx_capacity_bits=32, rx_capacity_bits=32)
        identity = slot.begin(program.key, (), 0)
        model = BufferedEngine(slot, identity, program)
        # START samples raw into stage1 but enters using the pre-edge stage2.
        model._first, model._second = trial, 3
        def snapshot():
            return dict(control='stopped' if model.done else model.mode,
                stop_reason=model.mode if model.done else None,
                remaining=model.remaining, wait_left=model.wait_left,
                samples=list(model.samples), pc=model.pc, levels=model.levels,
                enabled=model.enabled, tx_consumed_bits=slot._tx_consumed,
                rx_bits=list(slot._rx), sampler_first=model._first, sampler_second=model._second)
        edge(raw=trial, command=3, expected_generation=1,
             expect=BASE.model_state(program, snapshot()))
        for cycle in range(128):
            raw = (cycle + trial) % 4
            model.step(raw)
            BASE.require(not model.done and model.remaining == 0,
                         'Consecutive CHECKED fixture stopped or inserted an edge')
            edge(raw=raw, expect=BASE.model_state(program, snapshot()))
        edge(command=7, expect=dict(valid=0, busy=0, retained=0, phase=0))
        cases.append(dict(name=f'sram-consecutive-one-cycle-branches-{trial}',
            vectors=vectors, checks=checks))
    # Full-width physical addressing plus row-zero mirror replacement; the last
    # WRITE0 must supply START, while all 64 independently distinctive rows run.
    vectors, checks = [], []
    def edge(raw=3, expect=None, **command):
        vectors.append(dict(command=command, raw_inputs=raw))
        if expect is not None: checks.append(dict(edge=len(vectors)-1, state=expect))
    edge(initialize=1)
    for k in range(16): edge(command=6, address=k)
    edge(command=1, address=0, word=3)
    for k in range(64):
        edge(command=1, address=k, word=3 if k == 63 else (k % 8) * 8 + 7 * 64)
    edge(command=2, count=64, virtual_span=64)
    edge(command=3, expected_generation=1, expect=dict(pc=0, levels=0, phase=1))
    for k in range(1, 63): edge(expect=dict(pc=k, levels=k % 8, phase=1))
    edge(expect=dict(pc=0, phase=5, retained=1))
    edge(command=4, expected_generation=1, expected_transfer=1)
    # New short image has a nonzero descriptor at dictionary zero. A stale
    # physical row1 must not have effects when the declared count is only one.
    for k in range(16): edge(command=6, address=k, branch=1 | ((2 + (1 << 11)) << 6) if k == 0 else 0)
    edge(command=1, address=0, word=6, branch=0)
    edge(command=2, count=1, virtual_span=2)
    edge(command=3, expected_generation=2, expect=dict(pc=0, phase=3))
    edge(expect=dict(pc=0, phase=7, retained=1, rx_length=0, tx_consumed=0))
    cases.append(dict(name='sram-all-addresses-start-mirror-short-reload', vectors=vectors, checks=checks))
    return dict(schema='pinwheel-buffered-shared-branches-input-v1', cases=cases)


def prepare_oracle(run, out, directory):
    request = json.loads((directory / 'input.json').read_text())
    expected = json.loads((directory / 'vectors.json').read_text())
    extra = directed_cases()
    path = out / 'directed-input.json'; path.write_text(json.dumps(extra, indent=2) + '\n')
    target = out / 'directed-oracle'
    target.mkdir()
    shard_report = target / 'export-shards/report.json'
    try:
        run([sys.executable, '-B', ROOT / 'scripts/buffered_shared_branches_export.py',
            directory / 'export', path, target, directory, '--checker',
            ROOT / 'scripts/check-buffered-shared-branches.py'],
            'accepted-shared-directed-oracle', timeout=1805)
    finally:
        if shard_report.exists(): run.records.extend(json.loads(shard_report.read_text())['commands'])
    for name in ('core.mlir', 'assembly.json'):
        BASE.require((target / name).read_bytes() == (directory / name).read_bytes(),
                     'Accepted directed exporter changed its core artifact: ' + name)
    additional = json.loads((target / 'vectors.json').read_text())
    SHARED.check_export(extra, additional)
    request['cases'] += extra['cases']; expected['cases'] += additional['cases']
    SHARED.check_export(request, expected)
    (out / 'input.json').write_text(json.dumps(request, indent=2) + '\n')
    oracle = out / 'oracle.json'; oracle.write_text(json.dumps(expected, indent=2) + '\n')
    return request, expected, oracle


def native_export(run, out, request, expected, oracle):
    source = 'test/BufferedSramExport.lean'
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
    BASE.require(len(small['cases']) == len(names), 'Missing native parity case')
    path = out / 'parity-input.json'; path.write_text(json.dumps(small, indent=2) + '\n')
    interpreted, native = out / 'interpreted', out / 'native'
    run(['lake', 'env', 'lean', '-DwarningAsError=true', '--run', source, path, interpreted], 'interpreter-parity')
    run([executable, path, native], 'native-parity')
    for name in ('vectors.json', 'core.mlir', 'assembly.json'):
        BASE.require((interpreted / name).read_bytes() == (native / name).read_bytes(),
                     'Native/interpreted SRAM exporter differs: ' + name)
    check_export(small, json.loads((native / 'vectors.json').read_text()), expected)
    shard_path = out / 'export-shards/report.json'
    try:
        run([sys.executable, '-B', Path(__file__), '--supervise-export', executable,
            out / 'input.json', out, native, '--oracle', oracle,
            '--oracle-sha256', sha(oracle)], 'export', timeout=1805)
    finally:
        if shard_path.exists(): run.records.extend(json.loads(shard_path.read_text())['commands'])
    shards = json.loads(shard_path.read_text())
    BASE.require(shards['status'] == 'passed' and shards['cases'] == len(request['cases']) and
        shards['edges'] == sum(len(c['vectors']) for c in request['cases']) and
        all(c.get('direct_child_reaped') and c.get('exit_code') == 0 for c in shards['commands']),
        'Incomplete supervised SRAM export')
    return dict(compiler=compiler, cases=len(small['cases']),
        edges=sum(len(c['vectors']) for c in small['cases']),
        byte_identical=['vectors.json', 'core.mlir', 'assembly.json'],
        full_export_shards=shards, library_sha256=sha(library),
        executable_sha256=sha(executable), c_sha256=sha(out / 'export.c'),
        boundary='Actual closed-loop typed SRAM model; finite old/new all-public-state and native/interpreter parity. No compiler/emitter proof.')


def compile_complete(run, out, controller, label, models, *, memory=MEMORY, bridge=BRIDGE, cells=()):
    executable = Path(out) / (label + '.vvp')
    run([CAD / 'iverilog', '-g2012', '-DFUNCTIONAL', '-s', 'buffered_reactive_host_bridge',
        '-o', executable, controller, WRAPPER, memory, bridge, *models, *cells], label + '-compile')
    return executable


def composite_bridge(out, models):
    """Supply the unchanged macro binding to the existing controller mapper."""
    path = Path(out) / 'controller-macro-bridge.sv'
    path.write_text('\n'.join(p.read_text() for p in (WRAPPER, MEMORY, *models, BRIDGE)))
    return path


def wire_gate(executable, full=False):
    namespace = dict(BASE.wire_gate.__globals__, BufferedReactiveHardwareHost=BufferedSramHardwareHost)
    gate = types.FunctionType(BASE.wire_gate.__code__, namespace,
        BASE.wire_gate.__name__, BASE.wire_gate.__defaults__)
    report = gate(executable, full)
    report['uploaded_program_bits'] = sum(image['uploaded_bits'] for image in report['program_images'])
    report['uploaded_branch_records'] = 16 * len(report['program_images'])
    return report


def binding_readback(data):
    """Inspect the complete, flattened saved binding rather than source text."""
    module = data['modules'][TOP]
    public = {name: ('input', width) for name, width in
        dict(clk=1, raw_inputs=2, **BASE.COMMAND_FIELDS).items()}
    public.update({name: ('output', width) for name, width in BASE.STATE_WIDTHS.items()})
    ports = module.get('ports', {})
    BASE.require(set(ports) == set(public) and all(
        ports[name].get('direction') == direction and
        type(ports[name].get('bits')) is list and len(ports[name]['bits']) == width
        for name, (direction, width) in public.items()),
        'Changed complete SRAM public wrapper boundary')
    def foreign_blackbox(cell):
        attributes = data['modules'].get(cell['type'], {}).get('attributes', {})
        opaque = any(int(attributes.get(name, '0'), 2) != 0
            if type(attributes.get(name, '0')) is str else bool(attributes.get(name, 0))
            for name in ('blackbox', 'whitebox'))
        return opaque and not cell['type'].startswith('sg13cmos5l_')
    macros = {name: c for name, c in module['cells'].items()
        if c['type'].startswith('RM_IHPSG13_') or foreign_blackbox(c)}
    BASE.require(set(macros) == {'memory.storage0', 'memory.storage1'}, 'Wrong SRAM macro instances')
    BASE.require(all(cell['type'] == MACRO for cell in macros.values()), 'Wrong SRAM macro type')
    def net(name, width):
        bits = module['netnames'].get(name, {}).get('bits')
        BASE.require(type(bits) is list and len(bits) == width, 'Missing complete SRAM wire: ' + name)
        return bits
    interface = dict((name, width) for name, (_, width) in public.items())
    interface.update(mem_addr0=6, mem_addr1=6, mem_data=64, mem_write=1,
        mem_read=1, mem_q0=64, mem_q1=64)
    for name, width in interface.items():
        BASE.require(net(name, width) == net('controller.' + name, width),
                     'Changed transparent SRAM controller wire: ' + name)
        if name in public:
            BASE.require(ports[name]['bits'] == net(name, width),
                         'Changed transparent SRAM public port wire: ' + name)
    BASE.require(all(cell['type'] == '$scopeinfo' or name in macros or name.startswith('controller.')
        for name, cell in module['cells'].items()), 'Circuitry outside controller and SRAM macros')
    common = dict(A_CLK=net('clk', 1), A_MEN=['1'], A_DLY=['1'],
        A_WEN=net('mem_write', 1), A_REN=net('mem_read', 1), A_DIN=net('mem_data', 64),
        A_BM=['1'] * 64, A_BIST_CLK=['0'], A_BIST_EN=['0'], A_BIST_MEN=['0'],
        A_BIST_WEN=['0'], A_BIST_REN=['0'], A_BIST_ADDR=['0'] * 6,
        A_BIST_DIN=['0'] * 64, A_BIST_BM=['0'] * 64)
    for k in range(2):
        expected = dict(common, A_ADDR=net(f'mem_addr{k}', 6), A_DOUT=net(f'mem_q{k}', 64))
        BASE.require(macros[f'memory.storage{k}']['connections'] == expected,
                     'Changed complete SRAM macro port binding: ' + str(k))
        BASE.require(macros[f'memory.storage{k}'].get('port_directions') ==
            {name: 'output' if name == 'A_DOUT' else 'input' for name in expected},
            'Changed complete SRAM macro port directions: ' + str(k))
    return dict(macros=2, macro=MACRO, ports_per_macro=len(common)+2,
        full_word_broadcast=True, independent_addresses=True, bist_disabled=True,
        public_input_ports=sum(direction == 'input' for direction, _ in public.values()),
        public_output_ports=sum(direction == 'output' for direction, _ in public.values()),
        response_edge='Macro Q connects directly to controller input; no wrapper response register.')


def read_complete_binding(run, out, controller, label, library=None):
    path = Path(out) / (label + '-binding.json')
    lines = [f'read_liberty -lib {VIEWS}/{MACRO}_typ_1p20V_25C.lib']
    if library is not None: lines.append(f'read_liberty -lib {library}')
    lines += [f'read_verilog -sv {controller} {WRAPPER} {MEMORY}',
        f'hierarchy -check -top {TOP}', 'proc', 'flatten', 'opt_clean', 'check -assert',
        f'write_json {path}']
    script = Path(out) / (label + '-binding.ys'); script.write_text('\n'.join(lines) + '\n')
    run([CAD / 'yosys', '-Q', '-T', '-s', script], label + '-binding-readback')
    return dict(binding_readback(json.loads(path.read_text())), readback_sha256=sha(path))


def poison_bridge(out, seed):
    text = BRIDGE.read_text()
    anchor = '  pinwheel_buffered_shared_branches_sram dut(.*);'
    BASE.require(text.count(anchor) == 1, 'Missing SRAM poison fixture insertion anchor')
    statements = ['  // Test-only arbitrary initial contents; no expected-value injection.',
                  '  integer poison_index;', '  initial begin']
    for k in range(2):
        core = f'dut.memory.storage{k}.i_SRAM_1P_behavioral_bm_bist'
        constant = (0x96A53CC36A5AC33C ^ (seed * 0x1111111111111111) ^ (k * 0xFFFFFFFFFFFFFFFF)) & ((1 << 64)-1)
        statements += [f'    {core}.dr_r = 64\'h{constant:016x};',
            '    for (poison_index = 0; poison_index < 64; poison_index = poison_index + 1)',
            f'      {core}.memory[poison_index] = 64\'h{constant:016x} ^ poison_index;']
    statements.append('  end')
    path = Path(out) / f'poison-bridge-{seed}.sv'
    path.write_text(text.replace(anchor, anchor + '\n' + '\n'.join(statements)))
    return path


def binding_mutants(out):
    text = MEMORY.read_text()
    anchor = f'  {MACRO} storage1 ('
    BASE.require(text.count(anchor) == 1, 'Missing SRAM replica mutation anchor')
    before, after = text.split(anchor)
    mutations = dict(single_response=('.A_ADDR(mem_addr1)', '.A_ADDR(mem_addr0)'),
        no_broadcast=('.A_WEN(mem_write)', ".A_WEN(1'b0)"),
        incomplete_word=('.A_BM(64\'hffffffffffffffff)', ".A_BM(64'h7fffffffffffffff)"))
    result = {}
    for name, (old, new) in mutations.items():
        BASE.require(after.count(old) == 1, 'Ambiguous SRAM negative control: ' + name)
        path = Path(out) / (name + '-memory.sv')
        path.write_text(before + anchor + after.replace(old, new))
        result[name] = path
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--tag')
    parser.add_argument('--pdk-root', type=Path)
    parser.add_argument('--smoke', action='store_true', help='Development wire subset; not acceptance')
    parser.add_argument('--supervise-export', nargs=4, type=Path)
    parser.add_argument('--oracle', type=Path)
    parser.add_argument('--oracle-sha256')
    args = parser.parse_args()
    if args.supervise_export:
        BASE.require(args.oracle is not None and sha(args.oracle) == args.oracle_sha256,
                     'Missing or changed SRAM export oracle')
        oracle = json.loads(args.oracle.read_text())
        supervise(*args.supervise_export,
            validator=lambda request, vectors: check_export(request, vectors, oracle))
        return
    if not args.tag: parser.error('--tag is required')
    out = fresh_directory(ROOT / 'build/buffered-sram', args.tag)
    run = Commands(ROOT, out, default_timeout=1800)
    report = dict(schema='pinwheel-buffered-sram-results-v1', target=FORMAT,
        status='running', smoke=args.smoke, commands=run.records)
    started = time.monotonic()
    try:
        accepted, prior, baseline_dir, report['baseline'] = accepted_baseline()
        paths, report['macro_geometry'] = macro_views()
        models = paths[:2]
        pdk = stage_pdk(pdk_root=args.pdk_root)
        BASE.require(pdk['files_sha256'] == prior['synthesis']['pdk']['files_sha256'],
                     'Comparison mapping library/models changed')
        sources = [ROOT / n for n in ('Pinwheel.lean', 'lean-toolchain', 'lakefile.toml',
            'lake-manifest.json', 'tools/storage-macros.json', 'tools/technology-library.json',
            'tools/hardware-toolchain.json')]
        sources += sorted((ROOT / 'Pinwheel').rglob('*.lean'))
        sources += sorted((ROOT / 'test').glob('*.lean')) + sorted((ROOT / 'test').glob('test_*.py'))
        sources += sorted((ROOT / 'test').glob('*.sv'))
        sources += sorted((ROOT / 'scripts').glob('*.py'))
        sources += [MEMORY, WRAPPER, BRIDGE, *paths, BASE.CIRCT,
            *[CAD / n for n in ('yosys', 'yosys-abc', 'iverilog', 'vvp')],
            *[CAD.parent / 'libexec' / n for n in ('yosys', 'yosys-abc', 'iverilog', 'vvp', 'ivl', 'ivlpp', 'realpath')],
            Path(pdk['library']), *map(Path, pdk['models']), CAD.parent / 'share/yosys/simcells.v']
        report['source_sha256'] = hashes = {str(p.relative_to(ROOT)): sha(p) for p in sources}
        for tool in [BASE.CIRCT, *[CAD / n for n in ('yosys', 'yosys-abc', 'iverilog', 'vvp')],
                *[CAD.parent / 'libexec' / n for n in ('yosys', 'yosys-abc', 'iverilog', 'vvp', 'ivl', 'ivlpp', 'realpath')]]:
            BASE.require(hashes[str(tool.relative_to(ROOT))] == prior['source_sha256'][str(tool.relative_to(ROOT))],
                         'Comparison tool changed')
        version = run(['lake', 'env', 'lean', '--version'], 'lean-version').strip()
        expected_version = (ROOT / 'lean-toolchain').read_text().strip().split(':v')[-1]
        BASE.require(bool(re.search(r'Lean \(version ' + re.escape(expected_version) + r'(?:,|\s)', version)),
                     'Lean version differs from repository pin')
        report['lean'] = version
        run(['lake', 'build'], 'build')
        audit = run(['lake', 'env', 'lean', '-DwarningAsError=true', 'test/ProofAudit.lean'], 'audit')
        count = re.search(r'Pinwheel audit: (\d+) declarations, (\d+) theorems;', audit)
        BASE.require(count is not None, 'Missing whole-library axiom audit')
        report['audit'] = dict(declarations=int(count[1]), theorems=int(count[2]))
        for suite in ('BufferedSramHardware', 'BufferedSramCandidates', 'BufferedSramMemoBind'):
            log = run(['lake', 'env', 'lean', '-DwarningAsError=true', '--run', f'test/{suite}.lean'], suite)
            if suite == 'BufferedSramMemoBind':
                finite = re.search(r'(\d+) fixtures; (\d+) Expr.bind evaluations; (\d+) byte-identical emitter comparisons', log)
                composed = re.search(r'(\d+) fixtures; (\d+) two-pass Expr.bind evaluations', log)
                BASE.require(finite is not None and composed is not None, 'Missing memo bind parity counts')
                report['memo_bind'] = dict(fixtures=int(finite[1]), evaluations=int(finite[2]),
                    byte_identical_emitter_comparisons=int(finite[3]),
                    composed_fixtures=int(composed[1]), composed_evaluations=int(composed[2]),
                    boundary='Finite public/direct executable substitution and emitter parity; no universal native bind proof.')
        request, oracle, oracle_path = prepare_oracle(run, out, baseline_dir)
        report['native_export'] = native_export(run, out, request, oracle, oracle_path)
        exported = json.loads((out / 'vectors.json').read_text())
        report['command_expectations'] = check_export(request, exported, oracle)
        description = json.loads((out / 'assembly.json').read_text())
        report['declared_controller_state_bits'] = sum(r['width'] for r in description['registers'])
        BASE.require(description['module'] == CONTROLLER and
            report['declared_controller_state_bits'] == DECLARED_CONTROLLER_STATE_BITS,
            'SRAM controller declared geometry changed')
        rtl = run([BASE.CIRCT, out / 'core.mlir', '--canonicalize', '--lower-seq-to-sv',
            '--lower-hw-to-sv', '--hw-legalize-modules', '--export-verilog', '-o', '/dev/null'], 'circt')
        source = out / 'core.sv'; source.write_text(rtl)
        executable = compile_complete(run, out, source, 'emitted', models)
        report['emitted_control'] = BASE.replay_gate(executable, exported)
        report['emitted_wire'] = wire_gate(executable, full=not args.smoke)
        report['emitted_binding'] = read_complete_binding(run, out, source, 'emitted')
        report['arbitrary_initial_witnesses'] = []
        for seed in (1, 7):
            bridge = poison_bridge(out, seed)
            poisoned = compile_complete(run, out, source, f'poison-{seed}', models, bridge=bridge)
            report['arbitrary_initial_witnesses'].append(dict(seed=seed, replay=BASE.replay_gate(poisoned, exported)))
        report['negative_controls'] = {}
        for name, memory in binding_mutants(out).items():
            mutant = compile_complete(run, out, source, name, models, memory=memory)
            try: BASE.replay_gate(mutant, exported)
            except RuntimeError as error:
                BASE.require(any(message in str(error) for message in
                    ('public state mismatch', 'Malformed buffered RTL observation',
                     'Unknown/contention on reactive resolved pads')),
                    'SRAM negative control failed outside public observation: ' + str(error))
                report['negative_controls'][name] = dict(rejected=True, reason=str(error))
            else: raise RuntimeError('SRAM binding negative control was accepted: ' + name)
        # Synthesize only controller logic: Q remains an unrestricted input in
        # the saved mapping SAT cut. Closed-loop memory is tested afterwards.
        report['synthesis'] = synthesize(run, out, source, pdk_root=args.pdk_root,
            top=CONTROLLER, storage=STORAGE, bridge=composite_bridge(out, models),
            testbench='buffered_reactive_host_bridge', equivalence=True)
        report['comparison'] = {}
        for name, result in report['synthesis']['variants'].items():
            target = Path(result['netlist_verilog']).parent
            cells = [Path(p) for p in result['simulation_models_sha256']]
            complete = compile_complete(run, target, Path(result['netlist_verilog']), name + '-complete', models, cells=cells)
            result['closed_loop_control'] = BASE.replay_gate(complete, exported)
            result['closed_loop_wire'] = wire_gate(complete)
            result['complete_binding'] = read_complete_binding(run, target,
                Path(result['netlist_verilog']), name, Path(pdk['library']) if name == 'typical' else None)
            saved = json.loads(Path(result['netlist_json']).with_name('readback.json').read_text())
            comparison = dict(controller_metrics=result['metrics'],
                controller_depth=SHARED.structural_depth(saved, CONTROLLER),
                baseline_metrics=prior['synthesis']['variants'][name]['metrics'],
                baseline_depth=prior['comparison'][name]['candidate_depth'])
            if name == 'typical':
                comparison['controller_and_macro_footprint_um2'] = round(
                    result['metrics']['standard_cell_area_um2'] + report['macro_geometry']['macro_footprint_um2'], 4)
                comparison['area_ratio'] = comparison['controller_and_macro_footprint_um2'] / comparison['baseline_metrics']['standard_cell_area_um2']
            report['comparison'][name] = comparison
        report['python'] = {}
        for label, flags in (('python', []), ('python-optimized', ['-O'])):
            log = run([sys.executable, *flags, '-B', '-m', 'unittest', 'discover', '-s', 'test', '-p', 'test_*.py'], label)
            count = re.search(r'Ran (\d+) tests', log)
            BASE.require(count is not None, 'Missing Python regression count')
            skipped = re.search(r'skipped=(\d+)', log)
            report['python'][label] = dict(total=int(count[1]), skipped=int(skipped[1]) if skipped else 0)
        for name, digest in hashes.items(): BASE.require(sha(ROOT / name) == digest, 'Frozen input changed: ' + name)
        report.update(status='passed', inputs_unchanged=True,
            elapsed_seconds=round(time.monotonic()-started, 3),
            boundary='Two replicated pinned latency-one instruction macros, register metadata/dictionary, START mirror, '
            'actual typed closed-loop model and finite all-public-state command/wire comparisons. '
            'Saved mapping SAT covers the controller with unrestricted Q inputs, separately from memory availability. '
            'No serial package, routed timing, CDC/electrical macro qualification or physical closure.')
        report['artifact_sha256'] = {str(p.relative_to(out)): sha(p) for p in out.rglob('*')
            if p.is_file() and p.name != 'report.json'}
    except BaseException as error:
        report.update(status='failed', error=str(error)); raise
    finally:
        (out / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print('Buffered SRAM gate passed: ' + str(out / 'report.json'), flush=True)


if __name__ == '__main__':
    main()
