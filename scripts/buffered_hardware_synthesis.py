"""Saved generic/CMOS5L synthesis evidence for the opt-in buffered circuit.

No retiming, physical flow or old target is changed. Area is the sum of mapped
standard-cell Liberty areas. Optional exact state cuts compare emitted RTL with
its saved gate artifacts for arbitrary inputs and represented register values.
"""
from collections import Counter
from copy import deepcopy
import json
from pathlib import Path

from tiled_chip import project_pruned_state, state_cut
from validation_run import sha


ROOT = Path(__file__).resolve().parents[1]
CAD = ROOT / 'build/tools/oss-cad-suite/bin'
TOP = 'pinwheel_buffered_linear'
LIBRARY = 'sg13cmos5l_stdcell_typ_1p20V_25C.lib'
MODEL_REVISION = '607e18d4bd9214a52575c194b4181ef449f9252f'
MODEL_SHA256 = {
    'sg13cmos5l_stdcell.v': 'b0adbc84c8f78feb01c3d8d9d55e9818ee6502347d336f3a1f846e6a5d64e0a2',
    'sg13cmos5l_udp.v': '5491a3edf7468792b5222e7abe057e0583a407c01b2086d4fd44a55b6cf88055',
}
RECOVERED_PDK = Path('/Users/attiliocastano/.codex/worktrees/a2b1/pinwheel/build/recovery/pdk/'
                     'ihp-sg13cmos5l/libs.ref/sg13cmos5l_stdcell')


def write(path, value):
    Path(path).write_text(json.dumps(value, indent=2) + '\n')


def stage_pdk(destination=None, pdk_root=None):
    """Copy exact pinned local files; preserve any already staged identical file."""
    destination = ROOT / 'build/buffered-hardware/pdk' if destination is None else Path(destination)
    lock = json.loads((ROOT / 'tools/technology-library.json').read_text())
    if lock['commit'] != MODEL_REVISION:
        raise ValueError('Update the buffered functional model pins for the selected library revision')
    libraries = {item['name']: item['sha256'] for item in lock['files']}
    expected = {LIBRARY: libraries[LIBRARY], **MODEL_SHA256}

    def receipt():
        return dict(revision=MODEL_REVISION, directory=str(destination),
                    files_sha256=expected, library=str(destination / LIBRARY),
                    models=[str(destination / name) for name in MODEL_SHA256])

    if pdk_root is None and all((destination / name).is_file() for name in expected):
        for name, digest in expected.items():
            if sha(destination / name) != digest:
                raise ValueError('Preserve and inspect the mismatched staged buffered PDK file: ' + name)
        return receipt()
    pdk_root = RECOVERED_PDK if pdk_root is None else Path(pdk_root)
    files = {LIBRARY: (pdk_root / 'lib' / LIBRARY, libraries[LIBRARY])}
    files.update({name: (pdk_root / 'verilog' / name, digest)
                  for name, digest in MODEL_SHA256.items()})
    # Verify every source before making the first copy.
    for name, (source, digest) in files.items():
        if sha(source) != digest:
            raise ValueError('Unpinned local buffered PDK file: ' + name)
    destination.mkdir(parents=True, exist_ok=True)
    for name, (source, digest) in files.items():
        target = destination / name
        if target.exists():
            if sha(target) != digest:
                raise ValueError('Preserve and inspect the mismatched staged buffered PDK file: ' + name)
        else:
            target.write_bytes(source.read_bytes())
    return receipt()


def resource_metrics(data, *, mapped=False):
    """Count saved actual cells, their state bits and mapped area fail closed."""
    module = data['modules'][TOP]
    cells = {name: cell for name, cell in module['cells'].items() if cell['type'] != '$scopeinfo'}
    counts = Counter(cell['type'] for cell in cells.values())
    sequential = {name: cell for name, cell in cells.items()
                  if cell['type'].startswith('sg13cmos5l_df' if mapped else '$_DFF')}
    roots = []
    for cell in sequential.values():
        pin = 'Q'
        bits = cell['connections'].get(pin)
        if bits is None or any(type(bit) is not int for bit in bits):
            raise ValueError('Invalid saved buffered state cell')
        roots.extend(bits)
    if len(set(roots)) != len(roots):
        raise ValueError('Aliased saved buffered state outputs')
    for cell in cells.values():
        if cell['type'].startswith(('$dff', '$adff', '$sdff', '$_DFFE')):
            raise ValueError('Normalize all saved buffered sequential cell forms')
    named = {}
    root_set = set(roots)
    for label, names in [('tx', ['r_tx_data']), ('rx', ['r_rx_data']),
                         ('program_bank', [f'r_word{row}' for row in range(128)]),
                         ('written_mask', ['r_written'])]:
        bits = [bit for name in names for bit in module['netnames'][name]['bits']]
        named[label] = dict(logical_bits=len(bits), physical_state_bits=len(set(bits) & root_set))
    result = dict(cells=len(cells), cell_types=dict(sorted(counts.items())),
                  flip_flops=len(sequential), physical_state_bits=len(roots), named_storage=named)
    if mapped:
        areas = {}
        for kind in counts:
            if not kind.startswith('sg13cmos5l_'):
                raise ValueError('Unmapped cell in the saved CMOS5L buffered artifact: ' + kind)
            area = float(data['modules'][kind]['attributes']['area'])
            if not area > 0:
                raise ValueError('Invalid mapped buffered cell area')
            areas[kind] = area
        result['standard_cell_area_um2'] = round(sum(areas[kind] * count
                                                   for kind, count in counts.items()), 4)
        result['sequential_area_um2'] = round(sum(areas[cell['type']]
                                                for cell in sequential.values()), 4)
    return result


def compile_rtl(run, out, source, label, *, cells=()):
    executable = Path(out) / (label + '.vvp')
    run([CAD / 'iverilog', '-g2012', '-DFUNCTIONAL', '-s', 'buffered_hardware_tb',
         '-o', executable, source, ROOT / 'test/buffered_hardware_tb.sv', *cells],
        label + '-compile')
    return executable


def synthesize(run, out, source, *, description=None, pdk_root=None, equivalence=True):
    out, source = Path(out), Path(source)
    pdk = stage_pdk(pdk_root=pdk_root)
    library = Path(pdk['library'])
    source_digest = sha(source)
    if description is None:
        description = json.loads((source.parent / 'assembly.json').read_text())
    if description.get('module') != TOP:
        raise ValueError('Wrong buffered circuit state description')

    def yosys(label, lines, *, reject=None):
        script = out / (label + '.ys')
        script.write_text('\n'.join(lines) + '\n')
        return run([CAD / 'yosys', '-Q', '-T', '-s', script], label,
                   timeout=900, reject=reject)

    result = dict(pdk=pdk, source_sha256=source_digest, variants={},
        boundary='Saved generic and typical CMOS5L standard-cell artifacts; no retiming, '
                 'pads, serial transport, SRAM integration, clock tree, placement, routing, '
                 'parasitics or timing qualification.')
    yosys('synthesis-source-readback', [f'read_verilog -sv {source}',
        f'synth -top {TOP} -flatten -noabc', 'dffunmap', 'clean', 'check -assert',
        f'write_json {out}/source-readback.json'])
    for variant in ('generic', 'typical'):
        target = out / variant
        target.mkdir(exist_ok=False)
        lines = [f'read_verilog -sv {source}', f'synth -top {TOP} -flatten -noabc',
                 'dffunmap']
        if variant == 'typical':
            constraint = target / 'abc.constr'
            constraint.write_text('set_driving_cell sg13cmos5l_buf_2\nset_load 10\n')
            lines += [f'dfflibmap -liberty {library}',
                      f'abc -liberty {library} -constr {constraint} -D 10000',
                      f'read_liberty -lib {library}']
        else:
            lines.append('abc')
        lines += ['clean', 'check -assert', 'stat' + (f' -liberty {library}'
                  if variant == 'typical' else ''), f'write_json {target}/netlist.json',
                  f'write_verilog -noattr' + (' -noexpr' if variant == 'typical' else '') +
                  f' {target}/netlist.v']
        yosys('synthesis-' + variant, lines)
        data = json.loads((target / 'netlist.json').read_text())
        metrics = resource_metrics(data, mapped=variant == 'typical')
        readback = ([f'read_liberty -lib {library}'] if variant == 'typical' else [])
        readback += [f'read_verilog -sv {target}/netlist.v',
                     f'hierarchy -check -top {TOP}']
        if variant == 'generic':
            readback += ['proc', 'opt_clean', 'techmap', 'dffunmap', 'clean']
        readback += ['check -assert', f'write_json {target}/readback.json']
        yosys('synthesis-' + variant + '-readback', readback)
        saved = json.loads((target / 'readback.json').read_text())
        saved_metrics = resource_metrics(saved, mapped=variant == 'typical')
        if variant == 'typical' and saved_metrics != metrics:
            raise ValueError('Saved buffered Verilog resource readback differs from synthesis')
        if saved_metrics['physical_state_bits'] != metrics['physical_state_bits']:
            raise ValueError('Saved buffered Verilog changes physical state capacity')
        metrics = saved_metrics
        models = ([ROOT / 'build/tools/oss-cad-suite/share/yosys/simcells.v']
                  if variant == 'generic' else [Path(name) for name in pdk['models']])
        executable = compile_rtl(run, target, target / 'netlist.v', variant + '-gates', cells=models)
        result['variants'][variant] = dict(metrics=metrics, executable=str(executable),
            netlist_json=str(target / 'netlist.json'), netlist_verilog=str(target / 'netlist.v'),
            netlist_sha256=sha(target / 'netlist.v'), json_sha256=sha(target / 'netlist.json'),
            readback_sha256=sha(target / 'readback.json'),
            simulation_models_sha256={str(path): sha(path) for path in models})
        if equivalence:
            result['variants'][variant]['equivalence'] = prove_saved_mapping(
                yosys, out, target, description, saved, variant, library)
    if sha(source) != source_digest:
        raise ValueError('Buffered source artifact changed during synthesis')
    return result


def prove_saved_mapping(yosys, out, target, description, data, variant, library):
    """Compare source and saved gates after exact, checked physical state intake."""
    source = json.loads((out / 'source-readback.json').read_text())
    reference, source_projection = state_cut(source['modules'][TOP], description, True)
    candidate, projection = state_cut(data['modules'][TOP], description, True)
    reference = project_pruned_state(reference, candidate, projection,
                                     projection['pruned_state_positions'])
    write(target / 'source-cut.json', dict(modules=dict(reference=reference)))
    write(target / 'gate-cut.json', dict(modules=dict(candidate=candidate)))

    def prove(candidate_path, label, reject=None):
        lines = []
        if variant == 'typical':
            lines.append(f'read_liberty -ignore_miss_func {library}')
        lines += [f'read_json {target}/source-cut.json', f'read_json {candidate_path}']
        lines += ['miter -equiv -flatten -make_outputs reference candidate miter',
                  'hierarchy -check -top miter', 'flatten', 'opt -full',
                  'sat -verify -prove trigger 0 -set-def-inputs miter']
        log = yosys(label, lines, reject=reject)
        if not reject and 'SAT proof finished - no model found: SUCCESS!' not in log:
            raise ValueError('Incomplete saved buffered mapping comparison')

    prove(target / 'gate-cut.json', 'synthesis-' + variant + '-equivalence')
    mutant = deepcopy(candidate)
    all_bits = [bit for cell in mutant['cells'].values()
                for bits in cell['connections'].values() for bit in bits if type(bit) is int]
    all_bits += [bit for port in mutant['ports'].values() for bit in port['bits'] if type(bit) is int]
    fresh = max(all_bits) + 1
    original = mutant['ports']['levels']['bits'][0]
    mutant['cells']['negative_levels'] = dict(type='$_NOT_', hide_name=0, parameters={},
        attributes={}, port_directions={'A': 'input', 'Y': 'output'},
        connections={'A': [original], 'Y': [fresh]})
    mutant['ports']['levels']['bits'][0] = fresh
    mutant['netnames']['levels']['bits'] = list(mutant['ports']['levels']['bits'])
    write(target / 'gate-cut-negative.json', dict(modules=dict(candidate=mutant)))
    prove(target / 'gate-cut-negative.json', 'synthesis-' + variant + '-negative',
          reject='proof did fail')
    return dict(status='equivalent', projection=projection, source_projection=source_projection,
        negative_control='Inverted public output level rejected',
        scope='All public outputs and surviving logical next-state bits for arbitrary defined '
              'inputs and state; only explicitly reported physically absent next-state '
              'coordinates are omitted. No initialization or reachability assumption.')
