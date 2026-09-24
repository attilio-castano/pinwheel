#!/usr/bin/env python3
"""Compare state ownership and structural communication in saved SRAM chips.

This is a mapped-netlist census, not a delay, activity or routability model.
The Lean assembly is regenerated and must match the saved MLIR/RTL before its
typed ownership is applied to old mapped netlists. No synthesis is run.
"""
import argparse
from collections import Counter, defaultdict
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import time

from validation_run import Commands, fresh_directory, sha
from chip_organization import SourceGraph, mapped_partition, placed_funnels, projection_screen
from chip_map_slice import cell_areas, map_slice_report, readback_view as map_slice_readback

ROOT = Path(__file__).resolve().parents[1]
FF = 'sg13cmos5l_dfrbpq_1'
MACROS = {
    'hybrid': 'RM_IHPSG13_1P_64x64_c2_bm_bist',
    'direct': 'RM_IHPSG13_1P_512x64_c2_bm_bist',
}
COMB = re.compile(r'sg13cmos5l_(?:a21o|a21oi|a221oi|a22oi|and[234]|buf|inv|'
                  r'mux[24]|nand[234]|nand[23]b|nor[234]|nor2b|o21ai|or[234]|xnor2|xor2)_1')


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def register_descriptions(module, assembly):
    """Use the typed emitter's state list; do not infer ownership from names."""
    owners = assembly['owners']
    if assembly['schema'] != 1 or not owners or len(set(owners)) != len(owners) or 'reference_image' in owners:
        raise ValueError('Invalid physical owner enumeration')
    slots = {}
    for slot in assembly['registers']:
        name, width, owner = slot['name'], slot['width'], slot['owner']
        if name in slots or not name.startswith('controller.r_'):
            raise ValueError(f'Duplicate or invalid register name: {name}')
        if type(width) is not int or width <= 0 or owner not in owners:
            raise ValueError(f'Invalid width or owner: {name}')
        slots[name] = slot
    actual = {n: x['bits'] for n, x in module['netnames'].items() if n.startswith('controller.r_')}
    if set(actual) != set(slots):
        raise ValueError(f'Register manifest mismatch: {sorted(set(actual) ^ set(slots))[:8]}')
    for name, bits in actual.items():
        if len(bits) != slots[name]['width']:
            raise ValueError(f'Register width mismatch: {name}')
    return {n: (slots[n]['owner'], bits) for n, bits in actual.items()}


def check_crossings(graph, assembly):
    """Bind every functional macro terminal, including address truncation."""
    expected = {(n, p) for n in graph.macros for p in ('A_ADDR', 'A_DIN', 'A_DOUT', 'A_REN', 'A_WEN')}
    seen, names = set(), set()
    for c in assembly['crossings']:
        if c['name'] in names:
            raise ValueError('Duplicate crossing name')
        names.add(c['name'])
        name = 'controller.' + c['name']
        signal = graph.module['netnames'].get(name, {}).get('bits', [])
        width = c['physical_width']
        if type(c['width']) is not int or len(signal) != c['width'] or type(width) is not int or not 0 < width <= len(signal):
            raise ValueError(f'Crossing width mismatch: {name}')
        if any(b != '0' for b in signal[width:]):
            raise ValueError(f'Nonzero or dynamic truncated address bits: {name}')
        if c['phase'] == 'before' and c['producer'] == 'controller':
            terminals, direction = c['consumers'], 'input'
        elif c['phase'] == 'after' and c['consumers'] == ['controller']:
            terminals, direction = [c['producer']], 'output'
        else:
            raise ValueError(f'Invalid crossing phase/ownership: {name}')
        for instance in terminals:
            terminal = instance, c['macro_port']
            if terminal not in expected or terminal in seen:
                raise ValueError(f'Duplicate or unknown macro terminal: {terminal}')
            cell = graph.macros[instance]
            if cell['port_directions'][c['macro_port']] != direction or cell['connections'][c['macro_port']] != signal[:width]:
                raise ValueError(f'Crossing does not match mapped terminal: {terminal}')
            seen.add(terminal)
    if seen != expected:
        raise ValueError(f'Missing macro terminals: {sorted(expected - seen)}')
    return {'crossings': len(names), 'macro_terminals': len(seen), 'address_truncation_checked': True}


class Graph:
    """All input pins conservatively influence every output of a combinational cell.

    Stop at flop Q, macro Q and top inputs. Cell depth includes buffers and
    inverters. It has no library delays or sensitization/path-exception model.
    """
    def __init__(self, module, assembly):
        self.module = module
        self.owner_names = assembly['owners']
        self.cells = {n: c for n, c in module['cells'].items() if c['type'] != '$scopeinfo'}
        self.drivers, self.roots, self.root_groups = {}, {}, {}
        self.loads, self.aliases = defaultdict(list), defaultdict(list)
        self.flops, self.macros, self.comb = {}, {}, {}
        self.registers = register_descriptions(module, assembly)
        for n, (_, bits) in self.registers.items():
            for i, b in enumerate(bits):
                self.aliases[b].append(f'{n}[{i}]')
        for n, p in module['ports'].items():
            for i, b in enumerate(p['bits']):
                if p['direction'] == 'input':
                    self.add_root(b, f'input:{n}[{i}]', 'package_inputs')
                elif p['direction'] == 'output':
                    self.loads[b].append((f'port:{n}', str(i)))
                else:
                    raise ValueError(f'Unsupported top port direction: {n}')
        for n, c in self.cells.items():
            kind = c['type']
            if kind == FF:
                if set(c['connections']) != {'CLK', 'D', 'Q', 'RESET_B'} or any(
                        len(b) != 1 for b in c['connections'].values()):
                    raise ValueError(f'Unsupported flop shape: {n}')
                self.flops[n] = c
            elif kind in MACROS.values():
                self.macros[n] = c
            elif COMB.fullmatch(kind):
                self.comb[n] = c
            else:
                raise ValueError(f'Unsupported cell type: {kind}')
            if set(c['connections']) != set(c['port_directions']):
                raise ValueError(f'Missing cell port directions: {n}')
            for p, bits in c['connections'].items():
                direction = c['port_directions'][p]
                if direction not in ('input', 'output'):
                    raise ValueError(f'Unsupported direction: {n}.{p}')
                for i, b in enumerate(bits):
                    if direction == 'input':
                        self.loads[b].append((n, p))
                    elif kind == FF:
                        aliases = self.aliases[b]
                        if not aliases or len({self.registers[a.split('[')[0]][0] for a in aliases}) != 1:
                            raise ValueError(f'Unowned or ambiguous flop: {n}')
                        self.add_root(b, 'state:' + '|'.join(sorted(aliases)), self.registers[aliases[0].split('[')[0]][0])
                    elif n in self.macros:
                        self.add_root(b, f'{n}:{p}[{i}]', n)
                    else:
                        self.add_driver(b, (n, p, i))
        self.signatures, self.depths, self.visiting = {}, {}, set()
        # Also reject undriven inputs and cycles in logic outside the selected cones.
        for b in self.loads:
            self.signature(b)
        for b in self.drivers:
            self.signature(b)

    def add_driver(self, bit, driver):
        if type(bit) is not int or bit in self.drivers or bit in self.roots:
            raise ValueError(f'Multiple or invalid drivers on bit {bit}')
        self.drivers[bit] = driver

    def add_root(self, bit, label, group):
        if type(bit) is not int or bit in self.roots or bit in self.drivers:
            raise ValueError(f'Multiple or invalid drivers on bit {bit}')
        self.roots[bit], self.root_groups[bit] = label, group

    def inputs(self, cell):
        return {p: bits for p, bits in cell['connections'].items()
                if cell['port_directions'][p] == 'input'}

    def signature(self, bit):
        if bit in self.signatures:
            return self.signatures[bit]
        if isinstance(bit, str):
            if bit not in ('0', '1', 'x', 'z'):
                raise ValueError(f'Unknown constant: {bit}')
            result, depth = digest(['constant', bit]), 0
        elif bit in self.roots:
            result, depth = digest(['root', self.roots[bit]]), 0
        else:
            if bit in self.visiting:
                raise ValueError(f'Combinational cycle at bit {bit}')
            if bit not in self.drivers:
                raise ValueError(f'Undriven loaded bit: {bit}')
            self.visiting.add(bit)
            name, port, index = self.drivers[bit]
            cell = self.cells[name]
            inputs = {p: [self.signature(b) for b in bits] for p, bits in self.inputs(cell).items()}
            depth = 1 + max((self.depths[b] for bits in self.inputs(cell).values() for b in bits), default=0)
            result = digest([cell['type'], cell.get('parameters', {}), inputs, port, index])
            self.visiting.remove(bit)
        self.signatures[bit], self.depths[bit] = result, depth
        return result

    def boundary_signature(self):
        """Named sequential inputs and package outputs, independent of auto cell names."""
        result = {}
        for n, c in self.flops.items():
            result[self.roots[c['connections']['Q'][0]]] = {
                'type': c['type'], 'parameters': c.get('parameters', {}),
                'inputs': {p: [self.signature(b) for b in bits] for p, bits in self.inputs(c).items()}}
        for n, c in self.macros.items():
            result[n] = {'type': c['type'], 'parameters': c.get('parameters', {}),
                         'inputs': {p: [self.signature(b) for b in bits] for p, bits in self.inputs(c).items()}}
        result['ports'] = {n: {'direction': p['direction'], 'bits': [self.signature(b) for b in p['bits']]}
                           for n, p in self.module['ports'].items()}
        return result

    def cone(self, bits):
        for bit in bits:
            self.signature(bit)
        visited, cells, roots = set(), set(), set()
        pending = list(bits)
        while pending:
            b = pending.pop()
            if b in visited or isinstance(b, str):
                continue
            visited.add(b)
            if b in self.roots:
                roots.add(b)
            else:
                n, _, _ = self.drivers[b]
                cells.add(n)
                pending.extend(b for bb in self.inputs(self.cells[n]).values() for b in bb)
        return {'combinational_cells': len(cells), 'max_cell_depth': max((self.depths[b] for b in bits), default=0),
                'root_bits_by_owner': dict(sorted(Counter(self.root_groups[b] for b in roots).items())),
                'macro_response_bits': {n: sorted(self.roots[b] for b in roots if self.root_groups[b] == n)
                                        for n in self.macros}}

    def state(self):
        groups = {o: {'named_bits': 0, 'mapped_ff_bits': 0, 'unimplemented_bits': []} for o in self.owner_names}
        for n, (o, bits) in self.registers.items():
            groups[o]['named_bits'] += len(bits)
            for i, b in enumerate(bits):
                if b not in self.roots:
                    groups[o]['unimplemented_bits'].append(f'{n}[{i}]')
        for o in self.root_groups.values():
            if o in groups:
                groups[o]['mapped_ff_bits'] += 1
        return groups

    def port_budget(self, instances, port):
        bits = [b for n in instances for b in self.macros[n]['connections'][port]]
        nets = {b for b in bits if type(b) is int}
        return {'endpoint_pins': len(bits), 'nonconstant_endpoint_pins': sum(type(b) is int for b in bits),
                'distinct_nonconstant_nets': len(nets), 'loaded_nets': sum(bool(self.loads[b]) for b in nets)}

    def report(self):
        names = sorted(self.macros)
        groups = {
            'macro_addresses': [b for n in names for b in self.macros[n]['connections']['A_ADDR']],
            'broadcast_write_data': self.macros[names[0]]['connections']['A_DIN'],
            'read_write_enables': [b for n in names for p in ('A_REN', 'A_WEN') for b in self.macros[n]['connections'][p]],
            'package_outputs': [b for p in self.module['ports'].values() if p['direction'] == 'output' for b in p['bits']],
        }
        groups.update({n + '_address': self.macros[n]['connections']['A_ADDR'] for n in names})
        groups.update({o + '_next': [c['connections']['D'][0] for c in self.flops.values()
                                   if self.root_groups[c['connections']['Q'][0]] == o] for o in self.owner_names})
        fanout = []
        clock_bits = set(self.module['ports']['clk']['bits'])
        for b in sorted((b for b in self.loads if type(b) is int and b not in clock_bits),
                        key=lambda b: (-len(self.loads[b]), b))[:10]:
            driver = self.drivers.get(b)
            fanout.append({'bit': b, 'sink_pins': len(self.loads[b]), 'register_aliases': self.aliases[b],
                           'driver': self.roots.get(b) or f'{driver[0]}:{driver[1]}',
                           'driver_type': self.cells[driver[0]]['type'] if driver else 'sequential_or_input'})
        return {'cell_records_including_scopeinfo': len(self.module['cells']), 'physical_cells': len(self.cells),
                'combinational_cells': len(self.comb), 'flip_flops': len(self.flops), 'state': self.state(),
                'macro_types': {n: c['type'] for n, c in self.macros.items()},
                'macro_ports': {p: self.port_budget(names, p) for p in ('A_ADDR', 'A_DIN', 'A_DOUT', 'A_REN', 'A_WEN')},
                'broadcast_identical': {p: all(self.macros[n]['connections'][p] == self.macros[names[0]]['connections'][p]
                                              for n in names) for p in ('A_DIN', 'A_REN', 'A_WEN')},
                'cones': {n: self.cone(bits) for n, bits in groups.items()}, 'highest_fanout_excluding_clock': fanout,
                'clock_sink_pins': sum(len(self.loads[b]) for b in clock_bits)}


def check_hashes(root, expected):
    for name, wanted in expected.items():
        if sha(root / name) != wanted:
            raise ValueError(f'Source/artifact hash mismatch: {name}')


def load_graph(path, assembly):
    return Graph(json.loads(path.read_text())['modules']['tt_um_pinwheel'], assembly)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--comparison', type=Path, default=Path('build/storage/sram-chip/corridor-02'))
    p.add_argument('--tag', required=True)
    p.add_argument('--placed-context', type=Path, help='Saved routing_context.py export; no physical tool is run')
    p.add_argument('--placed-database', type=Path, help='Local database whose hash must match that export')
    p.add_argument('--locality-windows', type=Path, help='Analysis-only address-window projection; requires placed inputs')
    args = p.parse_args()
    if bool(args.placed_context) != bool(args.placed_database):
        p.error('Supply both --placed-context and --placed-database')
    if args.locality_windows and not args.placed_context:
        p.error('Locality windows require the placed context and database')
    comparison = (ROOT / args.comparison).resolve()
    receipt = json.loads((comparison / 'report.json').read_text())
    compatibility = json.loads((comparison / 'compatibility.json').read_text())
    if compatibility != receipt['compatibility']:
        raise ValueError('Macro compatibility receipt differs from the original comparison')
    # Source refactors are admitted only through exact regenerated-artifact
    # equality. Preserve the external macro binding and tool identities too.
    check_hashes(ROOT, {'test/sram_chip.sv': receipt['source_sha256']['test/sram_chip.sv']})
    yosys = Path('build/tools/oss-cad-suite/bin/yosys')
    circt = Path('build/tools/firtool-1.159.0/bin/circt-opt')
    check_hashes(ROOT, {str(tool): receipt['tools_sha256'][str(tool)] for tool in (yosys, circt)})
    check_hashes(comparison, {f'{v}/typical.v': receipt['variants'][v]['metrics']['typical']['netlist_sha256']
                              for v in MACROS})
    out = fresh_directory(ROOT / 'build/validation', args.tag)
    started = time.monotonic()
    commands = Commands(ROOT, out, default_timeout=30)
    input_paths = [comparison / 'report.json', comparison / 'compatibility.json',
                   *(ROOT / name for name in receipt['source_sha256']), ROOT / yosys, ROOT / circt,
                   *sorted((ROOT / 'Pinwheel').rglob('*.lean')), ROOT / 'Pinwheel.lean',
                   ROOT / 'test/ProofAudit.lean', ROOT / 'test/Interfaces.lean',
                   Path(__file__), ROOT / 'test/test_chip_architecture.py',
                   ROOT / 'scripts/validation_run.py', ROOT / 'scripts/process_group.py',
                   ROOT / 'scripts/chip_organization.py', ROOT / 'scripts/chip_map_slice.py']
    input_paths.extend(comparison / v / f'typical.{ext}' for v in MACROS for ext in ('json', 'v', 'ys'))
    if args.placed_context:
        input_paths.extend([ROOT / args.placed_context, ROOT / args.placed_database, ROOT / 'scripts/routing_context.py',
                            ROOT / 'scripts/routing_evidence.py'])
    if args.locality_windows:
        input_paths.append(ROOT / args.locality_windows)
    frozen = {str(path.relative_to(ROOT)): sha(path) for path in input_paths}
    result = {'schema': 2, 'created_utc': datetime.now(timezone.utc).isoformat(),
              'comparison': str(comparison.relative_to(ROOT)), 'inputs_sha256': frozen,
              'scope': 'Typed Lean ownership/schedule checks and regenerated MLIR/RTL equality bind current source to the saved typical mappings. Structural cones overapproximate dependence; no new synthesis, simulation or physical run.',
              'variants': {}, 'commands': commands.records}
    context = None
    if args.placed_context:
        context = json.loads((ROOT / args.placed_context).read_text())
        expected = {'database_sha256': sha(ROOT / args.placed_database),
                    'extractor_sha256': sha(ROOT / 'scripts/routing_context.py'),
                    'evidence_helper_sha256': sha(ROOT / 'scripts/routing_evidence.py'),
                    'units': 'micrometres'}
        for field, value in expected.items():
            if context.get(field) != value:
                raise ValueError(f'Placed context {field} mismatch')
    commands(['lake', 'build', 'Pinwheel', 'sram_chip_emit'], 'assembly-build', timeout=300)
    commands(['lake', 'env', 'lean', '-DwarningAsError=true', 'test/ProofAudit.lean'], 'assembly-axioms', timeout=120)
    commands(['lake', 'env', 'lean', '-DwarningAsError=true', '--run', 'test/Interfaces.lean'], 'assembly-contracts', timeout=60)
    emitted = out / 'emitted'
    emitted.mkdir()
    commands([ROOT / '.lake/build/bin/sram_chip_emit', emitted], 'assembly-emit', timeout=60)
    artifacts = {}
    for variant in MACROS:
        artifacts[variant] = {}
        for kind in ('core', 'chip'):
            mlir = emitted / f'{variant}-{kind}.mlir'
            rtl = emitted / f'{variant}-{kind}.sv'
            text = commands([ROOT / circt, mlir, '--canonicalize', '--lower-seq-to-sv', '--lower-hw-to-sv',
                             '--hw-legalize-modules', '--export-verilog', '-o', '/dev/null'], f'{variant}-{kind}-export')
            rtl.write_text(text)
            actual = {'mlir_sha256': sha(mlir), 'rtl_sha256': sha(rtl)}
            if actual != receipt['variants'][variant]['artifacts'][kind]:
                raise ValueError(f'{variant}/{kind}: regenerated MLIR/RTL differs from the saved mapping input')
            artifacts[variant][kind] = actual
    result['emitted_artifacts'] = artifacts
    result['source_changes_since_comparison'] = [n for n, h in receipt['source_sha256'].items() if sha(ROOT / n) != h]
    result['assembly_verification_seconds'] = round(time.monotonic() - started, 3)
    analysis_started = time.monotonic()
    for variant, macro in MACROS.items():
        source = comparison / variant
        assembly_path = emitted / f'{variant}-assembly.json'
        assembly = json.loads(assembly_path.read_text())
        if assembly['variant'] != variant:
            raise ValueError('Assembly variant mismatch')
        # Read the receipt-bound Verilog using the original JSON only for black-box
        # port declarations. Compare all named sequential inputs and package pins.
        readback = out / f'{variant}-verilog-readback.json'
        script = out / f'{variant}-readback.ys'
        script.write_text(f'read_json "{source / "typical.json"}"\n'
                          'delete tt_um_pinwheel\n'
                          f'read_verilog "{source / "typical.v"}"\n'
                          'hierarchy -check -top tt_um_pinwheel\n'
                          f'write_json "{readback}"\n')
        commands([ROOT / yosys, '-Q', '-T', '-s', script], variant + '-readback')
        graph, imported = load_graph(source / 'typical.json', assembly), load_graph(readback, assembly)
        signature = graph.boundary_signature()
        if signature != imported.boundary_signature():
            raise ValueError(f'{variant}: saved JSON differs from receipt-bound Verilog')
        report = graph.report()
        report['assembly_binding'] = check_crossings(graph, assembly)
        if check_crossings(imported, assembly) != report['assembly_binding']:
            raise ValueError('Imported Verilog has a different assembly interface')
        report['assembly_sha256'] = sha(assembly_path)
        partition = mapped_partition(graph, assembly)
        if partition['summary'] != mapped_partition(imported, assembly)['summary']:
            raise ValueError('Mapped consumer partition differs in Verilog read-back')
        source_report = SourceGraph((emitted / f'{variant}-chip.mlir').read_text(), assembly).report()
        organization = out / f'{variant}-organization.json'
        organization.write_text(json.dumps({'source': source_report, 'mapped': partition}, indent=2) + '\n')
        report['organization'] = {'artifact': str(organization.relative_to(ROOT)),
                                  'sha256': sha(organization), 'mapped_summary': partition['summary'],
                                  'request_modes': {k: {n: v[n] for n in ('operations', 'root_bits_by_owner')}
                                                    for k, v in source_report['request_modes'].items()}}
        metrics = receipt['variants'][variant]['metrics']['typical']
        if variant == 'hybrid':
            areas = cell_areas(json.loads((source / 'typical.json').read_text())['modules'], graph)
            if abs(sum(areas.values()) - metrics['standard_cell_area_um2']) > 0.001:
                raise ValueError('Mapped Liberty areas disagree with the comparison receipt')
            slices = map_slice_report(graph, assembly, areas)
            imported_areas = cell_areas(json.loads(readback.read_text())['modules'], imported)
            imported_slices = map_slice_report(imported, assembly, imported_areas)
            if map_slice_readback(slices) != map_slice_readback(imported_slices):
                raise ValueError('Map slice boundaries or costs differ in Verilog read-back')
            artifact = out / 'hybrid-map-slices.json'
            artifact.write_text(json.dumps(slices, indent=2) + '\n')
            report['map_slices'] = {'artifact': str(artifact.relative_to(ROOT)), 'sha256': sha(artifact),
                                   'readback_signature_sha256': digest(map_slice_readback(slices)),
                                   'standard_cell_area_reconciled_um2': round(sum(areas.values()), 4),
                                   'organizations': {kind: {
                                       'selected_group': slices[kind]['selected']['group'],
                                       'selected_budget': slices[kind]['groups'][slices[kind]['selected']['group']],
                                       'groups': slices[kind]['groups'],
                                       'unique_slice_crossing_nets': slices[kind]['unique_slice_crossing_nets']}
                                       for kind in ('planes', 'word_tiles', 'read_tree_tiles')}}
        if report['flip_flops'] != metrics['flip_flops'] or report['cell_records_including_scopeinfo'] != metrics['cells']:
            raise ValueError(f'{variant}: cell census disagrees with original comparison')
        if sorted(report['macro_types'].values()) != [macro, macro]:
            raise ValueError(f'{variant}: expected two matching SRAM replicas')
        report.update(mapped_metrics=metrics, boundary_signature_sha256=digest(signature),
                      verilog_readback_sha256=sha(readback), verilog_binding='structurally matched at all sequential inputs and package ports')
        report['macro_geometry'] = {k: compatibility['macros'][macro][k]
                                    for k in ('width_um', 'height_um', 'footprint_um2')}
        result['variants'][variant] = report
    if context is not None:
        placed = placed_funnels(context, COMB)
        artifact = out / 'placed-address-funnels.json'
        artifact.write_text(json.dumps(placed, indent=2) + '\n')
        result['placed_address_funnels'] = {'artifact': str(artifact.relative_to(ROOT)), 'sha256': sha(artifact),
                                            'context': str(args.placed_context), 'context_sha256': sha(ROOT / args.placed_context)}
        if args.locality_windows:
            plan = json.loads((ROOT / args.locality_windows).read_text())
            if plan['schema'] != 1 or plan['kind'] != 'address-window-projection':
                raise ValueError('Unsupported locality screen')
            screen = projection_screen(context, placed['funnels'], plan['windows_um'], plan['depth'])
            artifact = out / 'address-window-projection.json'
            artifact.write_text(json.dumps(screen, indent=2) + '\n')
            result['address_window_projection'] = {'artifact': str(artifact.relative_to(ROOT)), 'sha256': sha(artifact),
                                                    'joint': screen['joint'],
                                                    'isolated_improving_moves': screen['isolated_improving_moves']}
    check_hashes(ROOT, frozen)
    result['analysis_seconds'] = round(time.monotonic() - analysis_started, 3)
    result['elapsed_seconds'] = round(time.monotonic() - started, 3)
    (out / 'report.json').write_text(json.dumps(result, indent=2) + '\n')
    print(out / 'report.json')


if __name__ == '__main__':
    main()
