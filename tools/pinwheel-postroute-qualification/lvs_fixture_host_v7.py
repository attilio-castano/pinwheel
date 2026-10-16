#!/usr/bin/env python3
"""Prepare v6 safe-named native macro-boundary sensitivity fixture; no CAD."""
import argparse
import json
from pathlib import Path
import shutil

from audits import port_map, sha, spice_headers, write
from lvs_mutants_v2 import reference_faults

HERE = Path(__file__).resolve().parent
MASTER = 'RM_IHPSG13_1P_64x64_c2_bm_bist'
TOP = 'tt_um_pinwheel_buffered'


def fixture(std_models, macro_ports):
    assert len(macro_ports) == len(set(macro_ports)) == 345, 'Require exact unique 345-port native model order'
    assert {'VDD!', 'VDDARRAY!', 'VSS!'} <= set(macro_ports)
    assert set(std_models['sg13cmos5l_buf_1']) == {'A', 'X', 'VDD', 'VSS'}
    assert set(std_models['sg13cmos5l_dfrbpq_1']) == {'D', 'CLK', 'RESET_B', 'Q', 'VDD', 'VSS'}
    all_ports = ['I0', 'I1', 'clk', 'rst_n', 'Q0', 'Q1', 'VPWR', 'VGND']
    macro_nodes = {pin: ('VPWR' if pin in ('VDD!', 'VDDARRAY!') else 'VGND' if pin == 'VSS!' else 'M' + str(i))
                   for i, pin in enumerate(macro_ports)}
    all_ports += [node for pin, node in macro_nodes.items() if pin not in ('VDD!', 'VDDARRAY!', 'VSS!')]
    instances = {
        'hold8042': ('sg13cmos5l_buf_1', {'A': 'I0', 'X': 'net8042', 'VDD': 'VPWR', 'VSS': 'VGND'}),
        'hold8046': ('sg13cmos5l_buf_1', {'A': 'I1', 'X': 'net8046', 'VDD': 'VPWR', 'VSS': 'VGND'}),
        '_30759_': ('sg13cmos5l_dfrbpq_1', {'D': 'net8042', 'CLK': 'clk', 'RESET_B': 'rst_n', 'Q': 'Q0', 'VDD': 'VPWR', 'VSS': 'VGND'}),
        '_30606_': ('sg13cmos5l_dfrbpq_1', {'D': 'net8046', 'CLK': 'clk', 'RESET_B': 'rst_n', 'Q': 'Q1', 'VDD': 'VPWR', 'VSS': 'VGND'})}
    spice = ['* Synthetic comparator fixture; no physical geometry/extraction claim', '.subckt ' + TOP + ' ' + ' '.join(all_ports)]
    verilog = ['module ' + TOP + ' (' + ', '.join(all_ports) + ');', 'input ' + ', '.join(['I0', 'I1', 'clk', 'rst_n', *all_ports[8:]]) + ';',
        'output Q0, Q1;', 'inout VPWR, VGND;', 'wire net8042, net8046;']
    native = {'instances': {}, 'nets': {}}
    for name, (master, connections) in instances.items():
        spice.append('X' + name + ' ' + ' '.join(connections[p] for p in std_models[master]) + ' ' + master)
        verilog.append(master + ' ' + name + ' (' + ', '.join('.' + pin + '(' + net + ')' for pin, net in connections.items()) + ');')
        native['instances'][name] = {'master': master, 'terminals': []}
        for pin, net in connections.items():
            direction = 'OUTPUT' if pin in ('X', 'Q') else 'INOUT' if pin in ('VDD', 'VSS') else 'INPUT'
            native['instances'][name]['terminals'].append([pin, net, direction])
            native['nets'].setdefault(net, {'sig_type': 'SIGNAL', 'ports': [], 'terminals': []})['terminals'].append([name, pin, direction])
    spice += ['Xmemory ' + ' '.join(macro_nodes[pin] for pin in macro_ports) + ' ' + MASTER, '.ends ' + TOP]
    # Positional reference order exactly equals the copied SPICE boundary header.
    # Netgen's escaped per-bit named-port handling differs from standard Verilog.
    verilog += [MASTER + ' memory (' + ', '.join(macro_nodes[pin] for pin in macro_ports) + ');', 'endmodule']
    return '\n'.join(spice) + '\n', '\n'.join(verilog) + '\n', native


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--prepared', type=Path, required=True, help='Existing immutable same-campaign qualification package')
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    prepared_path = args.prepared.resolve()
    p = json.loads(prepared_path.read_text())
    assert p['schema'] == 'pinwheel-isolated-postroute-qualification-v1'
    for relative, digest in p['staged_sha256'].items():
        assert sha(prepared_path.parent / relative) == digest
    out = args.out.resolve()
    assert not out.exists()
    out.mkdir(parents=True)
    (out / 'fixture').mkdir()
    std = Path(p['PDK_root']) / 'ihp-sg13cmos5l/libs.ref/sg13cmos5l_stdcell/spice/sg13cmos5l_stdcell.spice'
    macro_dir = prepared_path.parent / 'core/macro'
    macro_cdl = macro_dir / (MASTER + '.cdl')
    macro_lef = macro_dir / (MASTER + '.lef')
    import re
    lef_ports = re.findall(r'^\s*PIN\s+(\S+)\s*$', macro_lef.read_text(), re.M)
    pairs = port_map(spice_headers(macro_cdl.read_text())[MASTER], lef_ports)
    assert len(pairs) == 345
    ports = [b for a, b in pairs]
    aliases = ['PW_SRAM_PIN_' + str(i).zfill(3) for i in range(345)]
    assert len(set(aliases)) == len(set(ports)) == 345
    extracted, reference, native = fixture(spice_headers(std.read_text()), ports)
    (out / 'fixture/extracted.spice').write_text(extracted)
    (out / 'fixture/macro-boundary.spice').write_text('.subckt ' + MASTER + ' ' + ' '.join(aliases) + '\n.ends ' + MASTER + '\n')
    # Netgen binds a physical file to a circuit number; each circuit needs distinct file paths.
    for circuit in ('extracted', 'reference'):
        shutil.copyfile(std, out / ('fixture/stdcell-' + circuit + '.spice'))
        shutil.copyfile(out / 'fixture/macro-boundary.spice', out / ('fixture/macro-boundary-' + circuit + '.spice'))
    write(out / 'fixture/inventory.json', native)
    write(out / 'fixture/macro-port-map.json', {'pairs': pairs, 'count': len(pairs), 'internal_SRAM_qualified': False})
    mutants, detail = reference_faults(reference, native)
    # These mutations change only one/two positional macro terminal attachments.
    macro_match = re.search(re.escape(MASTER) + r' memory \((.*?)\);', reference)
    macro_nodes = macro_match[1].split(', ')
    assert len(macro_nodes) == len(ports) == 345
    def macro_fault(name, pin_changes):
        changed = list(macro_nodes)
        ledger = []
        declarations = []
        for pin, value in pin_changes:
            index = ports.index(pin)
            ledger.append({'instance': 'memory', 'pin': pin, 'before': changed[index], 'after': value})
            changed[index] = value
            if value.startswith('PW_LVS_NEG_'):
                declarations.append('wire ' + value + ';')
        text = reference[:macro_match.start(1)] + ', '.join(changed) + reference[macro_match.end(1):]
        if declarations:
            text = text.replace('wire net8042, net8046;', 'wire net8042, net8046;\n' + '\n'.join(declarations))
        mutants[name] = text
        detail[name] = {'changed_terminal_count': len(ledger), 'changed_terminals': ledger, 'macro_boundary_fault': True}
    signal_ports = [pin for pin in ports if pin not in ('VDD!', 'VDDARRAY!', 'VSS!')]
    a, b = signal_ports[:2]
    macro_fault('macro-detached-signal', [(a, 'PW_LVS_NEG_MACRO_OPEN')])
    macro_fault('macro-bridged-signals', [(b, macro_nodes[ports.index(a)])])
    macro_fault('macro-detached-VSS', [('VSS!', 'PW_LVS_NEG_MACRO_VSS_OPEN')])
    # Netgen1.5.320 Verilog parser rejects positional macro instances. Use a
    # reversible345-pin safe-name map on both copied model headers/reference.
    for name, text in list(mutants.items()):
        match = re.search(re.escape(MASTER) + r' memory \((.*?)\);', text)
        nodes = match[1].split(', ')
        assert len(nodes) == 345
        named = ', '.join('.' + alias + '(' + node + ')' for alias, node in zip(aliases, nodes))
        mutants[name] = text[:match.start(1)] + named + text[match.end(1):]
    cases = {}
    setup = '/work/pdk/ihp-sg13cmos5l/libs.tech/netgen/ihp-sg13cmos5l_setup.tcl'
    for name, text in mutants.items():
        case = out / 'controls' / name
        case.mkdir(parents=True)
        (case / 'reference.v').write_text(text)
        script = '\n'.join([
            'model blackbox on',
            'set circuit1 [readnet spice /work/diagnostic/fixture/extracted.spice]',
            'readnet spice /work/diagnostic/fixture/stdcell-extracted.spice $circuit1',
            'readnet spice /work/diagnostic/fixture/macro-boundary-extracted.spice $circuit1',
            'set circuit2 [readnet verilog /dev/null]',
            'readnet spice /work/diagnostic/fixture/stdcell-reference.spice $circuit2',
            'readnet spice /work/diagnostic/fixture/macro-boundary-reference.spice $circuit2',
            'model "$circuit1 ' + MASTER + '" blackbox',
            'model "$circuit2 ' + MASTER + '" blackbox',
            'if {[model "$circuit1 ' + MASTER + '"] ne "blackbox" || [model "$circuit2 ' + MASTER + '"] ne "blackbox"} {error "Macro model not blackbox before reference read"}',
            'readnet verilog /work/diagnostic/controls/' + name + '/reference.v $circuit2',
            'set macro_model1 [model "$circuit1 ' + MASTER + '"]',
            'set macro_model2 [model "$circuit2 ' + MASTER + '"]',
            'if {$macro_model1 ne "blackbox" || $macro_model2 ne "blackbox"} {error "Macro blackbox classification not retained"}',
            'puts "PINWHEEL_MACRO_MODEL1 $macro_model1"',
            'puts "PINWHEEL_MACRO_MODEL2 $macro_model2"',
            'lvs "$circuit1 ' + TOP + '" "$circuit2 ' + TOP + '" ' + setup + ' /work/diagnostic/controls/' + name + '/lvs.rpt -blackbox -json']) + '\n'
        (case / 'run.lvs').write_text(script)
        cases[name] = {'reference_sha256': sha(case / 'reference.v'), 'script_sha256': sha(case / 'run.lvs'),
            'expected_unique_match': name == 'positive', 'mutation': detail.get(name, {'changed_terminal_count': 0})}
    helpers = ['lvs_fixture_host_v7.py', 'lvs_controls_host_v2.py', 'lvs_controls_native_v7.py',
               'lvs_execute_staged_v7.py', 'lvs_mutants_v2.py', 'lvs_case_verdict_v7.py', 'audits.py']
    for name in helpers:
        shutil.copyfile(HERE / name, out / name)
    shutil.copyfile(prepared_path.parent / 'campaign_runner.py', out / 'campaign_runner.py')
    sources = dict(p['source_sha256'])
    sources.update({str(prepared_path): sha(prepared_path), str(std): sha(std), str(macro_cdl): sha(macro_cdl), str(macro_lef): sha(macro_lef)})
    write(out / 'controls-config.json', {'schema': 'pinwheel-native-LVS-sensitivity-controls-v2',
        'synthetic_fixture_only': True, 'preparation_version': 7,
        'macro_comparison_pin_alias_map': list(zip(ports, aliases)),
        'macro_comparison_pin_alias_order': aliases,
        'native_parser_source': 'https://raw.githubusercontent.com/RTimothyEdwards/netgen/b3af7b98b4a3bfbb149134e17eb3004a086b686a/base/verilog.c#L2246-L2256',
        'native_parser_cause': 'Positional Verilog first token is not dot-name association; parser emits Ignoring subcircuit with no pin names and skips instance',
        'blackbox_mechanism': 'model blackbox on before any reads; explicit per-circuit macro blackbox set/query before comparison',
        'native_expected_macro_active_count_per_top': 1,
        'native_expected_top_devices_per_side': {'sg13cmos5l_buf_1': 2, 'sg13cmos5l_dfrbpq_1': 2, MASTER: 1},
        'mandatory_independent_semantic_gate': True,
        'macro_reference_connection_style': '345 explicit safe named scalar aliases with reversible originalpin mapping; both loaded SPICE boundary headers use the identical alias order',
        'macro_model_header_order': ports,
        'native_comparator_semantic_qualification_requires_independent_review': True,
        'model_circuit_file_identity_fix': 'Separate byte-identical stdcell and macro-boundary file paths for extracted and reference Netgen circuit numbers',
        'same_model_bytes_per_circuit': {name: sha(out / ('fixture/' + name + '-extracted.spice')) == sha(out / ('fixture/' + name + '-reference.spice')) for name in ('stdcell', 'macro-boundary')}, 'scope': 'Synthetic electrical comparator fixture using actual CMOS5L buffers/DFFs/PG models and exact 345-port SRAM boundary; no layout/extraction proof',
        'prepared': p, 'source_sha256': sources, 'positive_receipt_sha256': None,
        'positive_has_to_succeed_first_natively': True, 'cases': cases,
        'fixture_cell_count': 5, 'standard_cell_count': 4, 'macro_boundary_port_count': 345,
        'source_reference_sha256': sha(out / 'controls/positive/reference.v'),
        'physical_connectivity_claim': False, 'internal_SRAM_qualified': False})
    print(json.dumps({'status': 'staged_only_no_CAD', 'out': str(out),
        'root_only_run_argv': ['python3', '-B', str(out / 'lvs_execute_staged_v7.py'), '--staged-root', str(out), '--native-seconds', '300']}))


if __name__ == '__main__':
    main()
