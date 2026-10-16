#!/usr/bin/env python3
"""Prepare a small native comparator fixture; no CAD or Docker is launched."""
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
    def identifier(name):
        return name if name.replace('_', '').isalnum() else '\\' + name + ' '
    verilog += [MASTER + ' memory (' + ', '.join('.' + identifier(pin) + '(' + macro_nodes[pin] + ')' for pin in macro_ports) + ');', 'endmodule']
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
    extracted, reference, native = fixture(spice_headers(std.read_text()), ports)
    (out / 'fixture/extracted.spice').write_text(extracted)
    (out / 'fixture/macro-boundary.spice').write_text('.subckt ' + MASTER + ' ' + ' '.join(ports) + '\n.ends ' + MASTER + '\n')
    shutil.copyfile(std, out / 'fixture/stdcell.spice')
    write(out / 'fixture/inventory.json', native)
    write(out / 'fixture/macro-port-map.json', {'pairs': pairs, 'count': len(pairs), 'internal_SRAM_qualified': False})
    mutants, detail = reference_faults(reference, native)
    cases = {}
    setup = '/work/pdk/ihp-sg13cmos5l/libs.tech/netgen/ihp-sg13cmos5l_setup.tcl'
    for name, text in mutants.items():
        case = out / 'controls' / name
        case.mkdir(parents=True)
        (case / 'reference.v').write_text(text)
        script = '\n'.join([
            'set circuit1 [readnet spice /work/diagnostic/fixture/extracted.spice]',
            'readnet spice /work/diagnostic/fixture/stdcell.spice $circuit1',
            'readnet spice /work/diagnostic/fixture/macro-boundary.spice $circuit1',
            'set circuit2 [readnet verilog /dev/null]',
            'readnet spice /work/diagnostic/fixture/stdcell.spice $circuit2',
            'readnet spice /work/diagnostic/fixture/macro-boundary.spice $circuit2',
            'readnet verilog /work/diagnostic/controls/' + name + '/reference.v $circuit2',
            'lvs "$circuit1 ' + TOP + '" "$circuit2 ' + TOP + '" ' + setup + ' /work/diagnostic/controls/' + name + '/lvs.rpt -blackbox -json']) + '\n'
        (case / 'run.lvs').write_text(script)
        cases[name] = {'reference_sha256': sha(case / 'reference.v'), 'script_sha256': sha(case / 'run.lvs'),
            'expected_unique_match': name == 'positive', 'mutation': detail.get(name, {'changed_terminal_count': 0})}
    helpers = ['lvs_fixture_host_v2.py', 'lvs_controls_host_v2.py', 'lvs_controls_native_v2.py',
               'lvs_execute_staged_v2.py', 'lvs_mutants_v2.py', 'audits.py']
    for name in helpers:
        shutil.copyfile(HERE / name, out / name)
    shutil.copyfile(prepared_path.parent / 'campaign_runner.py', out / 'campaign_runner.py')
    sources = dict(p['source_sha256'])
    sources.update({str(prepared_path): sha(prepared_path), str(std): sha(std), str(macro_cdl): sha(macro_cdl), str(macro_lef): sha(macro_lef)})
    write(out / 'controls-config.json', {'schema': 'pinwheel-native-LVS-sensitivity-controls-v2',
        'synthetic_fixture_only': True, 'scope': 'Synthetic electrical comparator fixture using actual CMOS5L buffers/DFFs/PG models and exact 345-port SRAM boundary; no layout/extraction proof',
        'prepared': p, 'source_sha256': sources, 'positive_receipt_sha256': None,
        'positive_has_to_succeed_first_natively': True, 'cases': cases,
        'fixture_cell_count': 5, 'standard_cell_count': 4, 'macro_boundary_port_count': 345,
        'source_reference_sha256': sha(out / 'controls/positive/reference.v'),
        'physical_connectivity_claim': False, 'internal_SRAM_qualified': False})
    print(json.dumps({'status': 'staged_only_no_CAD', 'out': str(out),
        'root_only_run_argv': ['python3', '-B', str(out / 'lvs_execute_staged_v2.py'), '--staged-root', str(out), '--native-seconds', '300']}))


if __name__ == '__main__':
    main()
