"""Native comparison on copied, source-audited SRAM boundary spellings only."""
import json
from pathlib import Path
import re
import subprocess
import time

from audits import sha, write
from boundary_adapter_v5 import MASTER, canonical_pin, native_macro_contract, positional_reference, normalized_extracted_header

R = Path('/work/diagnostic')


def main():
    cfg = json.loads((R / 'boundary-lvs-request.json').read_text())
    phase = json.loads((R / 'phase.json').read_text())
    receipt = json.loads((R / 'report.json').read_text())
    gate = json.loads((R / 'fixture-semantic-gate.json').read_text())
    assert sha(R / 'fixture-semantic-gate.json') == phase['fixture_semantic_gate_sha256']
    assert gate['macro_connectivity_qualified'] is True and gate['standardcell_sensitivity_qualified'] is True
    stop = min(cfg['native_stop_epoch'], receipt['native_stop_epoch'])
    inventory = json.loads((R / 'input/inventory.json').read_text())
    native_contract = native_macro_contract(inventory)
    mapping = json.loads((R / 'macro-port-map.json').read_text())
    native_ports = [b for a, b in mapping['pairs']]
    order = [canonical_pin(pin) for pin in native_ports]
    assert len(order) == len(set(order)) == 345
    out = R / 'boundary-netgen-v5'
    out.mkdir()
    reference = Path(cfg['reference'])
    extracted = Path(cfg['extracted'])
    converted_reference, reference_audit = positional_reference(reference.read_text(), inventory, order)
    converted_extracted, extracted_audit = normalized_extracted_header(extracted.read_text(), native_ports)
    (out / 'reference-positional.v').write_text(converted_reference)
    (out / 'extracted-canonical-header.spice').write_text(converted_extracted)
    (out / 'macro-boundary-reference.spice').write_text('.subckt ' + MASTER + ' ' + ' '.join(order) + '\n.ends ' + MASTER + '\n')
    write(out / 'reference-adapter-audit.json', reference_audit)
    write(out / 'extracted-adapter-audit.json', extracted_audit)
    # Keep every physical extracted macro instance/node exactly as measured.
    # The header-only spelling map must never repair its rail connectivity.
    joined = re.sub(r'\n\+', ' ', converted_extracted)
    physical_macro_instances = []
    for line in joined.splitlines():
        parts = line.split()
        if parts and parts[0].startswith('X') and parts[-1] == MASTER:
            assert len(parts) - 2 == 345
            physical_macro_instances.append({'instance': parts[0], 'nodes': parts[1:-1]})
    assert len(physical_macro_instances) == len(native_contract) == 2
    setup = Path(cfg['setup'])
    lines = ['model blackbox on', 'set circuit1 [readnet spice ' + str(out / 'extracted-canonical-header.spice') + ']',
        'set circuit2 [readnet verilog /dev/null]']
    # Physical standard-cell models are present in circuit1's actual extraction;
    # do not overwrite them with reference library definitions.
    for path in cfg['standard_spice_models']:
        assert Path(path).is_file()
        lines.append('readnet spice ' + path + ' $circuit2')
    lines += ['readnet spice ' + str(out / 'macro-boundary-reference.spice') + ' $circuit2',
        'readnet verilog ' + str(out / 'reference-positional.v') + ' $circuit2']
    for circuit in ('1', '2'):
        lines += ['model "$circuit' + circuit + ' ' + MASTER + '" blackbox',
            'set macro_model' + circuit + ' [model "$circuit' + circuit + ' ' + MASTER + '"]',
            'if {$macro_model' + circuit + ' ne "blackbox"} {error "Macro blackbox classification failed"}',
            'puts "PINWHEEL_MACRO_MODEL' + circuit + ' $macro_model' + circuit + '"']
    lines.append('lvs "$circuit1 tt_um_pinwheel_buffered" "$circuit2 tt_um_pinwheel_buffered" ' + str(setup) + ' ' + str(out / 'lvs.rpt') + ' -blackbox -json')
    (out / 'run.lvs').write_text('\n'.join(lines) + '\n')
    command = ['netgen', '-batch', 'source', str(out / 'run.lvs')]
    result = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
        cwd=out, timeout=max(1, stop-time.time()))
    (out / 'native.log').write_text(result.stdout)
    assert result.returncode == 0
    assert not re.search(r'(?mi)^\s*(?:Error:|Tcl error|invalid command name)', result.stdout), 'Comparison syntax/model resolution error'
    for circuit in ('1', '2'):
        assert re.findall(r'^PINWHEEL_MACRO_MODEL' + circuit + r' (\S+)$', result.stdout, re.M) == ['blackbox']
    report = (out / 'lvs.rpt').read_text()
    parsed = json.loads((out / 'lvs.json').read_text())
    assert isinstance(parsed, list) and parsed
    top = [row for row in parsed if row.get('name') == ['tt_um_pinwheel_buffered'] * 2]
    assert len(top) == 1
    expected = {}
    for instance in inventory['instances'].values():
        master = instance['master']
        expected[master] = expected.get(master, 0) + 1
    active = [dict(side) for side in top[0]['devices']]
    assert active == [expected, expected], 'Full fixed native instance/master inventory not retained in comparison'
    final = re.findall(r'^Final result:\s*(.*?)\s*$', report, re.M)
    assert len(final) == 1
    known = ['Circuits match uniquely.', 'Netlists do not match.', 'Netlists failed to match.',
        'Circuits match with errors.', 'Top level cell failed pin matching.']
    assert final[0] in known, 'Unknown native final result; retain diagnostic, no qualification'
    write(out / 'measurement.json', {'schema': 'pinwheel-native-explicit-boundary-LVS-v5',
        'status': 'measured_native_comparison', 'native_final_result': final[0],
        'native_match_uniquely': final[0] == 'Circuits match uniquely.',
        'source_reference_sha256': sha(reference), 'source_extracted_sha256': sha(extracted),
        'reference_adapter': reference_audit, 'extracted_header_adapter': extracted_audit,
        'physical_extracted_macro_instances_preserved': physical_macro_instances,
        'native_active_device_master_counts': active, 'native_top_nets': top[0]['nets'],
        'native_top_pin_counts': [len(side) for side in top[0]['pins']],
        'native_badnet_group_count': len(top[0].get('badnets', [])),
        'native_badelement_group_count': len(top[0].get('badelements', [])),
        'native_command': command, 'script_sha256': sha(out / 'run.lvs'),
        'native_report_sha256': sha(out / 'lvs.rpt'), 'native_JSON_sha256': sha(out / 'lvs.json'),
        'fixture_semantic_gate_sha256': sha(R / 'fixture-semantic-gate.json'),
        'actual_layout_copied_positive_and_negative_controls_run': False,
        'physical_acceptance_claim': False, 'internal_SRAM_LVS_qualified': False,
        'scope': 'Compared fixed complete instance inventory and explicit345-port SRAM boundaries. Empty macro interiors are intentionally blackboxed; full boundary acceptance still requires actual positive report/contact review and copied-actual sensitivity controls.'})

if __name__ == '__main__': main()
