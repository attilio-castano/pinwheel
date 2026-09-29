"""Reproduce a refused supplied tile and test its explicit diagnostic copy."""
import argparse
from collections import Counter
import copy
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time
import klayout.db as db
from check_inputs import HERE, TOP, CELL, prepare_counterfactual, require, sha

POLICY = 'tile-physical-boundary-and-dimensional-resistors-v1'

def write(path, data):
    path.write_text(json.dumps(data, indent=2) + '\n')

def value(obj, name):
    item = getattr(obj, name)
    return item() if callable(item) else item

def readback(path):
    lvs = db.LayoutVsSchematic()
    lvs.read(str(path))
    xref = lvs.xref()
    rows = []
    for pair in xref.each_circuit_pair():
        row = dict(status=str(pair.status()))
        for side, circuit in [('layout', pair.first()), ('schematic', pair.second())]:
            row[side] = None if circuit is None else dict(name=circuit.name,
                models=dict(Counter(d.device_class().name for d in circuit.each_device())),
                pins=[value(p, 'name') for p in circuit.each_pin()])
        for kind, iterator in [('device', xref.each_device_pair), ('net', xref.each_net_pair),
                               ('pin', xref.each_pin_pair), ('subcircuit', xref.each_subcircuit_pair)]:
            row[kind + '_statuses'] = dict(Counter(str(p.status()) for p in iterator(pair)))
        rows.append(row)
    return dict(circuits=rows, database_match=bool(rows) and all(r['status'] == 'Match' for r in rows))

def accepted(row, log):
    audit = row.get('policy', {})
    stages = {'before_preparation', 'layout_flatten', 'schematic_flatten', 'after_flatten',
              'bound_layout_ports', 'after_simplify', 'prepared_layout_ports',
              'layout_prepared', 'schematic_prepared'}
    complete = stages <= audit.get('stages', {}).keys() and len(audit.get('physical_port_witnesses', [])) == 42
    return (row['exit_code'] == 0 and row.get('database_match', False) and complete
            and audit.get('policy') == POLICY and audit.get('top') == TOP
            and audit.get('status') == 'matched' and audit.get('native_success') is True
            and 'Congratulations! Netlists match.' in log)

def compare(deck, output, label, mode, gds, cdl, reasons=()):
    folder = output / (label + '_' + mode)
    folder.mkdir()
    cmd = ['python3', '-B', str(deck / 'run_lvs.py'), '--layout=' + str(gds), '--netlist=' + str(cdl),
           '--topcell=' + TOP, '--run_mode=' + mode, '--run_dir=' + str(folder / 'lvs')]
    start = time.monotonic()
    with (folder / 'native.log').open('w') as f:
        result = subprocess.run(cmd, stdout=f, stderr=subprocess.STDOUT, timeout=90,
                     env=dict(os.environ, QT_QPA_PLATFORM='offscreen', OMP_NUM_THREADS='4',
                              PINWHEEL_POLICY_REPORT=str(folder / 'policy.json'),
                              PINWHEEL_POLICY_CONTRACT=str(HERE / 'contract.json')))
    row = dict(command=cmd, exit_code=result.returncode, mode=mode,
               seconds=round(time.monotonic()-start,3), gds_sha256=sha(gds), cdl_sha256=sha(cdl))
    if (folder / 'policy.json').exists():
        row['policy'] = json.loads((folder / 'policy.json').read_text())
    database = folder / 'lvs' / (gds.stem + '.lvsdb')
    if database.exists():
        row.update(readback(database))
    log = (folder / 'native.log').read_text()
    row['accepted_counterfactual'] = accepted(row, log)
    audit = row.get('policy', {})
    row['native_rejection'] = (audit.get('status') == 'no_match' and audit.get('native_success') is False
                               and row.get('database_match') is False and "ERROR : Netlists don't match" in log)
    row['policy_rejection'] = (audit.get('status') == 'rejected' and 'PINWHEEL_POLICY_REJECT:' in log
                               and any(reason in audit.get('reason', '') for reason in reasons))
    row['attributed_rejection'] = not row['accepted_counterfactual'] and (row['native_rejection'] or row['policy_rejection'])
    return row, log

def geometry(layout):
    regions = {}
    texts = Counter()
    top = layout.cell(TOP)
    for index in layout.layer_indexes():
        layer = str(layout.get_info(index))
        regions[layer] = db.Region(top.begin_shapes_rec(index))
        it = top.begin_shapes_rec(index)
        while not it.at_end():
            if it.shape().is_text():
                texts[(layer, str(it.shape().text.transformed(it.trans())))] += 1
            it.next()
    return regions, texts

def identical_geometry(a, b):
    ra, ta = geometry(a)
    rb, tb = geometry(b)
    require(ta == tb, 'Carrier changed text')
    require(all((ra.get(k, db.Region()) ^ rb.get(k, db.Region())).is_empty()
                for k in ra.keys() | rb.keys()), 'Carrier changed polygons')

def controls(output, text, cdl):
    inputs = output / 'mutations'
    inputs.mkdir()
    gds = HERE / (TOP + '.gds')
    cases = []
    physical_checks = {}
    block = re.search(r'^\.SUBCKT ' + re.escape(CELL) + r'\b.*?^\.ENDS[^\n]*', text, re.M | re.S)[0]
    fault_name = CELL + '_FAULT'
    def single_bit(body):
        require(body != block, 'Missing single-bit mutation')
        body = body.replace('.SUBCKT ' + CELL + ' ', '.SUBCKT ' + fault_name + ' ', 1)
        source, count = re.subn(r'(?m)^(XCELL<0>[^\n]* /\s+)' + re.escape(CELL) + r'$',
                                lambda m: m[1] + fault_name, text)
        require(count == 1, 'Single-bit target not unique')
        return source + '\n' + body + '\n'
    mutations = {
        'one_bit_internal_open': (block.replace('MN1 NT ', 'MN1 FAULT_OPEN '), ()),
        'one_bit_internal_short': (block.replace('MN0 NC ', 'MN0 VSS '), ()),
        'one_bit_missing_nmos': (re.sub(r'^MN0[^\n]*\n', '', block, flags=re.M), ()),
        'one_bit_missing_resistor': (re.sub(r'^R0[^\n]*\n', '', block, flags=re.M), ()),
        'one_bit_wrong_metal': (block.replace('R0 BLT_BOT BLT_TOP res_metal2', 'R0 BLT_BOT BLT_TOP res_metal3'), ()),
        'one_bit_unknown_model': (block.replace('R0 BLT_BOT BLT_TOP res_metal2', 'R0 BLT_BOT BLT_TOP lvsres'), ('Unsupported active model lvsres',)),
    }
    for device, prefix in [('R0', 'metal2'), ('R2', 'metal3')]:
        line = next(line for line in block.splitlines() if line.startswith(device + ' '))
        for suffix, replacement in [
            ('width', line.replace('w=2e-07', 'w=4e-07')),
            ('length', line.replace('l=6e-07', 'l=1.2e-06')),
            ('equal_ratio_dimensions', line.replace('w=2e-07', 'w=4e-07').replace('l=6e-07', 'l=1.2e-06')),
        ]:
            mutations['one_bit_' + prefix + '_' + suffix] = (block.replace(line, replacement), ())
    for label, (body, reasons) in mutations.items():
        path = inputs / (label + '.cdl')
        path.write_text(single_bit(body))
        cases.append((label, gds, path, reasons))
    header = text.splitlines()[0]
    variants = {
        'original_widths': (text.replace('w=2e-07', 'w=2.6e-07'), ()),
        'declared_port_missing': (text.replace(header, header.replace(' A_LWL<0>', '')), ('Declared port identity/order changed',)),
        'wordline_swap': (text.replace('XCELL<0> A_BLC_BOT<0> A_LBLC<1> A_BLT_BOT<0> A_LBLT<1> A_LWL<0>',
                                      'XCELL<0> A_BLC_BOT<0> A_LBLC<1> A_BLT_BOT<0> A_LBLT<1> A_LWL<1>')
                         .replace('XCELL<1> A_LBLC<2> A_LBLC<1> A_LBLT<2> A_LBLT<1> A_LWL<1>',
                                  'XCELL<1> A_LBLC<2> A_LBLC<1> A_LBLT<2> A_LBLT<1> A_LWL<0>'), ()),
    }
    for label, (variant, reasons) in variants.items():
        require(variant != text, 'Missing interface mutation: ' + label)
        path = inputs / (label + '.cdl')
        path.write_text(variant)
        cases.append((label, gds, path, reasons))

    source = db.Layout()
    source.read(str(gds))
    carrier = db.Layout()
    carrier.read(str(gds))
    cell = carrier.cell('RM_IHPSG13_1P_BITKIT_CELL')
    cell.flatten(True)
    identical_geometry(source, carrier)
    carrier_path = inputs / 'unchanged_carrier.gds'
    carrier.write(str(carrier_path))
    reread = db.Layout()
    reread.read(str(carrier_path))
    identical_geometry(source, reread)
    cases.append(('unchanged_carrier', carrier_path, cdl, ()))
    gate = ((db.Region(cell.begin_shapes_rec(carrier.find_layer(1, 0)))
             - db.Region(cell.begin_shapes_rec(carrier.find_layer(14, 0))))
            & db.Region(cell.begin_shapes_rec(carrier.find_layer(5, 0))))
    require(not gate.is_empty(), 'Missing NMOS geometry')
    polygons = list(gate.each())
    selected_gate = db.Region(polygons[0])
    physical = {
        'physical_metal_open': ((10, 0), 'remove', db.Region(db.Box(380, -370, 620, -330)),
                                ('Disconnected physical port', 'Flattening lost physical port')),
        'physical_metal_bridge': ((10, 0), 'add', db.Region(db.Box(-600, -460, 600, -440)),
                                  ('Two physical ports probe the same net',)),
        'physical_missing_nmos_gate': ((5, 0), 'remove', selected_gate,
                                       ('Disconnected physical port', 'Flattening lost physical port')),
    }
    for label in [*physical, 'physical_port_missing', 'physical_ports_swapped', 'physical_port_off_metal']:
        target = db.Layout()
        target.read(str(carrier_path))
        reasons = ()
        if label in physical:
            layer, operation, region, reasons = physical[label]
            child = target.cell('RM_IHPSG13_1P_BITKIT_CELL')
            index = target.find_layer(*layer)
            before = db.Region(child.begin_shapes_rec(index))
            after = before - region if operation == 'remove' else before + region
            require(not (before ^ after).is_empty(), 'Physical mutation changed nothing')
            child.shapes(index).clear()
            child.shapes(index).insert(after)
            physical_checks[label] = dict(layer=list(layer), changed_area_dbu2=(before ^ after).area(),
                                          edited_bit_cell_occurrences=32)
        else:
            count = 0
            for shape in list(target.cell(TOP).shapes(target.find_layer(30, 25)).each()):
                if not shape.is_text():
                    continue
                label_text = shape.text
                name = label_text.string
                if label == 'physical_port_missing' and name == 'A_LWL<0>':
                    shape.delete()
                    count += 1
                    reasons = ('Physical boundary labels missing',)
                elif label == 'physical_ports_swapped' and name in ['A_LWL<0>', 'A_LWL<1>']:
                    label_text.string = 'A_LWL<1>' if name == 'A_LWL<0>' else 'A_LWL<0>'
                    shape.text = label_text
                    count += 1
                elif label == 'physical_port_off_metal' and name == 'A_LWL<0>':
                    label_text.x += 100000
                    shape.text = label_text
                    count += 1
                    reasons = ('Boundary label does not probe a top net',)
            require(count == (2 if label == 'physical_ports_swapped' else 1), 'Missing physical label target')
            physical_checks[label] = dict(changed_labels=count, polygons_changed=False)
        path = inputs / (label + '.gds')
        target.write(str(path))
        reread = db.Layout()
        reread.read(str(path))
        before_regions, before_text = geometry(carrier)
        after_regions, after_text = geometry(reread)
        deltas = {key: (before_regions.get(key, db.Region()) ^ after_regions.get(key, db.Region())).area()
                  for key in before_regions.keys() | after_regions.keys()}
        deltas = {key: area for key, area in deltas.items() if area}
        if label in physical:
            require(set(deltas) == {str(db.LayerInfo(*physical[label][0]))} and before_text == after_text,
                    'Physical control changed wrong geometry/text')
        else:
            require(not deltas and before_text != after_text, 'Port control changed polygons or no text')
        physical_checks[label]['whole_tile_changed_area_dbu2'] = deltas
        cases.append((label, path, cdl, reasons))
    return cases, physical_checks

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--pdk-deck', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--controls', action='store_true')
    args = parser.parse_args()
    identities = json.loads((HERE / 'inputs.json').read_text())
    pdk = args.pdk_deck.resolve()
    require({str(p.relative_to(pdk)): sha(p) for p in pdk.rglob('*') if p.is_file()} == identities['deck_sha256'],
            'Changed pinned deck')
    text, report = prepare_counterfactual()
    output = args.output.resolve()
    require(not output.exists(), 'Preserve prior run')
    output.mkdir(parents=True)
    cdl = output / (TOP + '.counterfactual.cdl')
    cdl.write_text(text)
    report.update(comparisons={}, policy=POLICY, counterfactual_cdl_sha256=sha(cdl), controls_requested=args.controls)
    write(output / 'report.json', report)
    deck = output / 'deck'
    shutil.copytree(pdk, deck)
    p = deck / 'sg13cmos5l.lvs'
    script = p.read_text()
    for before, after in [
        ('  target_netlist.simplify if SIMPLIFY',
         '  if SIMPLIFY\n    target_netlist.combine_devices\n'
         '    target_netlist.each_circuit { |c| c.purge_nets_keep_pins }\n  end'),
        ('  # === Aligns the extracted netlist vs. the schematic ===',
         (HERE / 'policy.rb').read_text() + '\n  # === Aligns the extracted netlist vs. the schematic ==='),
        ('  #=== IGNORE EXTREME VALUES ===', '  pw_verify_prepared.call\n  #=== IGNORE EXTREME VALUES ==='),
        ('  #------------- COMPARISON RESULTS ---------------',
         '  pw_finish.call(success)\n  #------------- COMPARISON RESULTS ---------------'),
    ]:
        require(script.count(before) == 1, 'Changed pinned deck anchor')
        script = script.replace(before, after)
    p.write_text(script)
    require([name for name, digest in identities['deck_sha256'].items() if sha(deck / name) != digest]
            == ['sg13cmos5l.lvs'], 'Unexpected private deck changes')
    cases = [('counterfactual', HERE / (TOP + '.gds'), cdl, ())]
    if args.controls:
        extra, report['physical_controls'] = controls(output, text, cdl)
        cases += extra
    positive_log = None
    positive_row = None
    for label, gds, source, reasons in cases:
        for mode in ['deep', 'flat']:
            row, log = compare(deck, output, label, mode, gds, source, reasons)
            expected_positive = label in ['counterfactual', 'unchanged_carrier']
            row['expected_positive_counterfactual'] = expected_positive
            row['expected_result_observed'] = row['accepted_counterfactual'] if expected_positive else row['attributed_rejection']
            report['comparisons'][label + '_' + mode] = row
            write(output / 'report.json', report)
            print(label, mode, 'positive' if expected_positive else 'negative', row['expected_result_observed'], flush=True)
            require(row['expected_result_observed'], 'Unexpected comparison: ' + label + '_' + mode)
            if expected_positive:
                require(len(row['circuits']) == 1 and row['circuits'][0]['device_statuses'] == {'Match': 288}
                        and row['circuits'][0]['net_statuses'] == {'Match': 182}
                        and row['circuits'][0]['pin_statuses'] == {'Match': 42}, 'Incomplete positive correspondence')
                positive_row, positive_log = row, log
    report['evidence_refusals'] = []
    for name in ['absent_audit', 'missing_stage', 'missing_witness', 'native_failure', 'database_failure', 'process_failure', 'missing_final_log']:
        row = copy.deepcopy(positive_row)
        log = positive_log
        if name == 'absent_audit':
            row.pop('policy')
        elif name == 'missing_stage':
            row['policy']['stages'].pop('after_simplify')
        elif name == 'missing_witness':
            row['policy']['physical_port_witnesses'].pop()
        elif name == 'native_failure':
            row['policy']['native_success'] = False
        elif name == 'database_failure':
            row['database_match'] = False
        elif name == 'process_failure':
            row['exit_code'] = 1
        elif name == 'missing_final_log':
            log = ''
        require(not accepted(row, log), 'Incomplete evidence admitted: ' + name)
        report['evidence_refusals'].append(name)
    report['status'] = 'diagnostic_complete_source_still_refused'
    write(output / 'report.json', report)

if __name__ == '__main__':
    main()
