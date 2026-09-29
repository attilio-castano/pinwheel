"""Read back tile fault geometry and exercise the narrow source adapter.

This supplements the frozen run.py receipt. Its local changed_area_dbu2 field
was evaluated after mutating a live KLayout Region view and reads zero. The
independent whole-tile XOR in that recipe was correct and remains authoritative.
"""
import argparse
import copy
import json
from pathlib import Path
import klayout.db as db
from check_inputs import HERE, TOP, CELL, prepare_counterfactual, require, sha, translate


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--controls-output', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    require(not args.output.exists(), 'Preserve previous audit')
    source = (HERE / (TOP + '.cdl')).read_text()
    geometry = json.loads((HERE / 'geometry.json').read_text())
    diagnostic, _ = prepare_counterfactual()
    proposed = source.replace('w=2.6e-07', 'w=2e-07')
    require(translate(proposed, geometry) == diagnostic, 'Changed adapter positive')
    resistor = next(line for line in proposed.splitlines() if line.startswith('R0 '))
    cases = {
        'original_widths': (source, copy.deepcopy(geometry)),
        'unknown_nodes': (proposed.replace('R0 BLT_BOT ', 'R0 UNKNOWN '), copy.deepcopy(geometry)),
        'unknown_model': (proposed.replace('R0 BLT_BOT BLT_TOP lvsres', 'R0 BLT_BOT BLT_TOP UNKNOWN'), copy.deepcopy(geometry)),
        'missing_resistor': (proposed.replace(resistor + '\n', ''), copy.deepcopy(geometry)),
        'duplicate_resistor': (proposed.replace(resistor, resistor + '\n' + resistor), copy.deepcopy(geometry)),
        'extra_parameter': (proposed.replace(resistor, resistor + ' extra=1'), copy.deepcopy(geometry)),
        'missing_dimension': (proposed.replace(resistor, resistor.replace(' w=2e-07', '')), copy.deepcopy(geometry)),
        'duplicate_dimension': (proposed.replace(resistor, resistor.replace('l=6e-07', 'w=2e-07')), copy.deepcopy(geometry)),
        'wrong_marker_width': (proposed, copy.deepcopy(geometry)),
        'marker_off_conductor': (proposed, copy.deepcopy(geometry)),
        'wrong_native_width': (proposed, copy.deepcopy(geometry)),
        'wrong_native_terminal': (proposed, copy.deepcopy(geometry)),
        'missing_cell_definition': (proposed.replace('.SUBCKT ' + CELL + ' ', '.SUBCKT OTHER '), copy.deepcopy(geometry)),
    }
    cases['wrong_marker_width'][1]['markers']['10/29'][0]['width_um'] = 0.26
    cases['marker_off_conductor'][1]['markers']['30/29'][0]['fully_on_conductor'] = False
    cases['wrong_native_width'][1]['native_resistors'][0]['parameters']['W'] = 0.26
    cases['wrong_native_terminal'][1]['native_resistors'][0]['terminals']['A']['name'] = 'UNKNOWN'
    refusals = {}
    for name, (text, witness) in cases.items():
        require(text != proposed or witness != geometry, 'Unchanged fault: ' + name)
        try:
            translate(text, witness)
        except RuntimeError as exc:
            refusals[name] = str(exc)
        else:
            raise RuntimeError('Adapter admitted fault: ' + name)

    output = args.controls_output.resolve()
    report = json.loads((output / 'report.json').read_text())
    carrier_path = output / 'mutations/unchanged_carrier.gds'
    carrier = db.Layout()
    carrier.read(str(carrier_path))
    cell_name = geometry['physical_cell']
    readbacks = {}
    inputs = {str(output / 'report.json'): sha(output / 'report.json'), str(carrier_path): sha(carrier_path)}
    for name, layer, expected_cell, expected_tile in [
        ('physical_metal_open', (10, 0), 8000, 256000),
        ('physical_metal_bridge', (10, 0), 12000, 384000),
        ('physical_missing_nmos_gate', (5, 0), 39000, 1248000),
    ]:
        path = output / 'mutations' / (name + '.gds')
        mutant = db.Layout()
        mutant.read(str(path))
        def region(layout, cell):
            return db.Region(layout.cell(cell).begin_shapes_rec(layout.find_layer(*layer))).dup()
        local_area = (region(carrier, cell_name) ^ region(mutant, cell_name)).area()
        tile_area = (region(carrier, TOP) ^ region(mutant, TOP)).area()
        require(local_area == expected_cell and tile_area == expected_tile, 'Changed physical fault: ' + name)
        native = report['physical_controls'][name]
        require(native['whole_tile_changed_area_dbu2'] == {str(db.LayerInfo(*layer)): tile_area},
                'Whole-tile receipt disagrees with independent readback')
        readbacks[name] = dict(layer=list(layer), bit_cell_area_dbu2=local_area,
                              whole_tile_area_dbu2=tile_area, dbu_um=carrier.dbu,
                              historical_local_area_field=native['changed_area_dbu2'],
                              historical_local_area_field_valid=False)
        inputs[str(path)] = sha(path)
    result = dict(status='passed', supplied_tile_qualification=False,
                  adapter_positive='explicit counterfactual only', adapter_refusals=refusals,
                  geometry_readback=readbacks, inputs_sha256=inputs,
                  boundary='Corrects an auxiliary local area field; no source, layout, policy or native verdict changed.')
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(dict(status=result['status'], adapter_refusals=len(refusals), geometry_readbacks=len(readbacks))))


if __name__ == '__main__':
    main()
