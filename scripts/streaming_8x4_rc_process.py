"""Data-only process/corner/via audit and a bounded consumer test contract.

This reviews exact retained ITF/draft/LEF bytes without executing upstream code,
OpenROAD or FasterCap.  Arithmetic/source agreement is not model qualification.
"""
import argparse
from decimal import Decimal, localcontext
import hashlib
import json
from pathlib import Path
import re
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
from streaming_tt_rc_compare import parse_stack, inventory_rules, METALS, stringify


NUM = r'[+-]?(?:\d+(?:\.\d*)?|\.\d+)(?:[eE][+-]?\d+)?'


def need(value, message):
    if not value:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def lef_resistance_inventory(text):
    clean = '\n'.join(line.split('#', 1)[0] for line in text.splitlines())
    layers = {}
    for match in re.finditer(r'^LAYER\s+(\w+)\s*\n(.*?)^END\s+\1\s*$', clean, re.M | re.S):
        name, body = match.groups()
        types = re.findall(r'^\s*TYPE\s+(ROUTING|CUT)\s*;', body, re.M)
        if not types:
            continue
        need(len(types) == 1 and name not in layers, 'Duplicate/ambiguous LEF routing/cut layer')
        pattern = r'\bRESISTANCE\s+' + (r'RPERSQ\s+' if types[0] == 'ROUTING' else '') + '(' + NUM + r')\s*;'
        resistance = re.findall(pattern, body)
        need(len(resistance) == 1, 'Missing/ambiguous LEF resistance: ' + name)
        value = Decimal(resistance[0])
        need(value.is_finite() and value > 0, 'Nonpositive/nonfinite LEF resistance')
        layers[name] = {'type': types[0], 'resistance': value,
                        'units': 'ohm_per_square' if types[0] == 'ROUTING' else 'ohm_per_cut'}
    need(set(METALS) <= set(layers) and all(x in layers for x in ('Via1', 'Via2', 'Via3', 'TopVia1')),
         'Incomplete expected LEF metal/via layer membership')
    vias = {}
    for match in re.finditer(r'^\s*Via\s+(\w+)(?:\s+DEFAULT)?\s*\n(.*?)^\s*END\s+\1\s*$',
                             clean, re.M | re.S | re.I):
        name, body = match.groups()
        values = re.findall(r'\bRESISTANCE\s+(' + NUM + r')\s*;', body)
        need(len(values) == 1 and name not in vias, 'Missing/ambiguous explicit LEF via resistance')
        cut_layers = {}; cut_rectangles = []
        for region in re.finditer(r'\bLAYER\s+(\w+)\s*;(.*?)(?=\bLAYER\b|\Z)', body, re.S):
            layer, geometry = region.groups()
            if layers.get(layer, {}).get('type') == 'CUT':
                count = len(re.findall(r'\bRECT\s+', geometry))
                need(count > 0, 'LEF via has no explicit cut rectangles')
                cut_layers[layer] = cut_layers.get(layer, 0) + count
                rectangles = re.findall(r'\bRECT\s+(' + NUM + r')\s+(' + NUM + r')\s+(' + NUM + r')\s+(' + NUM + r')\s*;', geometry)
                need(len(rectangles) == count, 'Unsupported/malformed cut rectangle')
                for rectangle in rectangles:
                    x0, y0, x1, y1 = map(Decimal, rectangle)
                    need(x1 > x0 and y1 > y0, 'Nonpositive via cut rectangle')
                    cut_rectangles.append((x0, y0, x1, y1))
        need(len(cut_layers) == 1, 'Selected LEF via does not have exactly one cut layer')
        layer, count = next(iter(cut_layers.items()))
        vias[name] = {'resistance_ohm': Decimal(values[0]),
                      'cut_layer': layer, 'cut_count': count,
                      'cut_bbox_um': (min(x[0] for x in cut_rectangles), min(x[1] for x in cut_rectangles),
                                      max(x[2] for x in cut_rectangles), max(x[3] for x in cut_rectangles))}
    need(vias, 'No explicit LEF vias inventoried')
    return {'layers': layers, 'explicit_vias': vias,
            'scope': 'selected LEF layer/via resistance fields; not a complete LEF validator'}


def verify_intake(base):
    base = Path(base)
    manifest = json.loads((base / 'manifest.json').read_text())
    need(manifest['schema'] == 'pinwheel.streaming-8x4-rc-process-intake.v1', 'Wrong process intake schema')
    result = {}
    for row in manifest['files']:
        path = base / row['path']
        need(path.is_file() and not path.is_symlink() and path.parent == base, 'Escaping/aliased source intake')
        data = path.read_bytes()
        blob = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        need(len(data) == row['bytes'] and hashlib.sha256(data).hexdigest() == row['sha256']
             and blob == row['git_blob'], 'Process intake byte identity differs')
        need(row['name'] not in result, 'Duplicate process intake name')
        result[row['name']] = data.decode()
    expected = {'itf_min', 'itf_typ', 'itf_max', 'itf_dir', 'draft_dir', 'draft_solver'}
    expected |= {'draft_' + c + '_' + suffix for c in ('MIN', 'TYP', 'MAX') for suffix in ('process', 'rules')}
    need(set(result) == expected, 'Process intake expected membership differs')
    return result, manifest


def consumer_protocol():
    return {
        'schema': 'pinwheel.streaming-8x4-rc-consumer-protocol.v1',
        'qualified': False, 'rc_model_promoted': False,
        'openroad_commit': 'dcf36133a369abc8f3c5e5738cd4d82e4903c0e0',
        'draft_commit': 'ffdafdbb4abb17316fa0ffd221ea99c0475c4734',
        'itf_commit': '7c783c7c56086511be93bb2097bee656a26148bd',
        'corners': ['MIN', 'TYP', 'MAX'],
        'extractor_version': '1.0', 'fresh_process_per_corner_and_policy': True,
        'policies': ['retained_rules', 'owned_explicit_via_rules'],
        'fixtures': [metal + '_L' + length for metal in METALS for length in ('50', '100')]
                    + ['Metal1_wide_L100', 'Metal2_wide_L100', 'Via1_XX', 'Via1_DC1B',
                       'Via2_XX', 'Via3_XX', 'TopVia1EWNS'],
        'numerical_gates': {
            'wire_R_relative_tolerance': '0.001', 'via_R_relative_tolerance': '0.001',
            'via_R_absolute_tolerance_ohm': '0.001',
            'nonnegative_finite_R_required': True,
            'exact_fixture_net_membership_required': True,
            'complete_connected_series_resistor_graph_required': True,
            'all_warnings_fatal': True, 'typed_zero_exit_required': True,
            'geometry_input_and_readback_identity_required': True,
        },
        'overlay_scope': 'new owned rules copies: populate only VIARES with each explicit tech-via R equal to per-cut ITF R divided by its observed cut count; shared PDK and capacitance tables unchanged',
        'overlay_parallel_cut_assumption': 'identical independent cuts; spreading/contact corrections require separate process authority',
        'resource_request': {'cpus': 1, 'memory_bytes': 2147483648, 'scratch_bytes': 134217728,
                             'seconds_per_openroad_call': 30, 'maximum_calls': 6,
                             'work_seconds': 210, 'outer_seconds': 300, 'root_go_required': True},
        'gates_are_separate': ['retained_consumer_behavior_reproduced', 'ITF_R_corner_arithmetic_matched',
                               'actual_final_target_via_and_width_coverage', 'physical_process_qualification'],
        'limits': ['a matching arithmetic fixture does not qualify the foundry R model',
                   'capacitance remains unqualified by this resistance experiment',
                   'no shared PDK/LEF, final layout or historical receipt is modified',
                   'generated dbVia objects and production installation remain separate evidence gates'],
    }


def audit(base, tech_lef):
    texts, intake = verify_intake(base)
    lef = lef_resistance_inventory(Path(tech_lef).read_text())
    corners = {}
    with localcontext() as context:
        context.prec = 50
        for corner in ('MIN', 'TYP', 'MAX'):
            itf = parse_stack(texts['itf_' + corner.lower()])
            process = parse_stack(texts['draft_' + corner + '_process'])
            rules = inventory_rules(texts['draft_' + corner + '_rules'], corner)
            via_headers = re.findall(r'^VIARES\s+(\d+)\s+Default LEF Vias:\s*$',
                                     texts['draft_' + corner + '_rules'], re.M)
            need(via_headers == ['0'], 'Draft VIARES inventory changed; reassess consumer proposal')
            wires = []
            for index, name in enumerate(METALS, 1):
                grid = rules['first_resover_grid_by_metal_index'][str(index)]
                width = grid['width_um']; ref = itf['CONDUCTOR', name]
                process_row = process['CONDUCTOR', name]
                actual_sheet = grid['resistance_ohm_per_nm'] * 1000 * width
                effective_width = width + process_row.get('width_delta', Decimal(0))
                wires.append({'metal': name, 'ITF_sheet_R_ohm': ref['RPSQ'],
                              'retained_LEF_sheet_R_ohm': lef['layers'][name]['resistance'],
                              'retained_LEF_matches_this_ITF_corner': lef['layers'][name]['resistance'] == ref['RPSQ'],
                              'draft_effective_sheet_R_ohm': actual_sheet,
                              'draft_vs_ITF_relative_difference': actual_sheet / ref['RPSQ'] - 1,
                              'declared_rule_width_um': width, 'draft_capacitance_geometry_width_um': effective_width,
                              'R_at_capacitance_geometry_width_ohm_per_um': ref['RPSQ'] / effective_width,
                              'draft_rule_R_ohm_per_um': grid['resistance_ohm_per_nm'] * 1000,
                              'width_support_inventory': rules['widths_um_by_metal_index'][str(index)]})
            vias = []
            for name in ('Via1', 'Via2', 'Via3', 'TopVia1'):
                target = itf['VIA', name]['RPV']; retained = lef['layers'][name]['resistance']
                vias.append({'via': name, 'ITF_R_per_cut_ohm': target, 'retained_LEF_R_per_cut_ohm': retained,
                             'retained_LEF_matches_this_ITF_corner': target == retained,
                             'retained_LEF_over_ITF_ratio': retained / target})
            corners[corner] = {'wires': wires, 'vias': vias, 'draft_VIARES_entries': 0,
                               'ITF_dielectric_ER': {n: v['ER'] for (k, n), v in itf.items() if k == 'DIELECTRIC'}}
    return stringify({
        'schema': 'pinwheel.streaming-8x4-rc-process-review.v1',
        'qualified': False, 'rc_model_qualified': False, 'native_executed': False,
        'process_intake_manifest_sha256': sha(Path(base) / 'manifest.json'),
        'tech_LEF': {'path': str(Path(tech_lef).resolve()), 'sha256': sha(tech_lef), 'inventory': lef},
        'corners': corners, 'consumer_protocol': consumer_protocol(),
        'source_inference': 'Empty draft VIARES tables plus the pinned consumer fallback predict retained LEF via R across MIN/TYP/MAX; actual Native extraction remains to be measured',
        'source_scope': 'ITF/draft arithmetic and selected LEF fields only; consumer source and planned microfixture are separate evidence',
    })


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--intake', type=Path, required=True)
    parser.add_argument('--tech-lef', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    need(not args.output.exists() and args.output.parent.is_dir(), 'Process review output must be fresh')
    result = audit(args.intake, args.tech_lef)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'output': str(args.output), 'qualified': False, 'native_executed': False,
                      'LEF_matches_MAX_for_all_selected_metals_and_vias': all(
                          x['retained_LEF_matches_this_ITF_corner'] for x in
                          result['corners']['MAX']['wires'] + result['corners']['MAX']['vias'])}, indent=2))


if __name__ == '__main__':
    main()
