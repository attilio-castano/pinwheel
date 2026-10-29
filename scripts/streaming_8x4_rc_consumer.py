"""Owned CMOS5L R-consumer fixture and a rules-only VIARES repair experiment.

`prepare` is HOST geometry/data work. `run` executes six fresh OpenROAD
processes and requires separate Root GO/resource admission. Passing this
experiment establishes a small consumer/arithmetic seam, not process RC signoff.
"""
import argparse
from decimal import Decimal
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parent))
import streaming_8x4_rc_process as P

D = Decimal
POLICIES = ('retained_rules', 'owned_explicit_via_rules')
WIDTHS = {'Metal1': D('.16'), 'Metal2': D('.20'), 'Metal3': D('.20'),
          'Metal4': D('.20'), 'TopMetal1': D('1.64')}
VIA_FIXTURES = ('Via1_XX', 'Via1_DC1B', 'Via2_XX', 'Via3_XX', 'TopVia1EWNS')


def need(value, message):
    P.need(value, message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def repair_rules(text, inventory, itf):
    """Only replace the one empty VIARES stanza; retain every other byte."""
    pattern = r'(?m)^VIARES 0 Default LEF Vias:\r?\nEND VIARES\r?\n'
    matches = list(re.finditer(pattern, text))
    need(len(matches) == 1, 'Expected exactly one empty draft VIARES stanza')
    rows = []
    for name, via in sorted(inventory['explicit_vias'].items()):
        layer = via['cut_layer']; count = via['cut_count']
        ref = itf['VIA', layer]
        bottom = list(P.METALS).index(ref['FROM']) + 1
        top = list(P.METALS).index(ref['TO']) + 1
        bbox = via['cut_bbox_um']
        dx, dy = (int((bbox[i + 2] - bbox[i]) * 1000) for i in (0, 1))
        need(dx > 0 and dy > 0 and top == bottom + 1 and count > 0, 'Invalid via repair metadata')
        value = ref['RPV'] / count
        rows.append(f'{value} {name} cuts {count} TopMetal {top} BotMetal {bottom} dx {dx} dy {dy}')
    replacement = f'VIARES {len(rows)} Default LEF Vias:\n' + '\n'.join(rows) + '\nEND VIARES\n'
    match = matches[0]
    result = text[:match.start()] + replacement + text[match.end():]
    need(result[:match.start()] == text[:match.start()] and result.endswith(text[match.end():]),
         'Non-VIARES bytes changed')
    return result, rows


def fixtures(inventory):
    rows = []
    for metal, width in WIDTHS.items():
        for length in (D(50), D(100)):
            rows.append({'name': f'{metal}_L{length}', 'segments': [(metal, str(length), str(width))], 'via': None})
    for metal, width in (('Metal1', D('.32')), ('Metal2', D('.40'))):
        rows.append({'name': metal + '_wide_L100', 'segments': [(metal, '100', str(width))], 'via': None})
    for name in VIA_FIXTURES:
        cut = inventory['explicit_vias'][name]['cut_layer']
        index = ('Via1', 'Via2', 'Via3', 'TopVia1').index(cut)
        lo, hi = P.METALS[index:index + 2]
        rows.append({'name': name, 'segments': [(lo, '50', str(WIDTHS[lo])), (hi, '50', str(WIDTHS[hi]))], 'via': name})
    return rows


def fixture_def(rows):
    """Separated straight series chains. This electrical fixture makes no DRC claim."""
    pins, nets = [], []
    for index, row in enumerate(rows):
        x0, y = 20000, (20 + index * 20) * 2000
        total = sum(D(s[1]) for s in row['segments'])
        x1 = x0 + int(total * 2000)
        a, b = row['name'] + '_A', row['name'] + '_B'
        for name, metal, x, direction in ((a, row['segments'][0][0], x0, 'INPUT'),
                                           (b, row['segments'][-1][0], x1, 'OUTPUT')):
            pins.append(f'- {name} + NET {row["name"]} + DIRECTION {direction} + USE SIGNAL\n'
                        f' + PORT + LAYER {metal} ( -100 -100 ) ( 100 100 ) + FIXED ( {x} {y} ) N ;')
        ndr = ' + NONDEFAULTRULE WIDE_' + row['segments'][0][0] if '_wide_' in row['name'] else ''
        route = f' + ROUTED {row["segments"][0][0]} ( {x0} {y} )'
        if row['via']:
            via_x = x0 + 100000
            route += f' ( {via_x} {y} ) {row["via"]} NEW {row["segments"][1][0]} ( {via_x} {y} ) ( {x1} {y} )'
        else:
            route += f' ( {x1} {y} )'
        nets.append(f'- {row["name"]} ( PIN {a} ) ( PIN {b} ){ndr}\n{route} ;')
    return ('VERSION 5.8 ;\nDIVIDERCHAR "/" ;\nBUSBITCHARS "[]" ;\nDESIGN rc_consumer ;\n'
            'UNITS DISTANCE MICRONS 2000 ;\nDIEAREA ( 0 0 ) ( 300000 800000 ) ;\n'
            'COMPONENTS 0 ;\nEND COMPONENTS\n'
            f'PINS {len(pins)} ;\n' + '\n'.join(pins) + '\nEND PINS\n'
            f'NETS {len(nets)} ;\n' + '\n'.join(nets) + '\nEND NETS\nEND DESIGN\n')


def ndr_lef():
    text = 'VERSION 5.8 ;\n'
    for metal, width in (('Metal1', '.32'), ('Metal2', '.40')):
        text += f'NONDEFAULTRULE WIDE_{metal}\n LAYER {metal}\n WIDTH {width} ;\n SPACING 0.21 ;\n END {metal}\nEND WIDE_{metal}\n'
    return text + 'END LIBRARY\n'


def tcl():
    return '''read_lef tech.lef
read_lef widths.lef
read_def fixture.def
write_def before.def
define_process_corner -ext_model_index 0 probe
extract_parasitics -ext_model_file rules.txt -no_merge_via_res -version 1.0
write_spef result.spef
write_def after.def
puts "PINWHEEL_CONSUMER_TERMINAL"
exit
'''


def prepare(intake, tech_lef, output):
    need(not output.exists() and output.parent.is_dir(), 'Prepared input directory must be fresh')
    texts, intake_manifest = P.verify_intake(intake)
    inventory = P.lef_resistance_inventory(tech_lef.read_text())
    rows = fixtures(inventory)
    need([r['name'] for r in rows] == P.consumer_protocol()['fixtures'], 'Declared consumer fixture membership differs')
    output.mkdir()
    inputs = {'tech.lef': tech_lef.read_bytes(), 'widths.lef': ndr_lef().encode(),
              'fixture.def': fixture_def(rows).encode(), 'run.tcl': tcl().encode()}
    corners = {}
    for corner in ('MIN', 'TYP', 'MAX'):
        itf = P.parse_stack(texts['itf_' + corner.lower()])
        raw = texts['draft_' + corner + '_rules']
        repaired, entries = repair_rules(raw, inventory, itf)
        inputs[corner + '-retained_rules.txt'] = raw.encode()
        inputs[corner + '-owned_explicit_via_rules.txt'] = repaired.encode()
        corners[corner] = {'wire_sheet_R': {m: str(itf['CONDUCTOR', m]['RPSQ']) for m in P.METALS},
                           'via_per_cut_R': {v: str(itf['VIA', v]['RPV']) for v in ('Via1', 'Via2', 'Via3', 'TopVia1')},
                           'repair_entries': entries}
    for name, data in inputs.items():
        (output / name).write_bytes(data)
    manifest = {'schema': 'pinwheel.streaming-8x4-rc-consumer-plan.v1', 'qualified': False,
                'model_qualified': False, 'native_executed': False,
                'protocol': {'policies': list(POLICIES), 'corners': ['MIN', 'TYP', 'MAX'],
                             'extractor_version': '1.0', 'fresh_process_per_corner_and_policy': True,
                             'wire_relative_tolerance': '0.001', 'via_relative_tolerance': '0.001',
                             'via_absolute_tolerance_ohm': '0.001', 'all_warnings_fatal': True,
                             'fixture_scope': 'straight synthetic chains; no DRC or device/process contact qualification',
                             'repair_scope': 'owned rules copies only, all explicit LEF tech-via names; no generated dbVia support claim',
                             'parallel_cut_assumption': 'identical independent cuts, per-cut ITF R divided by counted CUT rectangles',
                             'seconds_per_call': 30, 'maximum_calls': 6, 'work_seconds': 210,
                             'outer_seconds': 300, 'cpus': 1, 'memory_bytes': 2147483648,
                             'scratch_bytes': 134217728, 'root_go_required': True},
                'source_pins': P.consumer_protocol(),
                'producer_sha256': {Path(__file__).name: P.sha(__file__), 'streaming_8x4_rc_process.py': P.sha(P.__file__),
                                    'streaming_tt_rc_compare.py': P.sha(Path(P.__file__).with_name('streaming_tt_rc_compare.py'))},
                'process_intake_manifest_sha256': P.sha(Path(intake) / 'manifest.json'),
                'fixture_rows': rows, 'LEF_inventory': P.stringify(inventory), 'corners': corners,
                'files_sha256': {name: digest(data) for name, data in inputs.items()}}
    (output / 'plan.json').write_text(json.dumps(manifest, indent=2) + '\n')
    return {'prepared': str(output), 'plan_sha256': P.sha(output / 'plan.json'), 'native_executed': False}


def parse_spef(text, expected):
    """Strict supported SPEF subset, with complete connected series R graphs."""
    units = re.findall(r'^\*R_UNIT\s+(' + P.NUM + r')\s+(OHM|KOHM)\s*$', text, re.M)
    need(len(units) == 1, 'Missing/duplicate/unsupported SPEF R unit')
    factor = D(units[0][0]) * (1000 if units[0][1] == 'KOHM' else 1)
    need(factor.is_finite() and factor > 0, 'Nonpositive/nonfinite SPEF unit')
    names = {}
    name_block = re.findall(r'^\*NAME_MAP\s*\n(.*?)(?=^\*(?:PORTS|D_NET)\b)', text, re.M | re.S)
    need(len(name_block) <= 1, 'Duplicate NAME_MAP')
    if name_block:
        for line in name_block[0].splitlines():
            if not line.strip():
                continue
            match = re.fullmatch(r'\s*(\*\d+)\s+(\S+)\s*', line)
            need(match and match[1] not in names, 'Invalid/duplicate SPEF name mapping')
            names[match[1]] = match[2]
    def resolve(name):
        prefix, separator, rest = name.partition(':')
        return names.get(prefix, prefix) + (separator + rest if separator else '')
    blocks = re.findall(r'^\*D_NET\s+(\S+)\s+(' + P.NUM + r')\s*\n(.*?)^\*END\s*$', text, re.M | re.S)
    need(len(blocks) == text.count('*D_NET') == len(expected), 'Missing/truncated/extra SPEF net')
    result = {}
    for net_token, capacitance, body in blocks:
        net = resolve(net_token)
        need(net in expected and net not in result, 'Unexpected/duplicate SPEF net')
        need(D(capacitance).is_finite() and D(capacitance) >= 0, 'Invalid SPEF total capacitance')
        conn = re.findall(r'^\*CONN\s*\n(.*?)(?=^\*(?:CAP|RES)\b)', body, re.M | re.S)
        resistors = re.findall(r'^\*RES\s*\n(.*)\Z', body, re.M | re.S)
        need(len(conn) == len(resistors) == 1, 'Missing/duplicate SPEF CONN/RES')
        ports = []
        for line in conn[0].splitlines():
            if not line.strip():
                continue
            match = re.fullmatch(r'\s*\*P\s+(\S+)\s+[IOB](?:\s+.*)?', line)
            need(match is not None, 'Unsupported SPEF terminal')
            ports.append(resolve(match[1]))
        need(set(ports) == {net + '_A', net + '_B'} and len(ports) == 2, 'SPEF two-port membership differs')
        adjacency = {}; edges = []; ids = set()
        for line in resistors[0].splitlines():
            if not line.strip():
                continue
            match = re.fullmatch(r'\s*(\d+)\s+(\S+)\s+(\S+)\s+(' + P.NUM + r')\s*', line)
            need(match and match[1] not in ids, 'Invalid/duplicate SPEF resistor row')
            ids.add(match[1]); a, b, value = resolve(match[2]), resolve(match[3]), D(match[4]) * factor
            need(a != b and value.is_finite() and value >= 0, 'Invalid/negative/nonfinite SPEF resistor')
            edges.append((a, b, value)); adjacency.setdefault(a, []).append(b); adjacency.setdefault(b, []).append(a)
        need(edges and all(len(neighbors) == (1 if node in ports else 2) for node, neighbors in adjacency.items())
             and set(ports) <= set(adjacency), 'SPEF resistor graph is not a two-terminal series chain')
        seen = set(); todo = [ports[0]]
        while todo:
            node = todo.pop()
            if node not in seen:
                seen.add(node); todo.extend(adjacency[node])
        need(seen == set(adjacency) and len(edges) + 1 == len(seen), 'Disconnected/cyclic SPEF resistor graph')
        result[net] = {'R_ohm': str(sum(x[2] for x in edges)), 'edges': len(edges), 'nodes': len(seen), 'R_unit_ohm': str(factor)}
    return result


def analyze_values(plan, corner, policy, values):
    expected = {row['name']: row for row in plan['fixture_rows']}
    need(set(values) == set(expected), 'Consumer fixture result membership differs')
    wire_results, via_results = [], []
    for name, row in expected.items():
        actual = D(values[name]['R_ohm'])
        if row['via'] is None:
            metal, length, width = row['segments'][0]
            target = D(plan['corners'][corner]['wire_sheet_R'][metal]) * D(length) / D(width)
            relative = abs(actual / target - 1)
            wire_results.append({'name': name, 'actual_R_ohm': str(actual), 'ITF_R_ohm': str(target),
                                 'relative_difference': str(relative), 'passed': relative <= D('.001')})
        else:
            wire = sum(D(values[metal + '_L50']['R_ohm']) for metal, _, _ in row['segments'])
            measured = actual - wire; via = plan['LEF_inventory']['explicit_vias'][name]
            target = (D(via['resistance_ohm']) if policy == 'retained_rules' else
                      D(plan['corners'][corner]['via_per_cut_R'][via['cut_layer']]) / via['cut_count'])
            passed = abs(measured - target) <= max(D('.001'), abs(target) * D('.001'))
            via_results.append({'name': name, 'cut_count': via['cut_count'], 'actual_chain_R_ohm': str(actual),
                                'matched_wire_control_R_ohm': str(wire), 'via_difference_R_ohm': str(measured),
                                'policy_target_R_ohm': str(target), 'passed': passed})
    return {'wires': wire_results, 'vias': via_results,
            'passed': all(x['passed'] for x in wire_results + via_results), 'model_qualified': False}


def verify_plan(base, plan_hash):
    need(P.sha(base / 'plan.json') == plan_hash, 'Frozen consumer plan differs')
    plan = json.loads((base / 'plan.json').read_text())
    need(plan['schema'] == 'pinwheel.streaming-8x4-rc-consumer-plan.v1' and plan['qualified'] is False,
         'Consumer plan schema/promotion differs')
    for name, value in plan['files_sha256'].items():
        path = base / name
        need(path.parent == base and not path.is_symlink() and P.sha(path) == value, 'Consumer input changed/escaped')
    for name, value in plan['producer_sha256'].items():
        need(P.sha(Path(__file__).with_name(name)) == value, 'Frozen consumer producer changed')
    return plan


def run(base, plan_hash, output):
    plan = verify_plan(base, plan_hash)
    need(not output.exists() and output.parent.is_dir(), 'Consumer output directory must be fresh')
    # Root separately observes image identity, Docker admission and cleanup.
    cg = Path('/sys/fs/cgroup'); memory = (cg / 'memory.max').read_text().strip()
    cpu = (cg / 'cpu.max').read_text().split(); swap = (cg / 'memory.swap.max').read_text().strip()
    pids = (cg / 'pids.max').read_text().strip()
    need(memory.isdigit() and 0 < int(memory) <= 2147483648 and swap == '0', 'Consumer memory/swap ceiling differs')
    need(len(cpu) == 2 and cpu[0].isdigit() and 0 < int(cpu[0]) <= int(cpu[1]), 'Consumer CPU ceiling differs')
    need(pids.isdigit() and 0 < int(pids) <= 256, 'Consumer PID ceiling differs')
    output.mkdir(); started = time.monotonic(); jobs = []
    report = {'schema': 'pinwheel.streaming-8x4-rc-consumer-execution.v1', 'plan_sha256': plan_hash,
              'passed': False, 'qualified': False, 'model_qualified': False, 'jobs': jobs}
    try:
        for corner in ('MIN', 'TYP', 'MAX'):
            for policy in POLICIES:
                need(time.monotonic() - started < 175, 'Insufficient predeclared consumer work budget')
                directory = output / (corner + '-' + policy); directory.mkdir()
                for name in ('tech.lef', 'widths.lef', 'fixture.def', 'run.tcl'):
                    shutil.copyfile(base / name, directory / name)
                shutil.copyfile(base / (corner + '-' + policy + '.txt'), directory / 'rules.txt')
                before = {p.name: P.sha(p) for p in directory.iterdir()}
                log = directory / 'native.log'; command = ['openroad', '-no_init', '-exit', 'run.tcl']
                child = None
                with log.open('wb') as stream:
                    child = subprocess.Popen(command, cwd=directory, stdout=stream, stderr=subprocess.STDOUT,
                                             start_new_session=True)
                    try:
                        code = child.wait(timeout=30)
                    except subprocess.TimeoutExpired:
                        os.killpg(child.pid, signal.SIGKILL); child.wait()
                        raise ValueError('Consumer OpenROAD timeout')
                need(type(code) is int and code == 0, 'Consumer OpenROAD nonzero exit')
                try:
                    os.killpg(child.pid, 0)
                except ProcessLookupError:
                    pass
                else:
                    os.killpg(child.pid, signal.SIGKILL)
                    raise ValueError('Consumer OpenROAD left a live process group')
                raw = log.read_text()
                need(not re.search(r'(?im)\b(?:warning|warn|error|fatal)\b', raw), 'Consumer native warning/error')
                need(raw.count('PINWHEEL_CONSUMER_TERMINAL') == 1, 'Missing/duplicate terminal marker')
                need((directory / 'before.def').read_bytes() == (directory / 'after.def').read_bytes(),
                     'Extraction changed geometry DEF readback')
                need(all(P.sha(directory / name) == value for name, value in before.items()), 'Copied consumer input changed')
                values = parse_spef((directory / 'result.spef').read_text(), {r['name'] for r in plan['fixture_rows']})
                result = analyze_values(plan, corner, policy, values)
                jobs.append({'corner': corner, 'policy': policy, 'argv': command, 'exit_code': code,
                             'native_log_sha256': P.sha(log), 'SPEF_sha256': P.sha(directory / 'result.spef'),
                             'geometry_unchanged': True, 'copied_inputs_unchanged': True,
                             'process_tree_reaped': True, 'values': values, 'analysis': result})
                # Record all six measurements without adapting or silently dropping failed numeric controls.
        verify_plan(base, plan_hash)
        report['inputs_unchanged'] = True
        report['passed'] = len(jobs) == 6 and all(j['analysis']['passed'] for j in jobs)
    except Exception as error:
        report['error'] = type(error).__name__ + ': ' + str(error)
    report['wall_seconds'] = time.monotonic() - started
    (output / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='action', required=True)
    p = sub.add_parser('prepare'); p.add_argument('--intake', type=Path, required=True)
    p.add_argument('--tech-lef', type=Path, required=True); p.add_argument('--output', type=Path, required=True)
    p = sub.add_parser('run'); p.add_argument('--inputs', type=Path, required=True)
    p.add_argument('--plan-sha256', required=True); p.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = (prepare(args.intake, args.tech_lef, args.output) if args.action == 'prepare' else
              run(args.inputs, args.plan_sha256, args.output))
    print(json.dumps(result, indent=2))
    if args.action == 'run' and not result['passed']:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
