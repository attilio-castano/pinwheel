"""Distinct four-call TYP M1 OpenRCX capacitance diagnostic; HOST prepare only by default.

No extraction-model promotion. Native execution requires separate Root GO and
the shared resource supervisor. Existing resistance consumers are not modified.
"""
import argparse
from decimal import Decimal as D
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
import streaming_8x4_rc_consumer_cap_spef as Q

REFERENCE_HASH = '185bac5e2f4346aeb03ebda83b827e7fb0336ffbc51c8a0a46f24b4b72aa910c'
NATIVE_HASH = '6ea3613a03b2c29b8706da76d02e5a4f67ae2f5dc6ff55ddfe5cc1e27b418cc4'
TABLE_HASH = 'bf2af2235b102d7bb58fe782d8d8b41a64cb3efde46593562314a499e9c4a612'
TECH_HASH = '3edd5a1ad31e8307be537d0d1b85c3258fefeb21aac04aaa476e4f72de4cffd5'
IMAGE = 'sha256:5825633bea1f9cbc705ece2de2bc31de6e4ec83d233739205a0f265ef9d92f92'
PYTHON = '/nix/store/lqn6mbgzzdrqq2qkwddcmxj9z6amdd86-python3-3.13.13/bin/python3'
OUTPUT = 'rc-consumer-cap-01'
JOBS = ['self-isolation512', 'self-isolation1024', 'pair-isolation512', 'pair-isolation1024']
CASES = ['TYP-w.16-self', 'TYP-w.16-s.18']
SOURCES = ['streaming_8x4_rc_consumer_cap.py', 'streaming_8x4_rc_consumer_cap_spef.py',
           'streaming_8x4_rc_consumer_cap_readback.py', 'streaming_8x4_rc_process.py', 'streaming_tt_rc_compare.py',
           'streaming_8x4_rc_layered_analyze.py']


def need(value, message):
    Q.need(value, message)


def write(path, value):
    need(not path.exists(), 'Preserve existing capacitance artifact')
    path.write_text(json.dumps(value, indent=2) + '\n')


def protocol():
    return {'case_ids': CASES, 'lengths_um': [50, 100, 150], 'width_um': '.16', 'pair_spacing_um': '.18',
        'group_separations_um': [512, 1024], 'outer_padding_um': [32, 64],
        'extractor_version': '1.0', 'coupling_threshold_fF': '0', 'cc_model': 10, 'context_depth': 5,
        'lef_res': False, 'lef_rc': False, 'merge_via_res': False,
        'wire_only_zero_cells_ITerms_and_routed_vias': True, 'all_warnings_fatal': True,
        'consecutive_length_slope_relative_tolerance': '.05', 'fixture_spacing_isolation_tolerance': '.02',
        'independent_comparison_tolerance': '.10', 'reference_mesh_and_domain_tolerance': '.02',
        'physical_reference_prerequisite': 'complete unchanged layered M1 reference04/native06 independent pass; original BEM length .05 and ground-boundary .02, mesh .02 gates unchanged',
        'spacing_control_scope': 'consumer fixture spacing/isolation control, not a physical ground-boundary experiment',
        'qualification_scope': 'two fixed TYP M1 drawn-width contexts only; all-layer/range/corner/foundry qualification false',
        'calls': 4, 'seconds_per_call': 30, 'work_seconds': 150, 'outer_seconds': 180,
        'cpus': 1, 'memory_bytes': 2147483648, 'scratch_bytes': 134217728, 'no_extra_swap': True}


def definition(job):
    need(job in JOBS, 'Undeclared capacitance job')
    pair = job.startswith('pair-'); separation = int(job.split('isolation')[1]); padding = 32 if separation == 512 else 64
    rows = []
    for i, length in enumerate((50, 100, 150)):
        for index in range(2 if pair else 1):
            net = ('pair' if pair else 'self') + '_L' + str(length) + '_W' + str(index + 1)
            y = (padding + i * separation) * 1000 + ((-170, 170)[index] if pair else 0)
            rows.append({'net': net, 'case': CASES[1 if pair else 0], 'length_um': length, 'conductor': 'W' + str(index + 1),
                         'start_DBU': [padding * 1000, y], 'end_DBU': [(padding + length) * 1000, y]})
    partners = {r['net']: None for r in rows}
    if pair:
        for length in (50, 100, 150):
            a, b = [r['net'] for r in rows if r['length_um'] == length]
            partners[a] = b; partners[b] = a
    return {'job': job, 'case': CASES[1 if pair else 0], 'separation_um': separation,
            'padding_um': padding, 'rows': rows, 'partners': partners,
            'diearea_DBU': [0, 0, (150 + 2 * padding) * 1000, (2 * separation + 2 * padding) * 1000]}


def fixture(row):
    pins = []; nets = []
    for wire in row['rows']:
        name = wire['net']; start, end = wire['start_DBU'], wire['end_DBU']
        for suffix, xy, direction in (('A', start, 'INPUT'), ('B', end, 'OUTPUT')):
            pins.append(f'- {name}_{suffix} + NET {name} + DIRECTION {direction} + USE SIGNAL\n'
                        f' + PORT + LAYER Metal1 ( -80 -80 ) ( 80 80 ) + FIXED ( {xy[0]} {xy[1]} ) N ;')
        nets.append(f'- {name} ( PIN {name}_A ) ( PIN {name}_B )\n'
                    f' + ROUTED Metal1 ( {start[0]} {start[1]} ) ( {end[0]} {end[1]} ) ;')
    _, _, xmax, ymax = row['diearea_DBU']
    return ('VERSION 5.8 ;\nDIVIDERCHAR "/" ;\nBUSBITCHARS "[]" ;\nDESIGN rc_cap_probe ;\n'
            'UNITS DISTANCE MICRONS 1000 ;\n' + f'DIEAREA ( 0 0 ) ( {xmax} {ymax} ) ;\n'
            'COMPONENTS 0 ;\nEND COMPONENTS\n' + f'PINS {len(pins)} ;\n' + '\n'.join(pins)
            + '\nEND PINS\n' + f'NETS {len(nets)} ;\n' + '\n'.join(nets) + '\nEND NETS\nEND DESIGN\n')


def tcl():
    return '''read_lef tech.lef
read_def fixture.def
set b [ord::get_db_block]
set iterms 0
foreach n [$b getNets] { incr iterms [llength [$n getITerms]] }
puts "PINWHEEL_CAP_INVENTORY insts=[llength [$b getInsts]] iterms=$iterms nets=[llength [$b getNets]] bterms=[llength [$b getBTerms]]"
set tech [[ord::get_db] getTech]
puts "PINWHEEL_CAP_TECH dbu=[$tech getDbUnitsPerMicron] m1_width=[[$tech findLayer Metal1] getWidth]"
write_def before.def
define_process_corner -ext_model_index 0 probe
extract_parasitics -ext_model_file rules.txt -version 1.0 -coupling_threshold 0 -cc_model 10 -context_depth 5 -no_merge_via_res
write_spef result.spef
write_def after.def
puts "PINWHEEL_CAP_TERMINAL"
exit
'''


def source_intake(base):
    manifest = json.loads((base / 'manifest.json').read_text())
    need(manifest['schema'] == 'pinwheel.streaming-8x4-rc-cap-source-intake.v1'
         and manifest['downloaded_code_executed'] is False, 'Cap writer source intake scope differs')
    need([r['name'] for r in manifest['files']] == ['extSpef.cpp', 'extSpef.h', 'dbNet.cpp', 'OpenSTA-Util.tcl'],
         'Cap source membership differs')
    for r in manifest['files']:
        path = base / r['name']; data = path.read_bytes()
        need(path.is_file() and not path.is_symlink() and len(data) == r['bytes']
             and hashlib.sha256(data).hexdigest() == r['sha256']
             and hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest() == r['git_blob'],
             'Cap source Git blob/SHA identity differs')
    return manifest


def technology_units_width(text):
    units = re.findall(r'(?ms)^UNITS\s*\n(.*?)^END UNITS\s*$', text)
    need(len(units) == 1 and re.findall(r'DATABASE MICRONS\s+(\d+)\s*;', units[0]) == ['1000'],
         'Cap technology database units differ')
    metal = re.findall(r'(?ms)^LAYER Metal1\s*\n(.*?)^END Metal1\s*$', text)
    need(len(metal) == 1, 'Cap technology M1 membership differs')
    widths = re.findall(r'(?m)^\s*WIDTH\s+(' + Q.NUM + r')\s*;', metal[0])
    need(len(widths) == 1 and D(widths[0]) == D('.16'), 'Cap technology default M1 width differs')
    return {'DBU_per_um': 1000, 'default_M1_width_DBU': 160}


def physical_join(selected):
    expected = [[['-.08', '.08', '1.04', '1.46']],
                [['-.25', '-.09', '1.04', '1.46'], ['.09', '.25', '1.04', '1.46']]]
    need([c['name'] for c in selected] == CASES, 'Cap physical reference membership differs')
    for case, rectangles in zip(selected, expected):
        need([r['name'] for r in case['rectangles']] == ['W' + str(i + 1) for i in range(len(rectangles))]
             and [[D(x) for x in r['bounds_um']] for r in case['rectangles']]
                 == [[D(x) for x in row] for row in rectangles], 'Cap reference-to-DEF exact cross-section differs')
    need(selected[0]['epsilon_layers'] == selected[1]['epsilon_layers'], 'Cap TYP self/pair material stack differs')
    return {'reference_transverse_x_equals_DEF_y_relative_to_group_center': True,
            'reference_extrusion_equals_DEF_x': True, 'all_DBU_coordinates_integral_at_1000_per_um': True,
            'rectangle_bounds_um': expected, 'full_Typical_epsilon_layers': selected[0]['epsilon_layers']}


def prepare(process_intake, cap_source, consumer_baseline, reference_plan, native_plan, output):
    need(not output.exists() and output.parent.is_dir(), 'Fresh capacitance preparation owner required')
    texts, _ = P.verify_intake(process_intake); source_intake(cap_source)
    need(P.sha(reference_plan) == REFERENCE_HASH and P.sha(native_plan) == NATIVE_HASH,
         'Frozen layered reference/native authority differs')
    reference = json.loads(reference_plan.read_text()); native = json.loads(native_plan.read_text())
    selected = [c for c in reference['cases'] if c['name'] in CASES]
    need([c['name'] for c in selected] == CASES and native['reference_plan_sha256'] == REFERENCE_HASH,
         'Reference physical case membership differs')
    tech = consumer_baseline / 'tech.lef'; table = consumer_baseline / 'TYP-owned_explicit_via_rules.txt'
    need(P.sha(tech) == TECH_HASH and P.sha(table) == TABLE_HASH, 'Exact owned TYP table/technology differs')
    technology = technology_units_width(tech.read_text()); physical = physical_join(selected)
    need(P.parse_stack(texts['itf_typ'])['CONDUCTOR', 'Metal1']['THICKNESS'] == D('.42'), 'M1 process thickness differs')
    output.mkdir(); shutil.copytree(process_intake, output / 'process-intake'); shutil.copytree(cap_source, output / 'source-evidence')
    shutil.copyfile(reference_plan, output / 'reference-plan.json'); shutil.copyfile(native_plan, output / 'native-plan.json')
    files = {'tech.lef': tech.read_bytes(), 'rules.txt': table.read_bytes(), 'run.tcl': tcl().encode()}
    for job in JOBS:
        files[job + '.def'] = fixture(definition(job)).encode()
    for name, data in files.items():
        (output / name).write_bytes(data)
    producers = {n: P.sha(Path(__file__).with_name(n)) for n in set(SOURCES) | set(reference['producers_sha256']) | set(native['producers_sha256'])}
    plan = {'schema': 'pinwheel.streaming-8x4-rc-consumer-cap-plan.v1', 'qualified': False, 'model_qualified': False,
        'native_executed': False, 'root_go_required': True, 'protocol': protocol(), 'reference_plan_sha256': REFERENCE_HASH,
        'native_plan_sha256': NATIVE_HASH, 'process_intake_manifest_sha256': P.sha(output / 'process-intake/manifest.json'),
        'source_intake_manifest_sha256': P.sha(output / 'source-evidence/manifest.json'), 'reference_cases': selected,
        'exact_physical_join': physical, 'technology_units_and_width': technology,
        'jobs': [definition(j) for j in JOBS], 'producer_sha256': dict(sorted(producers.items())),
        'files_sha256': {name: hashlib.sha256(data).hexdigest() for name, data in files.items()},
        'geometry_contract': 'M1 default drawn width .16um, reference transverse x mapped to DEF y and extrusion to DEF x; ITF vertical/ER stack from exact reference cases, implicit substrate model context; no standard-cell pin loads',
        'accuracy_state': 'unmeasured until unchanged complete reference and BEM prerequisites independently reopen'}
    write(output / 'plan.json', plan); verify(output, P.sha(output / 'plan.json'))
    return {'plan_sha256': P.sha(output / 'plan.json'), 'native_executed': False, 'model_qualified': False}


def verify(base, plan_hash):
    need(P.sha(base / 'plan.json') == plan_hash, 'Capacitance plan hash differs')
    plan = json.loads((base / 'plan.json').read_text())
    need(plan['schema'] == 'pinwheel.streaming-8x4-rc-consumer-cap-plan.v1' and plan['qualified'] is False
         and plan['model_qualified'] is False and plan['native_executed'] is False and plan['root_go_required'] is True
         and plan['protocol'] == protocol() and plan['jobs'] == [definition(j) for j in JOBS], 'Cap plan scope/membership differs')
    need(P.sha(base / 'reference-plan.json') == plan['reference_plan_sha256'] == REFERENCE_HASH
         and P.sha(base / 'native-plan.json') == plan['native_plan_sha256'] == NATIVE_HASH,
         'Cap frozen independent prerequisites differ')
    reference = json.loads((base / 'reference-plan.json').read_text()); native = json.loads((base / 'native-plan.json').read_text())
    selected = [c for c in reference['cases'] if c['name'] in CASES]
    need(plan['reference_cases'] == selected and [c['name'] for c in selected] == CASES,
         'Cap exact reference geometry/material/case binding differs')
    need(plan['exact_physical_join'] == physical_join(selected)
         and plan['technology_units_and_width'] == technology_units_width((base / 'tech.lef').read_text()),
         'Cap exact unit/cross-section witness differs')
    expected_sources = set(SOURCES) | set(reference['producers_sha256']) | set(native['producers_sha256'])
    need(set(plan['producer_sha256']) == expected_sources, 'Cap transitive producer membership differs')
    for name, value in plan['producer_sha256'].items():
        need(Path(name).name == name and P.sha(Path(__file__).with_name(name)) == value, 'Frozen cap/reference producer changed')
        for source in (reference['producers_sha256'], native['producers_sha256']):
            need(name not in source or source[name] == value, 'Inherited frozen producer identity differs')
    need(P.sha(base / 'process-intake/manifest.json') == plan['process_intake_manifest_sha256']
         and P.sha(base / 'source-evidence/manifest.json') == plan['source_intake_manifest_sha256'], 'Cap source manifest differs')
    P.verify_intake(base / 'process-intake'); source_intake(base / 'source-evidence')
    expected_files = {'tech.lef', 'rules.txt', 'run.tcl'} | {j + '.def' for j in JOBS}
    need(set(plan['files_sha256']) == expected_files, 'Cap complete input file membership differs')
    for name, value in plan['files_sha256'].items():
        path = base / name
        need(path.is_file() and not path.is_symlink() and P.sha(path) == value, 'Cap frozen input differs')
    need(P.sha(base / 'tech.lef') == TECH_HASH and P.sha(base / 'rules.txt') == TABLE_HASH
         and (base / 'run.tcl').read_text() == tcl()
         and all((base / (j + '.def')).read_text() == fixture(definition(j)) for j in JOBS), 'Cap exact fixture/policy/table changed')
    return plan


def validate_geometry(text, job):
    need(re.findall(r'^UNITS DISTANCE MICRONS\s+(\d+)\s*;', text, re.M) == ['1000']
         and re.findall(r'^COMPONENTS\s+(\d+)\s*;', text, re.M) == ['0'], 'Actual DEF DBU/cell inventory differs')
    section = re.findall(r'^NETS\s+(\d+)\s*;(.*?)^END NETS\s*$', text, re.M | re.S)
    need(len(section) == 1 and int(section[0][0]) == len(job['rows']), 'Actual DEF net count differs')
    rows = re.findall(r'^\s*-\s+(\w+)\s+(.*?);', section[0][1], re.M | re.S)
    need(len(rows) == len(job['rows']) and {n for n, _ in rows} == {r['net'] for r in job['rows']}, 'Actual DEF membership differs')
    expected = {r['net']: r for r in job['rows']}
    for name, body in rows:
        route = re.split(r'\+\s+ROUTED\s+', body)
        need(len(route) == 2 and re.fullmatch(r'Metal1\s+(?:\(\s*(?:-?\d+|\*)\s+(?:-?\d+|\*)\s*\)\s*){2}', route[1].strip()),
             'Actual routed via/width/metal/shape unsupported')
        points = re.findall(r'\(\s*(-?\d+|\*)\s+(-?\d+|\*)\s*\)', route[1]); previous = None; decoded = []
        for point in points:
            need(previous is not None or '*' not in point, 'Unbound DEF wildcard')
            xy = [previous[i] if x == '*' else int(x) for i, x in enumerate(point)]
            decoded.append(xy); previous = xy
        need(decoded == [expected[name]['start_DBU'], expected[name]['end_DBU']], 'Actual routed dimensions differ')
    return True


def parse_leaf(directory, job):
    raw = (directory / 'native.log').read_text()
    need(not re.search(r'(?im)\b(?:warning|warn|error|fatal)\b', raw)
         and raw.count('PINWHEEL_CAP_TERMINAL') == 1, 'Cap native warning/error/terminal gap')
    n = len(job['rows'])
    need(re.findall(r'PINWHEEL_CAP_INVENTORY insts=(\d+) iterms=(\d+) nets=(\d+) bterms=(\d+)', raw)
         == [('0', '0', str(n), str(2 * n))]
         and re.findall(r'PINWHEEL_CAP_TECH dbu=(\d+) m1_width=(\d+)', raw) == [('1000', '160')],
         'Actual native cells/ITerms/units/width inventory differs')
    before, after = directory / 'before.def', directory / 'after.def'
    need(before.read_bytes() == after.read_bytes(), 'Cap extraction changed actual geometry')
    validate_geometry(before.read_text(), job)
    return Q.parse((directory / 'result.spef').read_text(), [r['net'] for r in job['rows']], job['partners'])


def slopes(job, values):
    matrices = {int(re.search(r'_L(\d+)_', g['names'][0])[1]): g for g in values['groups']}
    need(set(matrices) == {50, 100, 150}, 'Cap complete length matrix membership differs')
    result = []
    for a, b in ((50, 100), (100, 150)):
        x, y = matrices[a]['matrix_F'], matrices[b]['matrix_F']
        matrix = [[(D(v) - D(u)) / D('50e-6') for u, v in zip(ar, br)] for ar, br in zip(x, y)]
        ground = [sum(row) for row in matrix]
        need(all(matrix[i][i] > 0 and ground[i] > 0 for i in range(len(matrix)))
             and all(matrix[i][j] < 0 for i in range(len(matrix)) for j in range(len(matrix)) if i != j),
             'Nonphysical length-slope Maxwell/ground/coupling')
        result.append({'length_pair_um': [a, b], 'matrix_F_per_m': [[str(x) for x in row] for row in matrix],
                       'ground_F_per_m': list(map(str, ground))})
    return result


def vector(row):
    return [D(x) for line in row['matrix_F_per_m'] for x in line] + [D(x) for x in row['ground_F_per_m']]


def relative(a, b):
    need(len(a) == len(b) and a and all(x != 0 for x in b), 'Invalid complete capacitance comparison')
    return max(abs(x / y - 1) for x, y in zip(a, b))


def measurements(rows):
    need([r['job'] for r in rows] == JOBS, 'Cap four-call membership differs')
    results = []; controls = []
    for job, row in zip(JOBS, rows):
        s = slopes(definition(job), row['values']); change = relative(vector(s[0]), vector(s[1]))
        results.append({'job': job, 'slopes': s, 'consecutive_slope_difference': str(change), 'passed': change <= D('.05')})
    for offset in (0, 2):
        changes = [relative(vector(a), vector(b)) for a, b in zip(results[offset]['slopes'], results[offset + 1]['slopes'])]
        controls.append({'case': CASES[offset // 2], 'spacing_isolation_differences': list(map(str, changes)),
                         'passed': max(changes) <= D('.02'), 'physical_boundary_test': False})
    return {'jobs': results, 'spacing_isolation_controls': controls,
            'measurement_controls_passed': all(r['passed'] for r in results + controls), 'model_qualified': False}


def cgroups():
    base = Path('/sys/fs/cgroup'); rows = {n: (base / n).read_text().strip() for n in ('cpu.max', 'memory.max', 'memory.swap.max', 'pids.max')}
    cpu = rows['cpu.max'].split()
    need(len(cpu) == 2 and cpu[0].isdigit() and 0 < int(cpu[0]) <= int(cpu[1])
         and rows['memory.max'].isdigit() and 0 < int(rows['memory.max']) <= 2147483648
         and rows['memory.swap.max'] == '0' and rows['pids.max'].isdigit() and 0 < int(rows['pids.max']) <= 128,
         'Cap actual cgroup ceiling differs')
    return rows


def run(base, plan_hash, output):
    plan = verify(base, plan_hash); cg = cgroups()
    need(not output.exists() and output.parent.is_dir(), 'Cap native output must be fresh')
    output.mkdir(); start = time.monotonic(); jobs = []
    report = {'schema': 'pinwheel.streaming-8x4-rc-consumer-cap-execution.v1', 'plan_sha256': plan_hash,
        'qualified': False, 'model_qualified': False, 'passed': False, 'measurement_packet_completed': False,
        'accuracy_status': 'unmeasured', 'independent_accuracy_passed': False, 'jobs': jobs, 'cgroups': cg}
    try:
        for job in plan['jobs']:
            need(time.monotonic() - start < 115, 'Insufficient fixed cap packet work budget')
            owner = output / job['job']; owner.mkdir()
            for name in ('tech.lef', 'rules.txt', 'run.tcl'):
                shutil.copyfile(base / name, owner / name)
            shutil.copyfile(base / (job['job'] + '.def'), owner / 'fixture.def')
            before = {p.name: P.sha(p) for p in owner.iterdir()}; child = None; timed_out = False
            command = ['openroad', '-no_init', '-exit', 'run.tcl']; leaf = {'job': job['job'], 'passed': False}
            with (owner / 'native.log').open('wb') as stream:
                child = subprocess.Popen(command, cwd=owner, stdout=stream, stderr=subprocess.STDOUT, start_new_session=True)
                try:
                    code = child.wait(timeout=30)
                except subprocess.TimeoutExpired:
                    timed_out = True; os.killpg(child.pid, signal.SIGKILL); code = child.wait()
            try:
                os.killpg(child.pid, 0)
            except ProcessLookupError:
                reaped = True
            else:
                os.killpg(child.pid, signal.SIGKILL); raise ValueError('Cap child left a process group')
            need(all(P.sha(owner / n) == h for n, h in before.items()), 'Copied cap inputs changed')
            leaf.update(argv=command, exit_code=code, timed_out=timed_out, process_tree_reaped=reaped,
                        copied_inputs_unchanged=True, copied_input_sha256=before, native_log_sha256=P.sha(owner / 'native.log'))
            try:
                need(type(code) is int and code == 0 and not timed_out, 'Cap OpenROAD exit/timeout failed')
                leaf['values'] = parse_leaf(owner, job); leaf['passed'] = True
            except (ValueError, OSError) as error:
                leaf['error'] = type(error).__name__ + ': ' + str(error)
            leaf['raw_output_sha256'] = {n: P.sha(owner / n) for n in ('before.def', 'after.def', 'result.spef') if (owner / n).is_file()}
            write(owner / 'report.json', leaf); jobs.append(dict(job=job['job'], passed=leaf['passed'], report_sha256=P.sha(owner / 'report.json')))
            # Preserve numeric failures and finish the fixed four calls; no adaptive retry.
        report['measurement_packet_completed'] = len(jobs) == 4
        if all(j['passed'] for j in jobs):
            leaves = [json.loads((output / j['job'] / 'report.json').read_text()) for j in jobs]
            report['analysis'] = measurements(leaves); report['passed'] = report['analysis']['measurement_controls_passed']
    except Exception as error:
        report['error'] = type(error).__name__ + ': ' + str(error)
    report['inputs_unchanged'] = verify(base, plan_hash) == plan
    report['wall_seconds'] = time.monotonic() - start; write(output / 'report.json', report)
    return report


def command_proposal(base, plan_hash, output_parent, require_fresh=True):
    plan = verify(base, plan_hash)
    need(output_parent.is_dir() and (not require_fresh or not (output_parent / OUTPUT).exists()), 'Cap output parent/freshness differs')
    argv = ['docker', 'run', '--name', 'pinwheel-8x4-rc-consumer-cap-01', '--rm', '--pull', 'never', '--network', 'none',
        '--read-only', '--cpus', '1', '--memory', '2g', '--memory-swap', '2g', '--pids-limit', '128', '--tmpfs',
        '/tmp:rw,nosuid,noexec,size=134217728', '--mount', 'type=bind,src=' + str(Path(__file__).parent.resolve()) + ',dst=/rc-source,readonly',
        '--mount', 'type=bind,src=' + str(base.resolve()) + ',dst=/rc-inputs,readonly', '--mount',
        'type=bind,src=' + str(output_parent.resolve()) + ',dst=/rc-output-parent', '--entrypoint', PYTHON, IMAGE,
        '-I', '-B', '/rc-source/' + Path(__file__).name, 'run', '--inputs', '/rc-inputs', '--plan-sha256', plan_hash,
        '--output', '/rc-output-parent/' + OUTPUT]
    return {'schema': 'pinwheel.streaming-8x4-rc-consumer-cap-command-proposal.v1', 'root_go_required': True,
        'admitted': False, 'native_executed': False, 'model_qualified': False, 'container_name': 'pinwheel-8x4-rc-consumer-cap-01',
        'timeout_seconds': 180, 'work_seconds': 150, 'maximum_calls': 4, 'plan_path': str((base / 'plan.json').resolve()),
        'plan_sha256': plan_hash, 'producer_sha256': plan['producer_sha256'], 'argv': argv}


def main():
    p = argparse.ArgumentParser(description=__doc__); sub = p.add_subparsers(dest='action', required=True)
    q = sub.add_parser('prepare')
    for n in ('process-intake', 'cap-source', 'consumer-baseline', 'reference-plan', 'native-plan', 'output'):
        q.add_argument('--' + n, type=Path, required=True)
    for action in ('verify', 'run', 'proposal'):
        q = sub.add_parser(action); q.add_argument('--inputs', type=Path, required=True); q.add_argument('--plan-sha256', required=True)
        if action != 'verify': q.add_argument('--output', type=Path, required=True)
        if action == 'proposal': q.add_argument('--output-parent', type=Path, required=True)
    a = p.parse_args()
    if a.action == 'prepare': result = prepare(a.process_intake, a.cap_source, a.consumer_baseline, a.reference_plan, a.native_plan, a.output)
    elif a.action == 'verify': result = verify(a.inputs, a.plan_sha256)
    elif a.action == 'run': result = run(a.inputs, a.plan_sha256, a.output)
    else:
        result = command_proposal(a.inputs, a.plan_sha256, a.output_parent); write(a.output, result)
    print(json.dumps(result, indent=2))
    if a.action == 'run' and not result['passed']: raise SystemExit(2)


if __name__ == '__main__': main()
