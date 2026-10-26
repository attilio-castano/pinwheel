"""Separately typed exact-DBU adapter for the frozen six-call R consumer.

The failed consumer02 experiment remains immutable. Only DEF integer units and
all integer coordinate pairs change; physical dimensions and numerical gates
remain exact. Root GO is required before the unchanged consumer executes.
"""
import argparse
import copy
from fractions import Fraction
import json
from pathlib import Path
import re
import shutil
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import streaming_8x4_rc_consumer as C

BASELINE_HASH = '51a58576fe349c88b6900185db8c7134172564d1ffcda40e46595747e3c1378a'
NEW_SCHEMA = 'pinwheel.streaming-8x4-rc-consumer-units-plan.v1'
PAIR = re.compile(r'(\(\s*)(-?\d+)(\s+)(-?\d+)(\s*\))')
HEADER = re.compile(r'(?m)^(UNITS DISTANCE MICRONS )(\d+)( ;)')
SOURCES = ('streaming_8x4_rc_consumer_units.py', 'streaming_8x4_rc_consumer_units_readback.py',
           'streaming_8x4_rc_consumer_readback.py')


def need(value, message):
    C.need(value, message)


def write(path, value):
    need(not path.exists(), 'Preserve existing units experiment artifact')
    path.write_text(json.dumps(value, indent=2) + '\n')


def lef_dbu(text):
    blocks = re.findall(r'(?ms)^UNITS\s*\n(.*?)^END UNITS\s*$', text)
    need(len(blocks) == 1, 'Missing/ambiguous actual technology LEF units')
    values = re.findall(r'(?m)^\s*DATABASE MICRONS\s+(\d+)\s*;\s*$', blocks[0])
    need(len(values) == 1 and int(values[0]) > 0, 'Missing/ambiguous/nonpositive technology DBU')
    return int(values[0])


def correct_def(original, target_dbu):
    headers = list(HEADER.finditer(original))
    need(len(headers) == 1 and type(target_dbu) is int and target_dbu > 0,
         'Missing/ambiguous DEF units or invalid target DBU')
    source_dbu = int(headers[0][2]); need(source_dbu > 0, 'Nonpositive original DEF DBU')
    rows = []
    def coordinate(match):
        before = [int(match[2]), int(match[4])]
        after = [Fraction(x * target_dbu, source_dbu) for x in before]
        need(all(v.denominator == 1 for v in after), 'DBU conversion would round a physical coordinate')
        after = [int(v) for v in after]
        need([Fraction(x, source_dbu) for x in before] == [Fraction(x, target_dbu) for x in after],
             'DBU conversion changes physical geometry')
        rows.append({'pair_index': len(rows), 'source_integer': before, 'target_integer': after,
                     'physical_um': [str(Fraction(x, source_dbu)) for x in before]})
        return match[1] + str(after[0]) + match[3] + str(after[1]) + match[5]
    converted = PAIR.sub(coordinate, original)
    converted = HEADER.sub(lambda m: m[1] + str(target_dbu) + m[3], converted)
    def signature(text):
        return HEADER.sub(lambda m: m[1] + '@DBU' + m[3],
                          PAIR.sub(lambda m: m[1] + '@X' + m[3] + '@Y' + m[5], text))
    need(rows and len(rows) == len(PAIR.findall(converted)) and signature(original) == signature(converted),
         'DEF membership or noncoordinate fields changed')
    return converted, {'schema': 'pinwheel.streaming-8x4-rc-consumer-exact-DBU-witness.v1',
        'source_DBU_per_um': source_dbu, 'target_DBU_per_um': target_dbu,
        'coordinate_pairs': rows, 'coordinate_pair_count': len(rows),
        'all_physical_coordinates_exactly_equal': True, 'noncoordinate_fields_unchanged': True,
        'rounding_used': False, 'physical_wire_lengths_um': [50, 100], 'qualified': False}


def producer_map(baseline):
    result = dict(baseline['producer_sha256'])
    for name in SOURCES:
        result[name] = C.P.sha(Path(__file__).with_name(name))
    return result


def inner_plan(baseline, fixture, producers):
    result = copy.deepcopy(baseline)
    result['files_sha256']['fixture.def'] = C.digest(fixture.encode())
    result['producer_sha256'] = producers
    result['unit_correction_scope'] = 'exact DEF DBU/coordinate rescale only; frozen fixture_rows/protocol/rules and physical dimensions unchanged'
    return result


def prepare(baseline, output):
    old = C.verify_plan(baseline, BASELINE_HASH)
    need(not output.exists() and output.parent.is_dir(), 'Units preparation owner must be fresh')
    original = (baseline / 'fixture.def').read_text(); dbu = lef_dbu((baseline / 'tech.lef').read_text())
    fixture, witness = correct_def(original, dbu)
    need(witness['source_DBU_per_um'] == 2000 and dbu == 1000, 'Observed consumer02 unit failure changed')
    producers = producer_map(old); adapted = inner_plan(old, fixture, producers)
    output.mkdir(); source = output / 'baseline'; source.mkdir(); inputs = output / 'consumer-inputs'; inputs.mkdir()
    shutil.copyfile(baseline / 'plan.json', source / 'plan.json')
    shutil.copyfile(baseline / 'fixture.def', source / 'fixture.def')
    for name in old['files_sha256']:
        shutil.copyfile(baseline / name, inputs / name)
    (inputs / 'fixture.def').write_text(fixture); write(inputs / 'plan.json', adapted)
    write(output / 'units-witness.json', witness)
    plan = {'schema': NEW_SCHEMA, 'qualified': False, 'model_qualified': False,
        'native_executed': False, 'root_go_required': True, 'baseline_plan_sha256': BASELINE_HASH,
        'baseline_fixture_sha256': old['files_sha256']['fixture.def'],
        'consumer_plan_sha256': C.P.sha(inputs / 'plan.json'), 'producer_sha256': producers,
        'units_witness_sha256': C.P.sha(output / 'units-witness.json'),
        'actual_technology_LEF_DBU_per_um': dbu, 'actual_technology_LEF_sha256': old['files_sha256']['tech.lef'],
        'protocol': old['protocol'], 'fixture_rows': old['fixture_rows'],
        'cause': 'consumer02 DEF2000DBU exceeded actual LEF1000DBU; OpenDB failed before extraction',
        'scope': 'same six corner/policy calls, R arithmetic and exact physical fixture; no tolerance/model/consumer-policy change'}
    write(output / 'plan.json', plan); C.verify_plan(baseline, BASELINE_HASH); verify(output, C.P.sha(output / 'plan.json'))
    return {'plan_sha256': C.P.sha(output / 'plan.json'), 'coordinate_pairs': witness['coordinate_pair_count'],
            'native_executed': False, 'model_qualified': False}


def verify(base, plan_hash):
    need(C.P.sha(base / 'plan.json') == plan_hash, 'Units plan identity differs')
    plan = json.loads((base / 'plan.json').read_text())
    need(plan['schema'] == NEW_SCHEMA and plan['qualified'] is False and plan['model_qualified'] is False
         and plan['native_executed'] is False and plan['root_go_required'] is True
         and plan['baseline_plan_sha256'] == BASELINE_HASH
         and C.P.sha(base / 'baseline/plan.json') == BASELINE_HASH,
         'Units typed scope/baseline/promotion differs')
    old = json.loads((base / 'baseline/plan.json').read_text()); inputs = base / 'consumer-inputs'
    need(C.P.sha(base / 'baseline/fixture.def') == old['files_sha256']['fixture.def'] == plan['baseline_fixture_sha256'],
         'Original failed DEF authority differs')
    expected_producers = producer_map(old)
    need(plan['producer_sha256'] == expected_producers, 'Units producer closure differs')
    for name, value in expected_producers.items():
        need(C.P.sha(Path(__file__).with_name(name)) == value, 'Frozen/new units producer bytes differ')
    dbu = lef_dbu((inputs / 'tech.lef').read_text())
    fixture, witness = correct_def((base / 'baseline/fixture.def').read_text(), dbu)
    need(dbu == plan['actual_technology_LEF_DBU_per_um'] == 1000 and witness['source_DBU_per_um'] == 2000
         and C.P.sha(inputs / 'tech.lef') == plan['actual_technology_LEF_sha256'] == old['files_sha256']['tech.lef']
         and C.P.sha(base / 'units-witness.json') == plan['units_witness_sha256']
         and json.loads((base / 'units-witness.json').read_text()) == witness
         and (inputs / 'fixture.def').read_text() == fixture,
         'Actual technology/exact physical coordinate witness differs')
    need(C.P.sha(inputs / 'plan.json') == plan['consumer_plan_sha256']
         and C.verify_plan(inputs, plan['consumer_plan_sha256']) == inner_plan(old, fixture, expected_producers)
         and plan['protocol'] == old['protocol'] and plan['fixture_rows'] == old['fixture_rows'],
         'Unchanged inner consumer protocol/geometry/rules differs')
    return plan


def run(base, plan_hash, output):
    plan = verify(base, plan_hash); need(not output.exists() and output.parent.is_dir(), 'Fresh units execution owner required')
    output.mkdir(); result = {'schema': 'pinwheel.streaming-8x4-rc-consumer-units-execution.v1',
        'qualified': False, 'model_qualified': False, 'plan_sha256': plan_hash, 'passed': False,
        'all_six_native_calls_closed': False, 'consumer_policy_unchanged': True}
    try:
        inner = C.run(base / 'consumer-inputs', plan['consumer_plan_sha256'], output / 'native')
        result.update(passed=inner['passed'], all_six_native_calls_closed=len(inner['jobs']) == 6,
                      inner_report_sha256=C.P.sha(output / 'native/report.json'))
    except BaseException as error:
        result['error'] = type(error).__name__ + ': ' + str(error)
    finally:
        result['inputs_unchanged'] = verify(base, plan_hash) == plan
        result['passed'] &= result['inputs_unchanged']; write(output / 'report.json', result)
    return result


def main():
    p = argparse.ArgumentParser(description=__doc__); sub = p.add_subparsers(dest='action', required=True)
    q = sub.add_parser('prepare'); q.add_argument('--baseline', type=Path, required=True); q.add_argument('--output', type=Path, required=True)
    for action in ('verify', 'run'):
        q = sub.add_parser(action); q.add_argument('--inputs', type=Path, required=True); q.add_argument('--plan-sha256', required=True)
        if action == 'run': q.add_argument('--output', type=Path, required=True)
    a = p.parse_args()
    result = prepare(a.baseline, a.output) if a.action == 'prepare' else verify(a.inputs, a.plan_sha256) if a.action == 'verify' else run(a.inputs, a.plan_sha256, a.output)
    print(json.dumps(result, indent=2))
    if a.action == 'run' and not result['passed']: raise SystemExit(1)


if __name__ == '__main__':
    main()
