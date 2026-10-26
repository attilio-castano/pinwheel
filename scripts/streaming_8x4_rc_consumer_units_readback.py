"""HOST-only exact-unit and raw SPEF readback of the new typed consumer."""
import argparse
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import streaming_8x4_rc_consumer_units as U
import streaming_8x4_rc_consumer_readback as R


def readback(inputs, plan_hash, directory):
    plan = U.verify(inputs, plan_hash); path = directory / 'report.json'
    report = json.loads(path.read_text()); inner = directory / 'native/report.json'
    U.need(report['schema'] == 'pinwheel.streaming-8x4-rc-consumer-units-execution.v1'
        and report['plan_sha256'] == plan_hash and report['qualified'] is False and report['model_qualified'] is False
        and report['all_six_native_calls_closed'] is True and report['consumer_policy_unchanged'] is True
        and report['inputs_unchanged'] is True and report['inner_report_sha256'] == U.C.P.sha(inner),
        'Typed units execution did not close exact six-call membership')
    raw = R.readback(inputs / 'consumer-inputs', plan['consumer_plan_sha256'], directory / 'native')
    U.need(raw['workflow_passed'] == report['passed'], 'Outer/inner consumer numeric outcome differs')
    U.verify(inputs, plan_hash)
    return {'schema': 'pinwheel.streaming-8x4-rc-consumer-units-independent-readback.v1',
        'qualified': False, 'model_qualified': False, 'plan_sha256': plan_hash,
        'execution_report_sha256': U.C.P.sha(path), 'workflow_passed': raw['workflow_passed'],
        'all_six_native_calls_closed': True, 'exact_physical_coordinate_rescale_checked': True,
        'units_witness_sha256': plan['units_witness_sha256'], 'consumer_policy_unchanged': True,
        'raw_consumer_readback': raw,
        'resource_cleanup_join': 'separate exact Root resource-supervisor receipt remains mandatory'}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    for name in ('inputs', 'directory', 'output'): p.add_argument('--' + name, type=Path, required=True)
    p.add_argument('--plan-sha256', required=True); a = p.parse_args()
    result = readback(a.inputs, a.plan_sha256, a.directory); U.write(a.output, result)
    print(json.dumps({'workflow_passed': result['workflow_passed'], 'model_qualified': False}, indent=2))


if __name__ == '__main__':
    main()
