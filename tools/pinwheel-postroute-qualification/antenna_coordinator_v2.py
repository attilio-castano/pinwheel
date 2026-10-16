"""Bound the optional antenna subprocess; retain unqualified/missing data truthfully."""
import json
from pathlib import Path
import re
import subprocess
import time
import traceback

from audits import write

R = Path('/work/diagnostic')


def main():
    job = json.loads((R / 'report.json').read_text())
    prepared = json.loads((R / 'prepared.json').read_text())
    stop = min(job['native_stop_epoch'], prepared['native_work_stop_epoch'])
    with (R / 'antenna-native.log').open('w') as log:
        result = subprocess.run(['openroad', '-python', '-exit', '-threads', '4', '-no_splash',
            '-metrics', '/work/diagnostic/antenna-native-metrics.json', '/work/diagnostic/antenna_native_v2.py'],
            cwd=R, stdout=log, stderr=subprocess.STDOUT, timeout=max(1, stop-time.time()))
    assert result.returncode == 0, 'Native antenna/readback diagnostic did not complete'
    measured = json.loads((R / 'measurement.json').read_text())
    if measured['checker_called']:
        text = (R / 'antenna-native.log').read_text()
        for field, noun in [('antenna_net_violation_count', 'net'), ('antenna_pin_violation_count', 'pin')]:
            matches = re.findall(r'Found (\d+) ' + noun + r' violations\.', text)
            assert len(matches) == 1, 'Missing/ambiguous actual native antenna count'
            measured[field] = int(matches[0])
        measured['native_metrics'] = json.loads((R / 'antenna-native-metrics.json').read_text())
        assert measured['native_metrics']['antenna__violating__nets'] == measured['antenna_net_violation_count']
        assert measured['native_metrics']['antenna__violating__pins'] == measured['antenna_pin_violation_count']
        measured['native_warnings_errors'] = re.findall(r'^\[(?:WARNING|ERROR)\s+[^\]]+\].*$', text, re.M)
        model_warning = any(re.search(r'THICKNESS|gate.area|antenna.rule', line, re.I)
                            for line in measured['native_warnings_errors'])
        measured['zero_native_count_with_complete_declared_model_coverage'] = (
            measured['antenna_net_violation_count'] == measured['antenna_pin_violation_count'] == 0 and
            measured['coverage']['all_input_gate_area_and_used_layer_rule_coverage_complete'] and not model_warning)
    else:
        measured['zero_native_count_with_complete_declared_model_coverage'] = False
    # No broad acceptance: missing metadata, native warnings, internal SRAM
    # models and independent deck qualification need root review.
    measured['antenna_pass_qualified'] = False
    write(R / 'measurement.json', measured)


if __name__ == '__main__':
    try:
        main()
    except BaseException as error:
        p = R / 'measurement.json'
        measured = json.loads(p.read_text()) if p.exists() else {}
        measured.update(status='failed', error=repr(error), traceback=traceback.format_exc(),
            antenna_pass_qualified=False, physical_acceptance_claim=False)
        write(p, measured)
        raise
