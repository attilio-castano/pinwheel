"""Bound unchanged native checker; reconcile native text, sections and optional metrics."""
import json
from pathlib import Path
import re
import subprocess
import time
import traceback
from audits import sha, write
from antenna_results_v3 import parse_native, require, validate_reference

R = Path('/work/diagnostic')


def main():
    job = json.loads((R / 'report.json').read_text())
    prepared = json.loads((R / 'prepared.json').read_text())
    expected = json.loads((R / 'antenna-expected-v3.json').read_text())
    stop = min(job['native_stop_epoch'], prepared['native_work_stop_epoch'])
    with (R / 'antenna-native.log').open('w') as log:
        result = subprocess.run(['openroad', '-python', '-exit', '-threads', '4', '-no_splash',
            '-metrics', '/work/diagnostic/antenna-native-metrics.json', '/work/diagnostic/antenna_native_v2.py'],
            cwd=R, stdout=log, stderr=subprocess.STDOUT, timeout=max(1, stop-time.time()))
    require(result.returncode == 0, 'Native antenna/readback did not complete')
    measured = json.loads((R / 'measurement.json').read_text())
    require(measured['status'] == 'measured' and measured['checker_called'] is True
            and measured['full_scope_and_DEF_TAPER_exact'] is True, 'Native checker/scope proof incomplete')
    require(measured['source_database_sha256'] == expected['source_ODB_sha256'] == sha(R / 'input/checkpoint.odb'), 'Antenna source selection differs')
    require(measured['native_API']['command_present'] and measured['native_API']['Tcl_binding_check_only'], 'Native check-only API not qualified')
    metrics = json.loads((R / 'antenna-native-metrics.json').read_text())
    inventory = json.loads((R / 'input/inventory.json').read_text())
    parsed = parse_native((R / 'antenna-native.log').read_text(), metrics, measured['coverage'], inventory)
    reference_checked = validate_reference(parsed, expected)
    require(measured['coverage']['relevant_consumed_net_count'] == expected['consumed_net_count']
            and measured['coverage']['relevant_connected_INPUT_ITerm_count'] == expected['INPUT_contact_count'], 'Model/route coverage denominator changed')
    require((R / 'input/checkpoint.def').read_bytes() == (R / 'export/checkpoint.def').read_bytes() ==
            (R / 'antenna-after.def').read_bytes(), 'Raw full DEF/TAPER/PG changed')
    require((R / 'export/before-tech-0.lef').read_bytes() == (R / 'export/after-tech-0.lef').read_bytes() ==
            (R / 'antenna-after-tech-0.lef').read_bytes(), 'Native technology/NDR rules changed')
    measured.update(schema='pinwheel-check-only-antenna-v3', native_checker_exit_code=result.returncode,
        antenna_net_violation_count=parsed['native_net_violation_count'], antenna_pin_violation_count=parsed['native_pin_violation_count'],
        native_metrics=metrics, optional_metric_telemetry=parsed['optional_metric_telemetry'],
        native_report_reconciliation=parsed, same_source_reference_checked=reference_checked,
        same_source_reference_reproduced=True if reference_checked else None,
        diagnostic_antenna_violations_present=bool(parsed['native_net_violation_count']),
        zero_native_count_with_complete_declared_model_coverage=(
            parsed['native_net_violation_count'] == parsed['native_pin_violation_count'] == 0
            and measured['coverage']['all_input_gate_area_and_used_layer_rule_coverage_complete']
            and not any(re.search(r'THICKNESS|gate.area|antenna.rule', line, re.I)
                        for line in parsed['native_warnings_errors'])),
        antenna_pass_qualified=False, physical_acceptance_claim=False)
    write(R / 'measurement.json', measured)


if __name__ == '__main__':
    try:
        main()
    except BaseException as error:
        path = R / 'measurement.json'
        measured = json.loads(path.read_text()) if path.exists() else {}
        measured.update(status='failed', error=repr(error), traceback=traceback.format_exc(),
            antenna_pass_qualified=False, physical_acceptance_claim=False)
        write(path, measured)
        raise
