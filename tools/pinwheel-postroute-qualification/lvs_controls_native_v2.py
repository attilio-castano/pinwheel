"""Replay one positive and two explicit negative native Netgen comparisons."""
import json
from pathlib import Path
import subprocess
import time
import traceback

from audits import sha, write
from lvs_mutants_v2 import native_verdict

R = Path('/work/diagnostic')


def main():
    cfg = json.loads((R / 'controls-config.json').read_text())
    receipt = json.loads((R / 'report.json').read_text())
    stop = min(receipt['native_stop_epoch'], cfg['prepared']['native_work_stop_epoch'])
    report = {'schema': 'pinwheel-native-LVS-sensitivity-measurement-v2', 'status': 'running',
        'positive_receipt_sha256': cfg['positive_receipt_sha256'], 'cases': {},
        'synthetic_fixture_only': cfg.get('synthetic_fixture_only', False),
        'geometry_or_extraction_qualified': False,
        'scope': cfg.get('scope', 'Copied complete actual positive reference/extraction sensitivity controls'),
        'original_layout_or_inputs_edited': False, 'internal_SRAM_qualified': False,
        'full_physical_connectivity_accepted': False}
    write(R / 'measurement.json', report)
    for case in ('positive', 'removed-terminal', 'bridged-nets'):
        assert time.time() < stop
        out = R / 'controls' / case
        expected = cfg['cases'][case]
        assert sha(out / 'reference.v') == expected['reference_sha256']
        assert sha(out / 'run.lvs') == expected['script_sha256']
        command = ['netgen', '-batch', 'source', str(out / 'run.lvs')]
        result = subprocess.run(command, capture_output=True, text=True, cwd=out,
            timeout=min(180, max(1, stop-time.time())))
        (out / 'native.log').write_text(result.stdout + result.stderr)
        native = (out / 'lvs.rpt').read_text() if (out / 'lvs.rpt').exists() else ''
        verdict = native_verdict(native)
        assert result.returncode == 0, 'Netgen did not complete a valid native comparison'
        json_path = out / 'lvs.json'
        parsed = json.loads(json_path.read_text())
        assert isinstance(parsed, (dict, list)) and parsed, 'Missing/malformed native Netgen JSON'
        assert verdict['match_uniquely'] == expected['expected_unique_match'], 'LVS sensitivity control failed'
        report['cases'][case] = {**verdict, 'native_exit_code': result.returncode, 'command': command,
            'expected_unique_match': expected['expected_unique_match'], 'expected_behavior_observed': True,
            'mutation': expected['mutation'], 'reference_sha256': sha(out / 'reference.v'),
            'script_sha256': sha(out / 'run.lvs'), 'native_report_sha256': sha(out / 'lvs.rpt'),
            'native_JSON_sha256': sha(json_path), 'native_log_sha256': sha(out / 'native.log')}
        write(R / 'measurement.json', report)
    report.update(status='measured', positive_reproduced=True, removed_terminal_detected=True,
        deliberately_bridged_distinct_consumed_nets_detected=True,
        sensitivity_coverage_qualified='Only these explicit signal-boundary faults; root must review all positive layout/model/port-coverage gates separately')
    write(R / 'measurement.json', report)


if __name__ == '__main__':
    try:
        main()
    except BaseException as error:
        path = R / 'measurement.json'
        report = json.loads(path.read_text()) if path.exists() else {}
        report.update(status='failed', error=repr(error), traceback=traceback.format_exc(),
            full_physical_connectivity_accepted=False)
        write(path, report)
        raise
