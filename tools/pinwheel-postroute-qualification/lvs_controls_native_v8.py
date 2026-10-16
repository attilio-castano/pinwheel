"""Replay one positive and two explicit negative native Netgen comparisons."""
import json
import re
from pathlib import Path
import subprocess
import time
import traceback

from audits import sha, write
from lvs_case_verdict_v8 import native_case_verdict

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
    for case in ('positive', 'removed-terminal', 'bridged-nets', 'macro-detached-signal', 'macro-bridged-signals', 'macro-detached-VSS'):
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
        log = result.stdout + result.stderr
        assert not re.search(r'(?mi)^\s*(?:Error:|Tcl error|invalid command name)', log), 'Native parse/model error; mismatch cannot qualify a sensitivity fault'
        assert re.findall(r'^PINWHEEL_MACRO_MODEL1 (\S+)$', log, re.M) == ['blackbox']
        assert re.findall(r'^PINWHEEL_MACRO_MODEL2 (\S+)$', log, re.M) == ['blackbox']
        assert result.returncode == 0, 'Netgen did not complete a valid native comparison'
        json_path = out / 'lvs.json'
        parsed = json.loads(json_path.read_text())
        assert isinstance(parsed, list) and parsed, 'Missing/malformed native Netgen JSON'
        top = [row for row in parsed if row.get('name') == ['tt_um_pinwheel_buffered', 'tt_um_pinwheel_buffered']]
        assert len(top) == 1
        assert [dict(side) for side in top[0]['devices']] == [cfg['native_expected_top_devices_per_side']] * 2, 'Expected active BUF/DFF/macro hierarchy not retained'
        assert top[0]['nets'][0] == 352, 'Original source topology not retained in native comparison'
        if case == 'positive':
            assert len(top[0]['pins'][0]) == len(top[0]['pins'][1]) == 350, 'Expected complete top boundary port coverage missing'
        verdict = native_case_verdict(case, native, top[0], expected['mutation'])
        if case == 'positive':
            assert verdict['match_uniquely'] and verdict['targeted_native_evidence_verified'], 'Positive fixture must pass before any fault cases'
        report['cases'][case] = {**verdict, 'native_macro_model_queries': ['blackbox', 'blackbox'],
            'active_top_devices': top[0]['devices'], 'native_top_nets': top[0]['nets'],
            'native_top_pin_counts': [len(side) for side in top[0]['pins']],
            'independent_targeted_native_mismatch_semantic_review_required': True, 'native_exit_code': result.returncode, 'command': command,
            'expected_unique_match': expected['expected_unique_match'], 'expected_behavior_observed': True,
            'mutation': expected['mutation'], 'reference_sha256': sha(out / 'reference.v'),
            'script_sha256': sha(out / 'run.lvs'), 'native_report_sha256': sha(out / 'lvs.rpt'),
            'native_JSON_sha256': sha(json_path), 'native_log_sha256': sha(out / 'native.log')}
        write(R / 'measurement.json', report)
    assert all(item['match_uniquely'] == item['expected_unique_match'] for item in report['cases'].values()), 'Native fault comparison unexpectedly matched; all case artifacts retained'
    assert all(item['targeted_native_evidence_verified'] for item in report['cases'].values()), 'Unqualified targeted native mismatch; all diagnostic case artifacts retained'
    report.update(status='measured', positive_reproduced=True, removed_terminal_detected=True,
        deliberately_bridged_distinct_consumed_nets_detected=True,
        macro_signal_and_PG_faults_observed=True, independent_semantic_gate_still_required=True,
        sensitivity_coverage_qualified=False)
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
