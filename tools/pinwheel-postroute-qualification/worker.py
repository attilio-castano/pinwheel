"""Run only one named isolated verification phase inside the pinned image."""
from __future__ import annotations
import hashlib
import inspect
import json
from decimal import Decimal
from pathlib import Path
import re
import subprocess
import time
import traceback

from audits import annotation_audit, audit_spef, sha, spice_headers, write

R = Path('/work/diagnostic')


def plain(value):
    # Explicitly materialize native Metrics wrappers at callers. Unknown
    # serialization types fail closed instead of becoming plausible strings.
    def decimal_only(item):
        if isinstance(item, Decimal):
            return float(item)
        raise TypeError('Unsupported native metric/config value: ' + type(item).__name__)
    return json.loads(json.dumps(value, default=decimal_only, allow_nan=False))


def main():
    from librelane.common import get_script_dir
    from librelane.flows.classic import Classic
    from librelane.state import State, DesignFormat
    from librelane.steps.openroad import RCX, STAPostPNR
    from librelane.steps.klayout import StreamOut as KStreamOut, DRC as KDRC
    from librelane.steps.magic import SpiceExtraction
    from librelane.steps.netgen import LVS

    request = json.loads((R / 'prepared.json').read_text())
    phase = json.loads((R / 'phase.json').read_text())
    receipt = json.loads((R / 'report.json').read_text())
    stop = min(receipt['native_stop_epoch'], phase['native_work_stop_epoch'])
    assert time.time() < stop
    for name, digest in request['staged_sha256'].items():
        assert sha(R / name) == digest, 'Changed prepared native input: ' + name
    captured = json.loads((R / 'native-assets.json').read_text())
    classes = {'OpenROAD.RCX': RCX, 'OpenROAD.STAPostPNR': STAPostPNR,
        'KLayout.StreamOut': KStreamOut, 'KLayout.DRC': KDRC,
        'Magic.SpiceExtraction': SpiceExtraction, 'Netgen.LVS': LVS}
    assets = {}
    for name, cls in classes.items():
        actual = inspect.getsource(cls)
        expected = captured['step_classes'][name]['source']
        assert actual == expected, 'Installed step class changed: ' + name
        assets[name] = hashlib.sha256(actual.encode()).hexdigest()
    scripts = Path(get_script_dir())
    for name, text in captured['scripts'].items():
        assert (scripts / name).read_text() == text, 'Installed script changed: ' + name
        assets[name] = sha(scripts / name)
    write(R / 'verified-native-assets.json', assets)
    inv = json.loads((R / 'input/inventory.json').read_text())
    measured = {'schema': 'pinwheel-isolated-postroute-measurement-v1', 'phase': phase['phase'],
        'status': 'running', 'source_database_sha256': sha(R / 'input/checkpoint.odb'),
        'source_DEF_sha256': sha(R / 'input/checkpoint.def'),
        'source_SDC_sha256': sha(R / 'input/core.sdc'),
        'completed_stages': [], 'physical_acceptance_claim': False,
        'official_precheck_qualified': False, 'internal_SRAM_LVS_qualified': False}
    write(R / 'measurement.json', measured)

    def check_time():
        assert time.time() < stop, 'Absolute native verification deadline reached'

    def checkpoint():
        write(R / 'measurement.json', measured)

    check_time()
    with (R / 'export-native.log').open('w') as log:
        subprocess.run(['openroad', '-python', '-exit', '-threads', '4', '-no_splash',
                        '/work/diagnostic/export_native.py'], cwd=R, stdout=log,
                        stderr=subprocess.STDOUT, check=True, timeout=max(1, stop-time.time()))
    scope = json.loads((R / 'export/scope.json').read_text())
    assert scope['status'] == 'passed'
    measured['export_scope'] = scope
    measured['completed_stages'].append('same-ODB-readback-and-netlist-export')
    checkpoint()

    data = json.loads((R / 'core/core.json').read_text())
    # Classic is used only to resolve Config; Classic.start is never called.
    # Flow substitution metadata names placement/PG plugins that must not be
    # registered or executed during isolated verification. The source stays
    # byte-bound; no physical/timing configuration keys are removed.
    measured['unused_flow_only_metadata'] = data.pop('meta', None)
    data.update(OPENROAD_THREADS=4, STA_THREADS=1,
        PNR_SDC_FILE=str(R / 'input/core.sdc'), SIGNOFF_SDC_FILE=str(R / 'input/core.sdc'),
        FALLBACK_SDC=str(R / 'input/core.sdc'), RCX_SDC_FILE=str(R / 'input/core.sdc'))
    base = {'def': str(R / 'input/checkpoint.def'), 'odb': str(R / 'input/checkpoint.odb'),
        'nl': str(R / 'export/netlist.v'), 'pnl': str(R / 'export/powered.v'),
        'sdc': str(R / 'input/core.sdc'), 'metrics': {}}
    views = {'nl': base['nl'], 'pnl': base['pnl']}

    def config(extra=None):
        cfg = dict(data)
        if extra:
            cfg.update(extra)
        return Classic(cfg, pdk_root='/work/pdk', pdk='ihp-sg13cmos5l',
                       design_dir=str(R / 'core')).config

    def run_step(cls, name, state, cfg):
        check_time()
        result = cls(config=cfg, state_in=State.load(dict(state, metrics={}))).start(step_dir=str(R / name))
        check_time()
        measured['completed_stages'].append(name)
        checkpoint()
        return result

    if phase['phase'] == 'rcx-sta':
        cfg = config()
        assert set(cfg['STA_CORNERS']) == set(request['expected_corners'])
        rules = {str(k): str(v) for k, v in cfg['RCX_RULESETS'].items()}
        assert list(rules) == ['nom_*'], 'Unexpected RC corner model set'
        rule_text = Path(next(iter(rules.values()))).read_text()
        assert 'LayerCount 7' in rule_text
        assert 'DensityModel 0' in rule_text
        used = sorted(set(layer for layers in scope['used_routing_layers'].values() for layer in layers))
        levels = dict(scope['technology_routing_levels'])
        assert set(used) <= {'Metal1', 'Metal2', 'Metal3', 'Metal4'}
        common = ['Metal1', 'Metal2', 'Metal3', 'Metal4']
        assert all(levels[name] == int(name[5:]) for name in common)
        measured['RC_model'] = {'rulesets': rules,
            'rules_sha256': {name: sha(path) for name, path in rules.items()},
            'source_layer_count': 7, 'source_density_model_index': 0,
            'used_layer_name_to_index': {name: levels[name] for name in used},
            'common_technology_layer_name_to_index': {name: levels[name] for name in common},
            'common_used_layer_indices_verified': True,
            'CMOS5L_physical_stack_accuracy_qualified': False,
            'qualification': request['RCX_qualification']}
        checkpoint()
        extracted = run_step(RCX, 'rcx', {'def': base['def'], 'sdc': base['sdc']}, cfg)
        spefs = {str(k): str(v) for k, v in extracted[DesignFormat.SPEF].items()}
        assert set(spefs) == {'nom_*'}, 'RCX did not produce the single expected nominal model'
        measured['SPEF'] = spefs
        measured['SPEF_coverage'] = {}
        for name, path in spefs.items():
            assert Path(path).is_file() and Path(path).stat().st_size > 0
            coverage = audit_spef(Path(path).read_text(), inv)
            write(R / 'SPEF-coverage.json', coverage)
            measured['SPEF_coverage'][name] = coverage
            checkpoint()
            assert coverage['status'] == 'passed', 'Extracted consumed-pin SPEF coverage failed'
        measured['three_Liberty_corners_on_one_nominal_RC_model'] = True
        measured['corner_results'] = {}
        for corner in request['expected_corners']:
            cfg = config({'DEFAULT_CORNER': corner, 'STA_CORNERS': [corner],
                          'STA_EXTRA_CORNER_TCL_FILE': str(R / 'analysis.tcl')})
            state = dict(base, spef=spefs)
            result = run_step(STAPostPNR, 'sta/' + corner, state, cfg)
            metrics = plain(dict(result.metrics))
            assert all('__corner:' not in k or k.endswith('__corner:' + corner) for k in metrics)
            for key in ('timing__setup__ws', 'timing__hold__ws'):
                assert key + '__corner:' + corner in metrics, 'Missing fresh corner metric: ' + key
            reports = list((R / 'sta' / corner).rglob('checks.rpt'))
            assert len(reports) == 1, 'Missing/ambiguous fresh annotation report'
            annotation = annotation_audit(reports[0].read_text(), inv)
            clock_reports = list((R / 'sta' / corner).rglob('qualification-clock.rpt'))
            assert len(clock_reports) == 1, 'Missing native clock qualification report'
            clock_text = clock_reports[0].read_text()
            assert re.findall(r'^PINWHEEL_CLOCK_COUNT (\d+)$', clock_text, re.M) == ['1']
            assert re.findall(r'^PINWHEEL_PROPAGATED_CLOCK (\S+)$', clock_text, re.M) == ['1']
            period = re.findall(r'^PINWHEEL_CLOCK_PERIOD (\S+)$', clock_text, re.M)
            assert len(period) == 1 and abs(float(period[0]) - 20) < 1e-9
            measured['corner_results'][corner] = {'metrics': metrics, 'annotation': annotation,
                'checks_report': str(reports[0]), 'checks_sha256': sha(reports[0]),
                'clock_report': str(clock_reports[0]), 'clock_report_sha256': sha(clock_reports[0]),
                'single_20ns_propagated_clock_verified': True,
                'Liberty_temperature_qualification': request['FAST_qualification'] if 'fast' in corner else 'matched declared temperature'}
            checkpoint()
            assert annotation['status'] == 'passed', 'Consumed/partial/unresolved unannotated timing nets'
        views.update({'spef': spefs})

    elif phase['phase'] == 'streamout':
        result = run_step(KStreamOut, 'klayout-streamout', base, config())
        views['gds'] = str(result[DesignFormat.GDS])
        assert Path(views['gds']).is_file() and Path(views['gds']).stat().st_size > 0
        measured['filler_density_qualification'] = 'No fill/finishing-cell insertion; diagnostic streamout of frozen inventory'

    elif phase['phase'] in ('lef-lvs', 'gds-lvs'):
        mapping = json.loads((R / 'macro-port-map.json').read_text())
        # This is an explicit boundary model, not the full SRAM transistor CDL.
        boundary = R / 'macro-boundary.spice'
        ports = [b for a, b in mapping['pairs']]
        boundary.write_text('.subckt ' + mapping['master'] + ' ' + ' '.join(ports) + '\n.ends ' + mapping['master'] + '\n')
        assert spice_headers(boundary.read_text())[mapping['master']] == ports
        cfg = config({'MAGIC_EXT_USE_GDS': phase['phase'] == 'gds-lvs',
            'MAGIC_EXT_ABSTRACT_CELLS': ['^' + mapping['master'] + '$'],
            'MAGIC_EXT_UNIQUE': 'all', 'MAGIC_EXT_SHORT_RESISTOR': False,
            'EXTRA_SPICE_MODELS': [str(boundary)], 'LVS_INCLUDE_MARCO_NETLISTS': False,
            'LVS_IGNORE_CELLS': [], 'LVS_FLATTEN_CELLS': []})
        state = dict(base, **phase['prior_views'])
        extracted = run_step(SpiceExtraction, 'magic-extraction', state, cfg)
        spice = str(extracted[DesignFormat.SPICE])
        assert Path(spice).is_file()
        state['spice'] = spice
        measured['extraction_metrics'] = plain(dict(extracted.metrics))
        measured['explicit_abstract_boundary'] = {'master': mapping['master'], 'port_count': len(ports),
            'reference_spice_sha256': sha(boundary), 'naming_bijection': mapping,
            'standard_cell_mode': 'LEF boundary abstractions' if phase['phase'] == 'lef-lvs' else 'actual streamed GDS extraction',
            'qualification': 'Native extraction/LVS across macro boundary only; no internal SRAM transistor claim'}
        standard_models = cfg.get('SPICE_MODELS') or cfg['CELL_SPICE_MODELS']
        assert standard_models, 'Reference standard-cell SPICE coverage required'
        assert phase.get('fixture_semantic_gate_sha256'), 'Explicit retained-macro sensitivity admission required'
        write(R / 'boundary-lvs-request.json', {'reference': base['pnl'], 'extracted': spice,
            'standard_spice_models': [str(path) for path in standard_models],
            'setup': '/work/pdk/ihp-sg13cmos5l/libs.tech/netgen/ihp-sg13cmos5l_setup.tcl',
            'native_stop_epoch': stop})
        with (R / 'boundary-lvs-native.log').open('w') as log:
            subprocess.run(['python3', '-B', '/work/diagnostic/boundary_lvs_native_v6.py'],
                cwd=R, stdout=log, stderr=subprocess.STDOUT, check=True, timeout=max(1, stop-time.time()))
        measured['native_boundary_LVS'] = json.loads((R / 'boundary-netgen-v6/measurement.json').read_text())
        measured['completed_stages'].append('explicit-boundary-netgen-v6')
        measured['native_LVS_negative_controls_run'] = False
        measured['LVS_acceptance_requires_independent_report_review'] = True
        views.update({'spice': spice})

    elif phase['phase'] == 'drc':
        cfg = config({'KLAYOUT_DRC_OPTIONS': {'no_recommended': 0, 'run_mode': 'deep'},
                      'KLAYOUT_DRC_THREADS': 4})
        result = run_step(KDRC, 'klayout-drc', dict(base, **phase['prior_views']), cfg)
        measured['DRC_metrics'] = plain(dict(result.metrics))
        measured['DRC_options'] = plain(cfg['KLAYOUT_DRC_OPTIONS'])
        measured['recommended_rules_enabled'] = True
        measured['qualification'] = 'Public PDK full-layout deck; distinct from official Tiny Tapeout dependency/runtime-pinned precheck, LVS and antenna'
    else:
        raise ValueError('Unknown phase')
    measured.update(status='measured', views=views,
        view_sha256={k: {a: sha(b) for a, b in v.items()} if isinstance(v, dict) else sha(v)
                     for k, v in views.items()})
    checkpoint()


if __name__ == '__main__':
    try:
        main()
    except BaseException as error:
        p = R / 'measurement.json'
        measured = json.loads(p.read_text()) if p.exists() else {'status': 'failed_before_measurement'}
        measured.update(status='failed', error=repr(error), traceback=traceback.format_exc(),
                        physical_acceptance_claim=False)
        write(p, measured)
        raise
