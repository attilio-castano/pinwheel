"""Exact diagnostic admission for one completed native access-placement checkpoint."""
from pathlib import Path
import re
from common import ROOT, IMAGE, read, sha


def validate(design, state_path, manifest_path):
    design, state_path = design.resolve(), state_path.resolve()
    manifest = read(manifest_path)
    assert manifest['schema'] == 'pinwheel-buffered-tt-access-placement-checkpoint-admission-v1'
    assert design == (ROOT / manifest['design_path']).resolve()
    assert state_path == (ROOT / manifest['state_path']).resolve() and state_path.is_relative_to(design)
    state = read(state_path)
    prefix = '/work/recovery/'
    assert state['odb'].startswith(prefix)
    relative = Path(state['odb'][len(prefix):])
    assert not relative.is_absolute() and '..' not in relative.parts
    database = (design / relative).resolve()
    assert database.is_relative_to(design) and database == (ROOT / manifest['database_path']).resolve()
    assert sha(database) == manifest['database_sha256']
    files = {}
    for name, expected in manifest['files_sha256'].items():
        source = (ROOT / name).resolve()
        assert sha(source) == expected, name
        files[str(source)] = expected
    producer_path = (ROOT / manifest['producer_path']).resolve()
    producer = read(producer_path)
    assert producer_path.is_relative_to(design)
    assert producer['container_termination']['status'] == 'absent' and producer['inputs_unchanged']
    assert producer['runtime']['image_id'] == IMAGE
    assert producer['stop_after'] == 'OpenROAD.STAMidPNR-2'
    assert producer['preparation_sha256'] == manifest['preparation_sha256'] == sha(design / 'preparation.json')
    for name, expected in manifest['producer_artifacts_sha256'].items():
        assert producer['artifacts_sha256'][name] == expected
        assert sha(design / name) == expected
    assert manifest['state_path'] in manifest['files_sha256']
    assert manifest['database_path'] in manifest['files_sha256']
    assert manifest['producer_path'] in manifest['files_sha256']
    deferred = None
    if producer['status'] == 'failed':
        assert producer['exit_code'] == 2
        counts = manifest['inherited_power_metrics']
        assert counts == {'design__power_grid_violation__count': 30396,
                          'design__power_grid_violation__count__net:VGND': 10392,
                          'design__power_grid_violation__count__net:VPWR': 20004}
        assert all(state['metrics'][key] == value for key, value in counts.items())
        log_path = (ROOT / manifest['producer_log_path']).resolve()
        assert manifest['producer_log_path'] in manifest['files_sha256']
        log = log_path.read_text()
        assert re.search(r'One or more deferred errors were\s+encountered:', log)
        assert re.search(r'30396\s+power\s+grid\s+violations', log)
        deferred = 30396
    else:
        assert producer['status'] == 'passed' and producer['exit_code'] == 0
    nominal = 'nom_typ_1p20V_25C'
    assert state['metrics']['timing__setup__ws__corner:' + nominal] is not None
    assert state['metrics']['timing__hold__ws__corner:' + nominal] is not None
    core = read(design / 'core.json')
    assert core['MACROS']['RM_IHPSG13_1P_64x64_c2_bm_bist']['instances'] == {
        'engine.memory.storage0': {'location': [252, 30], 'orientation': 'N'},
        'engine.memory.storage1': {'location': [252, 144], 'orientation': 'N'}}
    return files, dict(overall_native_flow_status=producer['status'],
        overall_native_flow_exit_code=producer['exit_code'], completed_checkpoint_diagnostic_allowed=True,
        deferred_inherited_power_count=deferred, fresh_native_PSM_and_geometry_checks_waived=False,
        checkpoint_admission_sha256=sha(manifest_path))
