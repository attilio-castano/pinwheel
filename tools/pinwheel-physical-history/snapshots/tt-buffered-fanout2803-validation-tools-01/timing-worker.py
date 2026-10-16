"""Fresh native per-corner ODB STA; starts with no inherited timing metrics."""
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time
from librelane.common import get_script_dir

root = Path('/work/diagnostic')
inputs = json.loads((root / 'inputs.json').read_text())
scripts = Path(get_script_dir())
native = root / 'native-scripts'
script_hashes = {}
for name, expected in inputs['native_script_sha256'].items():
    source = scripts / name
    digest = hashlib.sha256(source.read_bytes()).hexdigest()
    assert digest == expected, (name, digest, expected)
    target = native / name
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(source, target)
    script_hashes[name] = digest
measurements = {}
for entry in inputs['corners']:
    corner = entry['name']
    folder = root / corner
    folder.mkdir()
    libs = ' '.join('/work/diagnostic/' + name for name in entry['libs'])
    # No inherited SPEF/SDF or metrics are consumed. Native ODB parasitics are estimated afresh.
    text = ('source /work/diagnostic/baseline-env.tcl\n'
            'foreach key [array names ::env _LIB_CORNER_*] {unset ::env($key)}\n'
            'foreach key [array names ::env *SPEF*] {unset ::env($key)}\n'
            'foreach key [array names ::env *SDF*] {unset ::env($key)}\n'
            'set ::env(CURRENT_ODB) /work/diagnostic/checkpoint.odb\n'
            'set ::env(_SDC_IN) /work/diagnostic/core.sdc\n'
            'set ::env(_LIB_CORNER_0) {' + corner + ' ' + libs + '}\n'
            'set ::env(_PNR_EXCLUDED_CELLS) {}\n'
            'set ::env(OPENROAD_THREADS) 3\n')
    env_file = folder / 'corner-env.tcl'
    env_file.write_text(text)
    env = dict(os.environ, SCRIPTS_DIR=str(scripts), _TCL_ENV_IN=str(env_file))
    command = ['openroad', '-exit', '-threads', '3', '-no_splash', '-metrics',
               str(folder / 'metrics.json'), str(scripts / 'openroad/sta/corner.tcl')]
    started = time.monotonic()
    with (folder / 'native.log').open('w') as log:
        result = subprocess.run(command, env=env, cwd=folder, stdout=log, stderr=subprocess.STDOUT)
    assert result.returncode == 0, (corner, result.returncode)
    log = (folder / 'native.log').read_text()
    for filename, body in re.findall(r'^%OL_CREATE_REPORT ([^\n]+)\n(.*?)^%OL_END_REPORT', log, re.M | re.S):
        assert Path(filename).name == filename
        (folder / filename).write_text(body)
    metrics = json.loads((folder / 'metrics.json').read_text())
    setup = float(metrics['timing__setup__ws__corner:' + corner])
    hold = float(metrics['timing__hold__ws__corner:' + corner])
    assert corner + ' Corner' in log
    assert all('__corner:' not in key or key.endswith('__corner:' + corner) for key in metrics)
    measurements[corner] = dict(setup_worst_slack_ns=setup, hold_worst_slack_ns=hold,
                                setup_met=setup >= 0, hold_met=hold >= 0,
                                qualification=entry['qualification'], fresh_metrics=metrics,
                                elapsed_seconds=round(time.monotonic() - started, 3), command=command)
    print(corner, 'setup', setup, 'hold', hold, flush=True)
nominal = measurements['nom_typ_1p20V_25C']
comparison = inputs['nominal_reference']
if comparison['same_database']:
    comparison['reproduced'] = (abs(nominal['setup_worst_slack_ns'] - comparison['setup_ns']) <= 1e-5
                               and abs(nominal['hold_worst_slack_ns'] - comparison['hold_ns']) <= 1e-5)
    assert comparison['reproduced'], comparison
else:
    comparison['reproduced'] = None
    comparison['reason'] = 'Selected newer ODB differs from nominal reference checkpoint.'
measurement = dict(status='measured', corners=measurements, native_script_sha256=script_hashes,
                   nominal_reference=comparison,
                   all_three_setup_hold_met=all(row['setup_met'] and row['hold_met'] for row in measurements.values()),
                   scope=inputs['scope'])
(root / 'measurement.json').write_text(json.dumps(measurement, indent=2) + '\n')
