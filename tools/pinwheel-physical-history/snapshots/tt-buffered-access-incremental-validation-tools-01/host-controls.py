"""Labeled synthetic admission rejection controls; no native or CAD calls."""
from copy import deepcopy
import json
from pathlib import Path
import time
from admission import BOOL_GATES,SOURCE_ODB_SHA,movement_contract,rooted
from common import sha

OUT=Path(__file__).resolve().parent
started=time.monotonic()
assert not (OUT/'host-controls.json').exists()
policy={'allowed_movable_instances':['fixture_access0','fixture_neighbor0'],'protected_clock_instances':['fixture_clock0']}
odb='1'*64;nl='2'*64
baseline={**{k:True for k in BOOL_GATES},'status':'measured','source_database_sha256':SOURCE_ODB_SHA,
          'output_database_sha256':odb,'allowed_instance_names':policy['allowed_movable_instances'],
          'moved_instance_names':['fixture_access0'],'before_netlist_sha256':nl,'after_netlist_sha256':nl}
movement_contract(baseline,policy,odb,nl)
controls=['labeled valid structural fixture admitted']
def reject(label,mutate):
    value,p=deepcopy(baseline),deepcopy(policy)
    mutate(value,p)
    try:movement_contract(value,p,odb,nl)
    except (AssertionError,KeyError):controls.append(label);return
    raise AssertionError('Bad fixture admitted: '+label)
for key in BOOL_GATES:
    reject('false '+key+' rejected',lambda v,p,k=key:v.update({k:False}))
reject('wrong source ODB rejected',lambda v,p:v.update(source_database_sha256='3'*64))
reject('wrong candidate ODB rejected',lambda v,p:v.update(output_database_sha256='3'*64))
reject('allowlist enlargement after placement rejected',lambda v,p:v['allowed_instance_names'].append('fixture_outside0'))
reject('outside member movement rejected',lambda v,p:v['moved_instance_names'].append('fixture_outside0'))
reject('duplicate moved member rejected',lambda v,p:v['moved_instance_names'].append('fixture_access0'))
reject('protected clock in allowlist rejected',lambda v,p:p['protected_clock_instances'].append('fixture_access0'))
reject('netlist byte change rejected',lambda v,p:v.update(after_netlist_sha256='3'*64))
try:rooted('../outside-root')
except AssertionError:controls.append('path traversal rejected')
else:raise AssertionError('Traversal admitted')
report=dict(schema='pinwheel-buffered-tt-access-incremental-admission-host-controls-v1',status='passed',
            fixtures_are_synthetic=True,native_or_CAD_calls=0,controls_passed=len(controls),controls=controls,
            source_sha256={str(OUT/name):sha(OUT/name) for name in ('host-controls.py','admission.py','common.py')},
            host_elapsed_seconds=round(time.monotonic()-started,3),
            boundary='These synthetic host rejection controls validate intake guards; they are not placement/inventory/clock/power measurements or proof of a candidate.')
(OUT/'host-controls.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'controls_passed':len(controls),'host_elapsed_seconds':report['host_elapsed_seconds']}))
