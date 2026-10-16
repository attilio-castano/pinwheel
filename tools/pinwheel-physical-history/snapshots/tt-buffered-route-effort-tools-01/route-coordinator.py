import os,subprocess,shutil,json,hashlib
from pathlib import Path
from librelane.common import get_script_dir
root=Path('/work/diagnostic');parameters=json.loads((root/'parameters.json').read_text());iterations=parameters['native_iterations_per_segment'];assert iterations in (5,10);scripts=Path(get_script_dir());native=root/'native-scripts';native.mkdir()
for name in ['openroad/common/io.tcl','openroad/common/dpl_cell_pad.tcl','openroad/common/grt.tcl','openroad/common/set_routing_layers.tcl','openroad/common/set_layer_adjustments.tcl','openroad/gpl.tcl']:
 if (scripts/name).exists():
  target=native/name;target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(scripts/name,target)
env=dict(os.environ,SCRIPTS_DIR=str(scripts),_TCL_ENV_IN='/work/diagnostic/corner-env.tcl')
with (root/'native.log').open('w') as log:
 result=subprocess.run(['openroad','-exit','-threads','4','-no_splash','-metrics','/work/diagnostic/metrics.json','/work/diagnostic/route.tcl'],env=env,cwd=str(root),stdout=log,stderr=subprocess.STDOUT)
assert result.returncode==0,result.returncode
subprocess.run(['openroad','-python','-exit','/work/diagnostic/export_geometry.py'],env=env,cwd=str(root),check=True)

import re
geometry=json.loads((root/'geometry.json').read_text())
assert geometry['grid_edge_policy']['all_saved_units_preserved']
assert set(geometry['macros'])=={'engine.memory.storage0','engine.memory.storage1'}
for name,expected in {'engine.memory.storage0':[252000,30000,1036480,94360],
                      'engine.memory.storage1':[252000,144000,1036480,208360]}.items():
 assert geometry['macros'][name]['orientation']=='R0'
 assert geometry['macros'][name]['bbox_dbu']==expected
log=(root/'native.log').read_text()
pattern=r'^(Metal[234]|Total)\s+(\d+)\s+(\d+)\s+([\d.]+)%\s+(\d+)\s*/\s*(\d+)\s*/\s*(\d+)\s*$'
rows=re.findall(pattern,log,re.M)
assert rows, 'Native congestion table missing'
layers={}
for name,resource,demand,usage,h,v,total in rows:
 layers[name]={'resource':int(resource),'demand':int(demand),'usage_percent':float(usage),'max_horizontal_overflow':int(h),'max_vertical_overflow':int(v),'overflow':int(total)}
assert set(layers)=={'Metal2','Metal3','Metal4','Total'}
assert layers['Total']['overflow']==sum(layers[n]['overflow'] for n in ('Metal2','Metal3','Metal4'))
marker_path=root/'congestion.json'
if layers['Total']['overflow']==0 and not marker_path.exists():marker_path.write_text('')
markers=marker_path.read_text()
marker_total=sum(map(int,re.findall(r'overflow:(\d+)',markers)))
assert marker_total==layers['Total']['overflow'],(marker_total,layers)
segments=root/'after_grt.segments';assert segments.is_file() and segments.stat().st_size>0
audit=json.loads((root/'routing-inventory.json').read_text());assert audit['all_frozen_native_invariants_passed']
measurement={'status':'measured','native_iterations_per_segment':iterations,'native_frozen_inventory':audit,'route_segments':{'path':'after_grt.segments','sha256':hashlib.sha256(segments.read_bytes()).hexdigest(),'bytes':segments.stat().st_size},'native_layers':layers,'native_overflow':layers['Total']['overflow'],
 'saved_preferred_grid_overflow':sum(x['overflow'] for x in geometry['layers'].values()),
 'spatial_assigned_overflow':sum(x['spatial_assigned_overflow'] for x in geometry['layers'].values()),
 'unassigned_edge_overflow':sum(x['unassigned_edge_overflow'] for x in geometry['layers'].values()),
 'wirelength_um':int(re.findall(r'Total wirelength: (\d+) um',log)[-1]),
 'routed_nets':int(re.findall(r'Routed nets: (\d+)',log)[-1]),
 'fresh_native_metrics':json.loads((root/'metrics.json').read_text()),
 'macros':geometry['macros'],'inventory_unchanged':geometry['inventory_unchanged'],
 'exported_netlist_unchanged':geometry['exported_netlist_unchanged'],
 'native_clock_ndr_fallback_retries':log.count('[WARNING GRT-0273]'),
 'native_clock_ndr_fallback_net_order':re.findall(r'Disabled NDR \(to reduce congestion\) for net: (\S+)',log),'boundary':f'One native{iterations}-iteration-per-segment effort diagnostic from exact original95f0. Native automatic clock-NDR fallback retained. All instances/PG/pins/rows/TechLEF/rule definitions/topology unchanged; only native CLOCK NDR association changes permitted and recorded. Saved grid and directional native totals are distinct. Segments allow separate global-route parasitic timing; no accepted routing, extraction or signoff.'}
(root/'measurement.json').write_text(json.dumps(measurement,indent=2)+'\n')
