import os,subprocess,shutil,json,hashlib
from pathlib import Path
from librelane.common import get_script_dir
root=Path('/work/diagnostic');scripts=Path(get_script_dir());native=root/'native-scripts';native.mkdir()
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
log=(root/'native.log').read_text()
pattern=r'^(Metal[234]|Total)\s+(\d+)\s+(\d+)\s+([\d.]+)%\s+(\d+)\s*/\s*(\d+)\s*/\s*(\d+)\s*$'
rows=re.findall(pattern,log,re.M)
assert rows, 'Native congestion table missing'
layers={}
for name,resource,demand,usage,h,v,total in rows:
 layers[name]={'resource':int(resource),'demand':int(demand),'usage_percent':float(usage),'max_horizontal_overflow':int(h),'max_vertical_overflow':int(v),'overflow':int(total)}
assert set(layers)=={'Metal2','Metal3','Metal4','Total'}
assert layers['Total']['overflow']==sum(layers[n]['overflow'] for n in ('Metal2','Metal3','Metal4'))
markers=(root/'congestion.json').read_text()
marker_total=sum(map(int,re.findall(r'overflow:(\d+)',markers)))
assert marker_total==layers['Total']['overflow'],(marker_total,layers)
measurement={'status':'measured','native_layers':layers,'native_overflow':layers['Total']['overflow'],
 'saved_preferred_grid_overflow':sum(x['overflow'] for x in geometry['layers'].values()),
 'wirelength_um':int(re.findall(r'Total wirelength: (\d+) um',log)[-1]),
 'routed_nets':int(re.findall(r'Routed nets: (\d+)',log)[-1]),
 'fresh_native_metrics':json.loads((root/'metrics.json').read_text()),
 'macros':geometry['macros'],'inventory_unchanged':geometry['inventory_unchanged'],
 'exported_netlist_unchanged':geometry['exported_netlist_unchanged'],
 'native_clock_ndr_fallback_retries':log.count('[WARNING GRT-0273]'),
 'boundary':'One native5-iteration-per-segment coarse congestion-allowed diagnostic; not equivalent to full50-iteration benchmark. Native automatic clock-NDR fallback retained; no cell mutation, accepted route or signoff claim. Unchanged inventory covers masters/positions/orientations/logical terminals, not routing-rule state. Saved grid and directional native totals are independent representations.'}
(root/'measurement.json').write_text(json.dumps(measurement,indent=2)+'\n')
