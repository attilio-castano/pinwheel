"""Fresh both-net connectivity plus source-bound native macro/contact readback."""
import json
from pathlib import Path
import subprocess
ROOT=Path('/work/diagnostic')
with (ROOT/'native.log').open('w') as log:
    result=subprocess.run(['openroad','-exit','/work/diagnostic/check_grid.tcl'],cwd=str(ROOT),stdout=log,stderr=subprocess.STDOUT)
assert result.returncode==0,result.returncode
native=(ROOT/'native.log').read_text()
results={net:{'all_shapes_connected':f'All shapes on net {net} are connected.' in native} for net in ('VPWR','VGND')}
assert all(v['all_shapes_connected'] for v in results.values()),results
with (ROOT/'metadata.log').open('w') as log:
    result=subprocess.run(['openroad','-python','-exit','/work/diagnostic/metadata.py'],cwd=str(ROOT),stdout=log,stderr=subprocess.STDOUT)
assert result.returncode==0,result.returncode
metadata=json.loads((ROOT/'metadata.json').read_text());assert metadata['status']=='measured'
measurement={'status':'measured','net_results':results,'native_metadata':metadata,
             'boundary':'Fresh native whole-grid both-net connectivity and exact candidate MX geometry/contact readback. No cell/netlist/grid mutation, DRC, IR drop or routed signoff.'}
(ROOT/'measurement.json').write_text(json.dumps(measurement,indent=2)+'\n')
