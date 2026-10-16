"""Host source-Liberty conservative setup loss bound; does not run CAD."""
import argparse,hashlib,json,re
from pathlib import Path
ROOT=Path('/work/diagnostic')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def group(text,kind,name):
 m=re.search(r'\b'+re.escape(kind)+r'\s*\(\s*"?'+re.escape(name)+r'"?\s*\)\s*\{',text);assert m,(kind,name)
 start=m.end();depth=1;quote=False
 for i in range(start,len(text)):
  c=text[i]
  if c=='"' and text[i-1]!='\\':quote=not quote
  if not quote:
   if c=='{':depth+=1
   if c=='}':
    depth-=1
    if not depth:return text[start:i]
 raise AssertionError('Unclosed Liberty group')
def pin_caps(lib,cell,pin):
 b=group(group(lib,'cell',cell),'pin',pin);vals=[]
 for k in ['capacitance','rise_capacitance','fall_capacitance']:
  m=re.search(r'\b'+k+r'\s*:\s*([.0-9eE+-]+)\s*;',b)
  if m:vals.append(float(m[1]))
 assert vals;return min(vals),max(vals)
def tables(lib,cell,kind):
 b=group(lib,'cell',cell);out=[]
 for m in re.finditer(r'\b'+kind+r'\s*\([^)]*\)\s*\{',b):
  sub=b[m.end():];end=sub.index('}');x=sub[:end]
  axes=[list(map(float,re.findall(r'[-+]?\d*\.\d+(?:[eE][-+]?\d+)?',re.search(r'index_'+str(n)+r'\s*\(\s*"([^"]+)"',x)[1]))) for n in [1,2]]
  values=re.search(r'values\s*\((.*?)\);',x,re.S)[1];rows=[list(map(float,r.split(','))) for r in re.findall(r'"([^"]+)"',values)];assert len(rows)==len(axes[0]) and all(len(r)==len(axes[1]) for r in rows);out.append((axes,rows))
 assert out;return out
def upper_over_cap(ts,cap):
 vals=[]
 for axes,rows in ts:
  a=axes[1];assert a[0]<=cap<=a[-1],('Cap bound outside axes',cap,a)
  i=next(i for i in range(len(a)-1) if a[i]<=cap<=a[i+1]);w=(cap-a[i])/(a[i+1]-a[i]);vals.extend(r[i]*(1-w)+r[i+1]*w for r in rows)
 return max(vals)
def constraint_spread(lib):
 b=group(group(lib,'cell','sg13cmos5l_dfrbpq_1'),'pin','D');vals=[]
 for x in re.split(r'\btiming\s*\(\s*\)',b)[1:]:
  if re.search(r'timing_type\s*:\s*setup_rising',x):
   for v in re.findall(r'values\s*\((.*?)\);',x,re.S):vals.extend(map(float,re.findall(r'[-+]?\d*\.\d+(?:[eE][-+]?\d+)?',v)))
 assert vals;return max(vals)-min(vals)
def parse_rows(text):
 out=[]
 for l in text.split('data arrival time')[0].splitlines():
  m=re.search(r'([\^v])\s+(\S+)\s+\(([^)]+)\)',l)
  if not m:continue
  vals=l[:m.start()].split()
  if len(vals) not in [3,5]:continue
  out.append(dict(pin=m[2],master=m[3],edge='rise' if m[1]=='^' else 'fall',cap=float(vals[-4]) if len(vals)==5 else None,slew=float(vals[-3]),delay=float(vals[-2])))
 return out

def assess(root,results):
 out={}
 for corner,candidate in results['candidate'].items():
  p=root/'candidate'/'lib';files=list(p.glob('*stdcell*'+corner.removeprefix('nom_')+'.lib'));assert len(files)==1;lib=files[0].read_text();bc=pin_caps(lib,'sg13cmos5l_buf_1','A');fc=pin_caps(lib,'sg13cmos5l_dfrbpq_1','D');rows={}
  for ep,h in candidate['terminal_headroom'].items():
   checks=[]
   for context,c in h['contexts'].items():
    baseline=results['control'][corner]['terminal_headroom'][ep]['contexts'][context];B=parse_rows((root/'control'/corner/baseline['report']).read_text());C=parse_rows((root/'candidate'/corner/c['report']).read_text());name='timing_eco_terminal_'+ep.split('/')[0].strip('_');bufA=next(r for r in C if r['pin']==name+'/A');bufX=next(r for r in C if r['pin']==name+'/X');ffD=C[-1];old=C[C.index(bufA)-1];oldB=B[-2];assert old['pin']==oldB['pin'] and ffD['pin']==ep
    low=.0186;high=2.5074
    clock_rows=[r for r in re.findall(r'([0-9.]+)\s+[-+0-9.]+\s+[-+0-9.]+\s+[\^v] '+re.escape(ep.split('/')[0])+r'/CLK', (root/'candidate'/corner/c['report']).read_text())];assert len(clock_rows)==1;clkSlew=float(clock_rows[0])
    domain=low<=bufA['slew']<=high and low<=ffD['slew']<=high and low<=clkSlew<=high and .001<=bufX['cap']<=.3
    loading=old['cap']<=oldB['cap']+bc[1]-fc[0]+.010+1e-6 and bufX['cap']<=fc[1]+.010+1e-6
    wire=bufA['delay']<=B[-1]['delay']+.100+1e-6 and ffD['delay']<=.100+1e-6
    checks.append(dict(context=context,BUF_A_input_slew_ns=bufA['slew'],FF_D_slew_ns=ffD['slew'],FF_CLK_slew_ns=clkSlew,BUF_total_output_cap_pF=bufX['cap'],old_driver_total_cap_pF=old['cap'],control_old_driver_total_cap_pF=oldB['cap'],new_to_D_wire_delay_ns=ffD['delay'],old_to_BUF_A_wire_delay_ns=bufA['delay'],observed_new_branch_source_domains_met=domain,planned_load_bounds_met=loading,planned_two_net_wire_delay_bounds_met=wire))
   rows[ep]=dict(contexts=checks,all_new_branch_domain_checks_passed=all(r['observed_new_branch_source_domains_met'] for r in checks),all_planned_RC_cost_bounds_passed=all(r['planned_load_bounds_met'] and r['planned_two_net_wire_delay_bounds_met'] for r in checks))
  out[corner]=rows
 return dict(corners=out,all_new_branch_source_domains_met=all(r['all_new_branch_domain_checks_passed'] for c in out.values() for r in c.values()),all_planned_RC_cost_bounds_met=all(r['all_planned_RC_cost_bounds_passed'] for c in out.values() for r in c.values()),scope='Explicitobservedcandidate newBUFinput/FF_D+CLKconstraintdomains andconservativeSTAload/netdelaybounds; qualificationreportedseparatelyfromunconditionalnumericSTA.')
