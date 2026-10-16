"""Host source-Liberty conservative setup loss bound; does not run CAD."""
import argparse,hashlib,json,re
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
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
def main():
 p=argparse.ArgumentParser();p.add_argument('--report',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args();r=json.loads(a.report.read_text());assert r['status']=='passed' and r['exit_code']==0 and r['inputs_unchanged'] and r['measurement']['no_edit_control_passed'];out=a.report.parent;results={};sources={str(a.report.resolve()):sha(a.report)}
 for c,v in r['measurement']['corners'].items():
  files=list((out/'headroom/lib').glob('*stdcell*'+c.removeprefix('nom_')+'.lib'));assert len(files)==1;f=files[0];lib=f.read_text();sources[str(f.resolve())]=sha(f);bufcaps=pin_caps(lib,'sg13cmos5l_buf_1','A');ffcaps=pin_caps(lib,'sg13cmos5l_dfrbpq_1','D');setupspread=constraint_spread(lib);rows={}
  for ep,h in v['terminal_headroom'].items():
   per=[]
   for key,ctx in h['contexts'].items():
    if not key.endswith('/max'):continue
    f=out/'headroom'/c/ctx['report'];sources[str(f.resolve())]=sha(f);pr=parse_rows(f.read_text());driver=pr[-2];assert driver['cap'] is not None and pr[-1]['pin']==ep
    capbound=driver['cap']+bufcaps[1]-ffcaps[0]+.010;newbufcapbound=ffcaps[1]+.010
    oldmax=max(upper_over_cap(tables(lib,driver['master'],kind),capbound) for kind in ['cell_rise','cell_fall']);bufmax=max(upper_over_cap(tables(lib,'sg13cmos5l_buf_1',kind),newbufcapbound) for kind in ['cell_rise','cell_fall'])
    added=max(0,oldmax-driver['delay'])+bufmax+setupspread+.200
    per.append(dict(context=key,driver=driver,old_driver_load_bound_pF=capbound,new_buffer_load_bound_pF=newbufcapbound,old_driver_delay_full_slew_axis_max_ns=oldmax,buffer_delay_full_slew_axis_max_ns=bufmax,FF_setup_constraint_full_axis_spread_ns=setupspread,two_net_added_delay_allowance_ns=.200,maximum_added_setup_loss_bound_ns=added,raw_setup_ns=ctx['slack_ns'],conservative_setup_after_cost_and_1ps_ns=ctx['slack_ns']-added-.001))
   rows[ep]=dict(contexts=per,safe_setup_headroom=all(q['conservative_setup_after_cost_and_1ps_ns']>=.5 for q in per))
  results[c]=rows
 result=dict(schema='pinwheel-five-terminal-pre-edit-setup-cost-v1',status='assessed',all_corner_endpoint_setup_safe=all(v['safe_setup_headroom'] for c in results.values() for v in c.values()),corners=results,input_sha256=sources,policy=dict(each_old_net_added_wire_capacitance_at_most_pF=.010,each_new_net_wire_capacitance_at_most_pF=.010,each_touched_signal_net_additional_delay_at_most_ns=.100,all_observed_buffer_and_old_driver_input_slews_must_be_within_source_axes=True,new_FF_D_and_clock_constraint_slews_must_be_within_source_axes=True,postroute_enforcement_required=True,hold_gain_not_guaranteed_by_this_setup_bound=True),scope='Conservative source-Liberty setupcost only, fullcharacterized input axes and all olddriverarcs plus FFsetupconstraintspread. Not prospective pinRClayout orholdpass claim; actualnewroute cap/delay/domain mustsatisfypolicy beforeclosing physicalcandidate.')
 assert not a.output.exists();a.output.write_text(json.dumps(result,indent=2)+'\n');print(a.output,result['all_corner_endpoint_setup_safe'])
if __name__=='__main__':main()
