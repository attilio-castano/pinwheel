"""Source-derived host qualification for observed five-terminal STA/RC. No CAD."""
import argparse,hashlib,json,re
from pathlib import Path
NUM=r'[-+]?(?:\d+(?:\.\d*)?|\.\d+)(?:[eE][-+]?\d+)?'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def body(text,start):
 depth=1;quote=False
 for i in range(start,len(text)):
  c=text[i]
  if c=='"' and (i==0 or text[i-1]!='\\'):quote=not quote
  if not quote:
   if c=='{':depth+=1
   elif c=='}':
    depth-=1
    if not depth:return text[start:i]
 raise AssertionError('Unclosed Liberty body')
def groups(text,kind):
 return [(m[1].strip().strip('"'),body(text,m.end())) for m in re.finditer(r'\b'+re.escape(kind)+r'\s*\(([^)]*)\)\s*\{',text)]
def group(text,kind,name):
 v=[b for n,b in groups(text,kind) if n==name];assert len(v)==1,(kind,name,len(v));return v[0]
def attr(text,key):
 m=re.search(r'\b'+key+r'\s*:\s*"?([^;"\n]+)"?\s*;',text);assert m,key;return m[1].strip()
def pin(lib,cell,name):return group(group(lib,'cell',cell),'pin',name)
def caps(lib,cell,name):
 p=pin(lib,cell,name);vals=[]
 for key in ['capacitance','rise_capacitance','fall_capacitance']:
  m=re.search(r'\b'+key+r'\s*:\s*('+NUM+r')\s*;',p)
  if m:vals.append(float(m[1]))
 assert vals;return min(vals),max(vals)
def axes(lib,table):
 template,t=table;tb=group(lib,'lu_table_template',template);result={}
 for index in [1,2]:
  m=re.search(r'index_'+str(index)+r'\s*\(\s*"([^"]+)"\s*\)',t);assert m,template
  nums=list(map(float,re.findall(NUM,m[1])));assert len(nums)>1 and nums==sorted(nums)
  result[attr(tb,'variable_'+str(index))]=[nums[0],nums[-1]]
 return result

def within(value,bounds):return value is not None and bounds[0]-1e-9<=value<=bounds[1]+1e-9

def output_domains(lib,master,output,input_pin,input_slew,cap,output_edge):
 out=[]
 for _,arc in groups(pin(lib,master,output),'timing'):
  if attr(arc,'related_pin')!=input_pin:continue
  for table in groups(arc,'cell_'+output_edge):
   ax=axes(lib,table);ib=ax.get('input_net_transition',ax.get('input_transition_time'));cb=ax.get('total_output_net_capacitance');assert ib is not None and cb is not None
   out.append({'input_pin':input_pin,'input_slew_ns':input_slew,'input_slew_axis_ns':ib,'reported_total_cap_pF':cap,'output_cap_axis_pF':cb,'observed_input_slew_and_total_cap_inside_axes':within(input_slew,ib) and within(cap,cb)})
 assert out,(master,output,input_pin,output_edge);return out

def ff_domains(lib,master,data_slew,clock_slew,data_edge,kind):
 out=[];tt='setup_rising' if kind=='max' else 'hold_rising'
 for _,arc in groups(pin(lib,master,'D'),'timing'):
  if attr(arc,'timing_type')!=tt:continue
  for table in groups(arc,data_edge+'_constraint'):
   ax=axes(lib,table);d=ax['constrained_pin_transition'];c=ax['related_pin_transition'];out.append({'timing_type':tt,'data_slew_ns':data_slew,'data_slew_axis_ns':d,'clock_slew_ns':clock_slew,'clock_slew_axis_ns':c,'observed_D_and_CLK_slews_inside_axes':within(data_slew,d) and within(clock_slew,c)})
 assert out;return out

def parse_rows(text):
 out=[]
 for line in text.splitlines():
  m=re.search(r'([\^v])\s+(\S+)\s+\(([^)]+)\)',line)
  if not m:continue
  vals=line[:m.start()].split()
  if len(vals) not in [3,5]:continue
  out.append({'pin':m[2],'master':m[3],'edge':'rise' if m[1]=='^' else 'fall','cap':float(vals[-4]) if len(vals)==5 else None,'slew':float(vals[-3]),'delay':float(vals[-2])})
 return out

def wire_caps(path):
 text=path.read_text();assert '"PIN_CAP NONE"' in text and re.search(r'^\*C_UNIT\s+1\s+PF\s*$',text,re.M),'Native wire-only pF SPEF required'
 names={m[1]:m[2] for m in re.finditer(r'^(\*\d+)\s+(\S+)\s*$',text,re.M)};out={}
 for m in re.finditer(r'^\*D_NET\s+(\S+)\s+('+NUM+r')\s*$',text,re.M):
  n=names.get(m[1],m[1]);assert n not in out;out[n]=float(m[2])
 assert out;return out

def assess(root,results):
 root=Path(root);out={};sources={};endpoints={'_30759_/D':'net8042','_30606_/D':'net8046','_30747_/D':'net9291','_30602_/D':'_00006_','_34083_/D':'_03109_'}
 for corner,candidate in results['candidate'].items():
  files=list((root/'candidate/lib').glob('*stdcell*'+corner.removeprefix('nom_')+'.lib'));assert len(files)==1;libfile=files[0];lib=libfile.read_text();sources[str(libfile)]=sha(libfile);bc=caps(lib,'sg13cmos5l_buf_1','A');fc=caps(lib,'sg13cmos5l_dfrbpq_1','D')
  cp=root/'control'/corner/'estimated.spef';pp=root/'candidate'/corner/'estimated.spef';before_wire=wire_caps(cp);after_wire=wire_caps(pp);sources[str(cp)]=sha(cp);sources[str(pp)]=sha(pp);records={}
  assert set(candidate['terminal_headroom'])==set(endpoints)
  for ep,h in candidate['terminal_headroom'].items():
   inst=ep.split('/')[0];name='timing_eco_terminal_'+inst.strip('_');new=name+'_D';oldnet=endpoints[ep];checks=[]
   assert set(h['contexts'])=={'rise/max','fall/max','rise/min','fall/min'}
   capcheck={'old_net':oldnet,'new_net':new,'old_wire_cap_control_pF':before_wire[oldnet],'old_wire_cap_candidate_pF':after_wire[oldnet],'old_net_added_wire_cap_pF':after_wire[oldnet]-before_wire[oldnet],'new_net_wire_cap_pF':after_wire[new],'each_touched_net_wire_cap_budget_pF':.010,'native_wire_cap_budget_met':after_wire[oldnet]<=before_wire[oldnet]+.010+1e-9 and after_wire[new]<=.010+1e-9}
   for context,case in h['contexts'].items():
    control=results['control'][corner]['terminal_headroom'][ep]['contexts'][context];bp=root/'control'/corner/control['report'];ap=root/'candidate'/corner/case['report'];sources[str(bp)]=sha(bp);sources[str(ap)]=sha(ap);B=parse_rows(bp.read_text().split('data arrival time')[0]);C=parse_rows(ap.read_text().split('data arrival time')[0]);allC=parse_rows(ap.read_text());aidx=next(i for i,r in enumerate(C) if r['pin']==name+'/A');bufA=C[aidx];bufX=C[aidx+1];old=C[aidx-1];oldinput=C[aidx-2];oldB=B[-2];ffD=C[-1];assert bufX['pin']==name+'/X' and ffD['pin']==ep and old['pin']==oldB['pin'] and old['master']==oldinput['master']
    clk=[r for r in allC if r['pin']==inst+'/CLK'];assert clk;clock=clk[-1]
    oldinst,oldout=old['pin'].rsplit('/',1);assert oldinput['pin'].rsplit('/',1)[0]==oldinst
    oldchecks=output_domains(lib,old['master'],oldout,oldinput['pin'].rsplit('/',1)[1],oldinput['slew'],old['cap'],old['edge']);bufchecks=output_domains(lib,'sg13cmos5l_buf_1','X','A',bufA['slew'],bufX['cap'],bufX['edge']);ffchecks=ff_domains(lib,ffD['master'],ffD['slew'],clock['slew'],ffD['edge'],context.split('/')[1])
    domain=all(r['observed_input_slew_and_total_cap_inside_axes'] for r in oldchecks+bufchecks) and all(r['observed_D_and_CLK_slews_inside_axes'] for r in ffchecks)
    loading=old['cap']<=oldB['cap']+bc[1]-fc[0]+.010+1e-6 and bufX['cap']<=fc[1]+.010+1e-6
    delays=bufA['delay']<=B[-1]['delay']+.100+1e-6 and ffD['delay']<=.100+1e-6
    checks.append({'context':context,'old_driver_observed_arc_domains':oldchecks,'new_BUF1_observed_arc_domains':bufchecks,'FF_D_CLK_constraint_domains':ffchecks,'old_to_BUF_A_wire_delay_ns':bufA['delay'],'control_old_to_D_wire_delay_ns':B[-1]['delay'],'new_to_D_wire_delay_ns':ffD['delay'],'old_driver_total_cap_pF':old['cap'],'control_old_driver_total_cap_pF':oldB['cap'],'new_BUF1_total_cap_pF':bufX['cap'],'planned_total_load_bounds_met':loading,'planned_two_net_delay_budgets_met':delays,'all_observed_source_table_domains_met':domain})
   records[ep]={'native_wire_cap_budget':capcheck,'contexts':checks,'all_contexts_source_domain_met':all(r['all_observed_source_table_domains_met'] for r in checks),'all_planned_RC_cost_bounds_met':capcheck['native_wire_cap_budget_met'] and all(r['planned_total_load_bounds_met'] and r['planned_two_net_delay_budgets_met'] for r in checks)}
  out[corner]=records
 return {'schema':'pinwheel-five-terminal-postroute-source-policy-v1','status':'assessed','corners':out,'all_observed_source_domains_met':all(v['all_contexts_source_domain_met'] for c in out.values() for v in c.values()),'all_planned_RC_cost_bounds_met':all(v['all_planned_RC_cost_bounds_met'] for c in out.values() for v in c.values()),'input_sha256':sources,'scope':'Fresh observed old-driver related-input/newBUF1 and FF-D/CLK constraint-domain checks plus native PIN_CAP-NONE SPEF wire C and reported total load/net-delay budgets. Numerical STA remains measured when domains fail. Reported totalcap axis checks do not certify internal effective capacitance.'}

def main():
 p=argparse.ArgumentParser();p.add_argument('--report',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args();r=json.loads(a.report.read_text());assert r['status']=='passed' and r['exit_code']==0 and r['inputs_unchanged'];result=assess(a.report.parent,r['measurement']['results']);assert not a.output.exists();a.output.write_text(json.dumps(result,indent=2)+'\n');print(a.output,result['all_planned_RC_cost_bounds_met'],result['all_observed_source_domains_met'])
if __name__=='__main__':main()
