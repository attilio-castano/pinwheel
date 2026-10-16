"""Host parser of actual native pin-access/DRT evidence, including failed runs."""
import argparse,collections,hashlib,json,re,math
from pathlib import Path
N=r'[-+]?(?:\d+(?:\.\d*)?|\.\d+)(?:[eE][-+]?\d+)?'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def overlaps(a,b):return a[0]<b[2] and a[2]>b[0] and a[1]<b[3] and a[3]>b[1]
def native_counts(text):
 patterns={'violations':r'(?i)(?:number of|#)\s*(?:DRC\s*)?violations\s*[:=]\s*(\d+)', 'unrouted':r'(?i)(?:number of|#|total)\s*unrouted(?:\s+(?:nets|connections))?\s*[:=]\s*(\d+)', 'pin_access_failures':r'(?i)(?:number of|#|total)\s*(?:pins?\s+with\s+no\s+access|pin\s*access\s*failures?)\s*[:=]\s*(\d+)'}
 out={}
 for k,p in patterns.items():
  obs=[{'line':text[:m.start()].count('\n')+1,'value':int(m[1]),'text':text.splitlines()[text[:m.start()].count('\n')]} for m in re.finditer(p,text)]
  out[k]={'availability':'observed' if obs else 'unavailable','observations':obs,'last_observation':obs[-1]['value'] if obs else None,'last_observation_not_necessarily_final_run_total':True}
 return out

def drc_markers(text,scale):
 out=[]
 for b in re.split(r'(?im)^\s*violation\s+type\s*:\s*',text)[1:]:
  typ=b.splitlines()[0].strip();sources=re.search(r'(?im)^\s*srcs\s*:\s*(.+)$',b);srcs=sources[1].split() if sources else []
  box=re.search(r'bbox\s*=\s*\(\s*('+N+r')\s*[, ]\s*('+N+r')\s*\)\s*-\s*\(\s*('+N+r')\s*[, ]\s*('+N+r')\s*\)\s*on\s+layer\s+(\S+)',b,re.I)
  coords=[float(box[i]) for i in [1,2,3,4]] if box else None
  out.append({'type':typ,'source_tokens':srcs,'reported_bbox':coords,'bbox_dbu':[round(x*scale) for x in coords] if coords and scale is not None else None,'layer':box[5] if box else None,'raw_record':b.strip(),'spatial_parse_complete':box is not None and scale is not None})
 return out

def net_roles(inv,token):
 names=[token]
 # Keep unmatched tokens intact; do notguess netaliases or reconstruct names.
 if token in inv['nets']:
  n=inv['nets'][token];roles={n['sig_type']};pins=[]
  for inst,p,d in n['terminals']:
   if inst in inv['macros']:
    pins.append(inst+'/'+p)
    if p.startswith('A_DIN['):roles.add('SRAM_write_data')
    elif p.startswith('A_DOUT['):roles.add('SRAM_read_data')
    elif p.startswith('A_ADDR['):roles.add('SRAM_address')
    elif p in ['A_WEN','A_REN','A_MEN']:roles.add('SRAM_control')
    elif p=='A_CLK':roles.add('SRAM_clock')
  return {'matched_net':token,'roles':sorted(roles),'macro_pins':pins}
 return {'matched_net':None,'unmatched_source_token':token,'roles':[],'macro_pins':[]}

def box_index(records,step):
 buckets={};large={}
 for i,x in enumerate(records):
  if not isinstance(x,dict) or not x.get('bbox_dbu') or not x.get('layer'):continue
  a=x['bbox_dbu'];xs=range(math.floor(a[0]/step),math.floor(a[2]/step)+1);ys=range(math.floor(a[1]/step),math.floor(a[3]/step)+1)
  if len(xs)*len(ys)>4096:large.setdefault(x['layer'],[]).append(i);continue
  for xx in xs:
   for yy in ys:buckets.setdefault((x['layer'],xx,yy),[]).append(i)
 return buckets,large
def query_boxes(box,layer,records,index,step):
 buckets,large=index;ids=set(large.get(layer,[]))
 for xx in range(math.floor(box[0]/step),math.floor(box[2]/step)+1):
  for yy in range(math.floor(box[1]/step),math.floor(box[3]/step)+1):ids.update(buckets.get((layer,xx,yy),[]))
 return [records[i] for i in sorted(ids) if overlaps(box,records[i]['bbox_dbu'])]

def main():
 p=argparse.ArgumentParser();p.add_argument('--native-log',type=Path,required=True);p.add_argument('--drc-report',type=Path,action='append',default=[]);p.add_argument('--inventory',type=Path,required=True);p.add_argument('--geometry',type=Path,required=True);p.add_argument('--drc-units',choices=['um','dbu','unknown'],default='unknown');p.add_argument('--producer-report',type=Path);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
 inv=json.loads(a.inventory.read_text());geo=json.loads(a.geometry.read_text());assert geo['dbu_per_micron']==inv['dbu_per_micron'];scale={'um':inv['dbu_per_micron'],'dbu':1,'unknown':None}[a.drc_units];text=a.native_log.read_text();inputs={str(a.native_log.resolve()):sha(a.native_log),str(a.inventory.resolve()):sha(a.inventory),str(a.geometry.resolve()):sha(a.geometry)}
 reports=[];roles=collections.Counter();layers=collections.Counter();kinds=collections.Counter();all_markers=[]
 obs=geo.get('macro_obstructions',[]);pbs=geo.get('power_boxes',[]);assert isinstance(obs,list) and isinstance(pbs,list);step=24000;oi=box_index(obs,step);pi=box_index(pbs,step)
 for file in a.drc_report:
  if not file.exists():reports.append({'path':str(file),'availability':'missing','marker_count':None});continue
  inputs[str(file.resolve())]=sha(file);raw=file.read_text();ms=drc_markers(raw,scale)
  for m in ms:
   m['report_path']=str(file);m['source_net_roles']=[net_roles(inv,n) for n in m['source_tokens']];m['macro_footprint_overlaps']=[];m['macro_obstruction_overlaps']=[];m['power_box_overlap_count']=None
   if m['bbox_dbu']:
    m['macro_footprint_overlaps']=[n for n,v in geo['macros'].items() if overlaps(m['bbox_dbu'],v['bbox_dbu'])]
    m['macro_obstruction_overlaps']=query_boxes(m['bbox_dbu'],m['layer'],obs,oi,step)
    m['power_box_overlap_count']=len(query_boxes(m['bbox_dbu'],m['layer'],pbs,pi,step))
   kinds[m['type']]+=1;layers[m['layer'] or 'unparsed']+=1
   for r in m['source_net_roles']:
    for role in r['roles']:roles[role]+=1
  reports.append({'path':str(file),'availability':'present','bytes':file.stat().st_size,'marker_count':len(ms),'parser_recognized_native_violation_records':bool(ms),'empty_report_not_a_complete_route_or_zero_DRC_claim':not bool(ms) });all_markers.extend(ms)
 lines=text.splitlines();pin_lines=[{'line':i+1,'text':l} for i,l in enumerate(lines) if re.search(r'(?i)(?:no|missing|failed|cannot|unable).*(?:access point|pin access)|(?:pin|terminal).*(?:no access|unreachable)',l)];error_lines=[{'line':i+1,'text':l} for i,l in enumerate(lines) if re.search(r'\[(?:ERROR|WARNING) DRT-\d+\]',l)]
 producer=None
 if a.producer_report:
  inputs[str(a.producer_report.resolve())]=sha(a.producer_report);r=json.loads(a.producer_report.read_text());producer={k:r.get(k) for k in ['schema','status','exit_code','inputs_unchanged','container_termination']}
 counts=native_counts(text);unroute_lines=[{'line':i+1,'text':l} for i,l in enumerate(lines) if re.search(r'(?i)unrout(?:ed|able)|failed\s+to\s+route',l)]
 result={'schema':'pinwheel-native-drt-pinaccess-diagnostic-v1','status':'diagnosed','input_sha256':inputs,'producer_state_observed':producer,'reported_coordinate_units':a.drc_units,'observed_native_count_ledger':counts,'pin_access_failure_lines':pin_lines,'unrouted_failure_lines':unroute_lines,'native_DRT_error_warning_lines':error_lines,'drc_reports':reports,'native_DRC_markers':all_markers,'aggregate_marker_observation_count_across_requested_reports':len(all_markers),'aggregate_counts_are_not_a_final_unique_DRC_count':True,'spatial_index_cell_dbu':step,'DRC_type_counts':dict(kinds),'DRC_layer_counts':dict(layers),'source_role_marker_incidences':dict(roles),'actual_native_DRC_failure_observed':bool(all_markers) or any(v['last_observation'] is not None and v['last_observation']>0 for k,v in counts.items() if k=='violations'),'official_precheck_pass_claim':False,'full_foundry_DRC_pass_claim':False,'extracted_timing_claim':False,'completed_legal_route_claim':False,'boundary':'Onlyactualnative DRT/pin-access reports and raw log observations. Missingcounts remainnull; global-routeoverflow never becomesDRC. Marker overlap/incidencesdo notallocatecausalresponsibility. Failed/partialnativeoutputs retained; no GDS/precheck/signoff inference.'}
 assert not a.output.exists();a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(result,indent=2)+'\n');print(a.output,len(all_markers))
if __name__=='__main__':main()
