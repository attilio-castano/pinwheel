"""Independent host readback after settled no-ECO DRT probe; never runs CAD."""
import argparse,hashlib,json,re
from pathlib import Path
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_text())
def lef(path):
 text=path.read_text();pat=r'(?ms)^VIA\s+(\S+).*?^END\s+\1\s*$';blocks={m[1]:m[0] for m in re.finditer(pat,text)};assert len(blocks)==len(re.findall(r'^VIA\s',text,re.M))
 return [line for line in re.sub(pat,'',text).splitlines() if line.strip()],blocks

def detailed_layers(path,inventory):
 text=path.read_text();m=re.search(r'(?ms)^NETS\s+\d+\s*;\s*(.*?)^END NETS\s*$',text);assert m,'Detailed DEF NETS section absent';out={};invalid=[]
 for entry in re.split(r'(?m)^-\s+',m[1]):
  if not entry.strip():continue
  name=entry.split()[0];assert name in inventory['nets'],('Unknown DEF net',name)
  layers=re.findall(r'\+\s+(?:ROUTED|FIXED|COVER)\s+(\S+)|\bNEW\s+(Metal\d+|TopMetal\d+)',entry)
  names=sorted({a or b for a,b in layers})
  if names:out[name]=names
  if inventory['nets'][name]['sig_type'] in ['SIGNAL','CLOCK']:
   for layer in names:
    if layer not in ['Metal1','Metal2','Metal3','Metal4']:invalid.append([name,layer])
 return out,invalid

def audit(report):
 r=read(report);root=report.parent;assert r['status']!='running' and r.get('inputs_unchanged') is True and r.get('container_termination',{}).get('status')=='absent','Probe must be settled/owned-cleaned/source-unchanged'
 custody={p:sha(p)==h for p,h in r['input_sha256'].items()};assert all(custody.values()),'Independent input recustody failed'
 before=root/'before';after=root/'after';required=['native-inventory.json','netlist.v','via-definitions.json','master-OBS-signature.json','checkpoint.def'];assert all((f/n).is_file() for f in [before,after] for n in required),'Complete native before/after readbacks absent'
 B=read(before/'native-inventory.json');A=read(after/'native-inventory.json');BV=read(before/'via-definitions.json');AV=read(after/'via-definitions.json');BM=read(before/'master-OBS-signature.json');AM=read(after/'master-OBS-signature.json')
 all_inventory_exact={k:v for k,v in B.items() if k!='canonical_all_TechLEF_sha256'}=={k:v for k,v in A.items() if k!='canonical_all_TechLEF_sha256'};original_vias_exact=all(AV.get(n)==v for n,v in BV.items());new_vias={n:v for n,v in AV.items() if n not in BV};viachecks={}
 for n,boxes in new_vias.items():
  levels=sorted({v[1] for v in boxes if v[1]>0});viachecks[n]=len(levels)==2 and 1<=levels[0]<levels[1]<=4 and levels[1]-levels[0]==1 and len(boxes)>=3 and all(v[2][0]<v[2][2] and v[2][1]<v[2][3] for v in boxes)
 blefs={f.name:lef(f) for f in before.glob('snapshot-tech-*.lef')};alefs={f.name:lef(f) for f in after.glob('snapshot-tech-*.lef')};assert blefs and set(blefs)==set(alefs)
 nonvia_rule_lines_exact=all(alefs[n][0]==blefs[n][0] for n in blefs);original_lef_vias_exact=all(all(alefs[n][1].get(v)==body for v,body in blefs[n][1].items()) for n in blefs)
 layeruse,outside=detailed_layers(after/'checkpoint.def',A);clocklayers={n:v for n,v in layeruse.items() if A['nets'][n]['sig_type']=='CLOCK'};signallayers={n:v for n,v in layeruse.items() if A['nets'][n]['sig_type']=='SIGNAL'}
 checks={'full_inventory_except_derived_technology_digest_exact':all_inventory_exact,'all_original_tech_and_block_via_definitions_exact':original_vias_exact,'all_nonblank_nonVIA_technology_rule_lines_exact':nonvia_rule_lines_exact,'all_original_TechLEF_VIA_blocks_exact':original_lef_vias_exact,'full_used_master_pin_geometry_and_OBS_signature_exact':AM==BM,'signal_netlist_bytes_exact':sha(before/'netlist.v')==sha(after/'netlist.v'),'generated_vias_structurally_adjacent_M1_M4_positive_geometry':all(viachecks.values()),'all_captured_detailed_SIGNAL_CLOCK_layers_M1_M4':not outside}
 native_log=(root/'native.log').read_text();detailed_attempt='PINWHEEL_NO_ECO_DRT_PINACCESS_BEGIN' in native_log;iteration_labels=[int(v) for v in re.findall(r'Start (\d+)(?:st|nd|rd|th) optimization iteration',native_log)]
 artifacts={str(report):sha(report)}
 for folder in [before,after]:
  for name in required:
   artifacts[str(folder/name)]=sha(folder/name)
  for f in folder.glob('snapshot-tech-*.lef'):artifacts[str(f)]=sha(f)
 for f in (root/'drt').rglob('*'):
  if f.is_file():artifacts[str(f)]=sha(f)
 if (root/'measurement.json').is_file():artifacts[str(root/'measurement.json')]=sha(root/'measurement.json')
 psm_after=[line for line in native_log.splitlines() if 'All shapes on net' in line];mastercount=len(BM)
 result={'schema':'pinwheel-no-ECO-DRT-independent-host-scope-audit-v1','status':'scope_verified' if all(checks.values()) else 'scope_rejected','checks':checks,'independent_input_recustody_all_exact':True,'independent_bound_input_count':len(custody),'source_instance_count':len(B['instances']),'after_instance_count':len(A['instances']),'used_master_count':mastercount,'source_CLOCK_net_count':sum(v['sig_type']=='CLOCK' for v in B['nets'].values()),'producer_status_retained':r['status'],'producer_exit_code_retained':r.get('exit_code'),'producer_not_relabelled':True,'full_native_measurement_available':(root/'measurement.json').is_file(),'native_DRT_attempt_marker_observed':detailed_attempt,'native_search_repair_iteration_labels_observed':iteration_labels,'new_generated_via_definition_count':len(new_vias),'new_generated_via_structural_checks':viachecks,'detailed_SIGNAL_nets_with_recorded_wire_layers':len(signallayers),'detailed_CLOCK_nets_with_recorded_wire_layers':len(clocklayers),'detailed_SIGNAL_CLOCK_layer_counts':{l:sum(l in v for v in [*signallayers.values(),*clocklayers.values()]) for l in ['Metal1','Metal2','Metal3','Metal4']},'detailed_SIGNAL_CLOCK_layers_outside_M1_M4':outside,'PG_connected_log_witnesses':psm_after,'input_sha256':artifacts,'boundary':'Independent comparison of complete native before/after readbacks. Only blank separator lines are ignored outside parsed TechLEF VIA blocks; original rules/via geometry and full master OBS are compared exactly. New native vias receive structural layer/shape checks, not a DRC waiver. Clock detailed wires may be new; clock topology remains exact. A failed producer stays failed; DRC/unroutes/pinaccess and signoff are separate.'}
 return result

def main():
 p=argparse.ArgumentParser();p.add_argument('--producer-report',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args();assert not a.output.exists();result=audit(a.producer_report);a.output.write_text(json.dumps(result,indent=2)+'\n');print(a.output,result['status'],result['producer_status_retained'],result['new_generated_via_definition_count'])
if __name__=='__main__':main()
