"""Host-only canonical-report summary, with separate per-report and connectivity evidence."""
import argparse,collections,hashlib,json,re
from pathlib import Path
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 a=argparse.ArgumentParser();a.add_argument('--diagnostic',type=Path,required=True);a.add_argument('--canonical-report',type=Path,required=True);a.add_argument('--inventory',type=Path,required=True);a.add_argument('--geometry',type=Path,required=True);a.add_argument('--producer-report',type=Path,required=True);a.add_argument('--native-log',type=Path,required=True);a.add_argument('--measurement',type=Path);a.add_argument('--output',type=Path,required=True);p=a.parse_args()
 D=json.loads(p.diagnostic.read_text());assert D['schema']=='pinwheel-native-drt-pinaccess-diagnostic-v5';I=json.loads(p.inventory.read_text());G=json.loads(p.geometry.read_text());P=json.loads(p.producer_report.read_text());assert P['status']!='running' and P['container_termination']['status']=='absent'
 for f in [p.inventory,p.geometry,p.producer_report,p.native_log]:assert D['input_sha256'][str(f.resolve())]==sha(f),str(f)
 expected=str(p.canonical_report.resolve());markers=[m for m in D['native_DRC_markers'] if str(Path(m['report_path']).resolve())==expected];reports=[r for r in D['drc_reports'] if str(Path(r['path']).resolve())==expected];assert len(reports)==1;report=reports[0]
 if report['availability']=='present':assert report['marker_count']==len(markers) and D['input_sha256'][expected]==sha(p.canonical_report)
 role_counts=collections.Counter();net_counts=collections.Counter();source_types=collections.Counter();macro_cone_pins=collections.Counter();zone_counts=collections.Counter();layer_zone_counts=collections.Counter()
 boxes=sorted([(n,v['bbox_dbu']) for n,v in G['macros'].items()],key=lambda v:v[1][1]);assert len(boxes)==2;left=min(b[0] for n,b in boxes);right=max(b[2] for n,b in boxes);bottom=boxes[0][1][1];top=boxes[-1][1][3]
 def zone(b):
  if b is None:return 'unparsed'
  x=(b[0]+b[2])/2;y=(b[1]+b[3])/2
  if y<bottom:return 'below_lower_SRAM'
  if y>=top:return 'above_upper_SRAM'
  if x<left:return 'left_macro_end_band'
  if x>=right:return 'right_macro_end_band'
  for n,q in boxes:
   if q[0]<=x<q[2] and q[1]<=y<q[3]:return 'inside_'+n+'_footprint'
  return 'between_SRAM_bodies'
 for m in markers:
  roles=set();nets=set();pins=set()
  for r in m['source_net_roles']:
   roles.update(r['roles']);source_types[r['source_object_type']]+=1
   if r['matched_net'] is not None:nets.add(r['matched_net'])
   pins.update(r['macro_pins'])
  role_counts.update(roles);net_counts.update(nets);macro_cone_pins.update(pins);z=zone(m['bbox_dbu']);zone_counts[z]+=1;layer_zone_counts[(m['layer'] or 'unparsed')+' / '+z]+=1
 failed=[]
 for r in D['native_connectivity_observations']['native_log_lines']:
  m=re.search(r'checkConnectivity break,\s*net\s+(\S+)',r['text'])
  if m:failed.append(dict(r,exact_failed_net=m[1],matched_source_net=m[1] in I['nets']))
 measurement=json.loads(p.measurement.read_text()) if p.measurement and p.measurement.exists() else None
 all_unmatched=collections.Counter(r.get('unmatched_source_token') for m in markers for r in m['source_net_roles'] if r.get('unmatched_source_token'))
 native_done=P['status']=='passed' and P.get('exit_code')==0 and measurement is not None and measurement.get('probe_command_returned_without_Tcl_error') is True
 result={'schema':'pinwheel-onepass-canonical-DRC-connectivity-summary-v1','status':'summarized-actual-native-evidence','input_sha256':{str(f.resolve()):sha(f) for f in [p.diagnostic,p.inventory,p.geometry,p.producer_report,p.native_log]},'summary_helper_sha256':sha(Path(__file__)),'producer_status':P['status'],'producer_exit_code':P.get('exit_code'),'owned_container_absent':True,'frozen_producer_inputs_unchanged':P.get('inputs_unchanged'),'actual_native_route_command_completed_without_Tcl_error':native_done,'measurement_native_Tcl_error':measurement.get('native_detailed_route_error') if measurement else None,'canonical_report':report,'canonical_report_marker_record_count':len(markers) if report['availability']=='present' else None,'per_report_record_counts_kept_independent':[{'path':r['path'],'availability':r['availability'],'marker_count':r['marker_count']} for r in D['drc_reports']],'canonical_type_counts':dict(collections.Counter(m['type'] for m in markers)),'canonical_layer_counts':dict(collections.Counter(m['layer'] or 'unparsed' for m in markers)),'canonical_unique_marker_source_role_counts':dict(role_counts),'canonical_source_object_token_type_counts':dict(source_types),'canonical_unique_source_net_count':len(net_counts),'canonical_source_net_marker_counts':dict(net_counts.most_common()),'canonical_associated_SRAM_pin_cone_marker_counts':dict(macro_cone_pins.most_common()),'unmatched_typed_source_tokens':dict(all_unmatched),'canonical_marker_center_zone_counts':dict(zone_counts),'canonical_layer_center_zone_counts':dict(layer_zone_counts),'zone_definition_dbu':{'lower_and_upper_SRAMs':dict(boxes),'macro_end_band_x_extent':[left,right],'macro_band_y_extent':[bottom,top],'centers_determine_disjoint_zone_not_overlap_causality':True},'spatial_parse_complete_marker_count':sum(m['spatial_parse_complete'] for m in markers),'zero_area_marker_bbox_count':sum(m['bbox_dbu'] is not None and (m['bbox_dbu'][0]==m['bbox_dbu'][2] or m['bbox_dbu'][1]==m['bbox_dbu'][3]) for m in markers),'same_layer_macro_OBS_overlap_marker_count':sum(bool(m['macro_obstruction_overlaps']) for m in markers),'same_layer_PG_overlay_overlap_marker_count':sum(bool(m['power_box_overlap_count']) for m in markers),'macro_footprint_overlap_marker_count':sum(bool(m['macro_footprint_overlaps']) for m in markers),'native_count_observation_ledger':D['observed_native_count_ledger'],'native_worker_progress_observations':D['native_worker_progress_violation_observations'],'native_PA_counters':D['native_pin_access_counters'],'unsupported_rule_warning_observations':D['unsupported_rule_warning_observations'],'native_connectivity_observations':D['native_connectivity_observations'],'native_connectivity_failed_net_observations':failed,'canonical_recheck_marker_count_potentially_connectivity_related_not_origin_proof':sum(m['type'].lower()=='recheck' for m in markers),'all_native_terminal_connectivity_zero_unroutes_claim':False,'native_checker_qualification':'Completed iteration without DRT-0206 conditionally passes modified-net/route-endpoint-mapped-pin checker; it does not independently enumerate all native ITerm/BTerm coverage. Recheck can arise from internal checks and is not automatically a connectivity failure.','source_checker_evidence':{'url':'https://raw.githubusercontent.com/The-OpenROAD-Project/OpenROAD/dcf36133a369abc8f3c5e5738cd4d82e4903c0e0/src/drt/src/dr/FlexDR_conn.cpp','mapped_pin_build_lines':[83,120],'mapped_pin_check_lines':[406,414],'modified_net_filter_lines':[1132,1145],'failure_lines':[1282,1310],'invocation_url':'https://raw.githubusercontent.com/The-OpenROAD-Project/OpenROAD/dcf36133a369abc8f3c5e5738cd4d82e4903c0e0/src/drt/src/dr/FlexDR.cpp','invocation_lines':[1338,1340]},'post_detail_extracted_timing_claim':False,'completed_foundry_DRC_LVS_or_GDS_precheck_claim':False,'boundary':'Canonical record counts, report siblings and provisional progress remain separate. Role/pin associations concern connected net cones, not exact causal ownership. Strict same-layer OBS/PG overlap can miss zero-area/boundary touch and adjacent-metal via interactions; absence does not exclude those causes. No full connectivity, signoff, precheck or extracted timing inference.'}
 if p.measurement and p.measurement.exists():result['input_sha256'][str(p.measurement.resolve())]=sha(p.measurement)
 assert not p.output.exists();p.output.parent.mkdir(parents=True,exist_ok=True);p.output.write_text(json.dumps(result,indent=2)+'\n');print(p.output,len(markers),sha(p.output))
if __name__=='__main__':main()
