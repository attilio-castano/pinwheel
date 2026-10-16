import argparse,datetime,json,shutil,time
from pathlib import Path
from common import ROOT,execute,sha,read,write
H=Path(__file__).resolve().parent;STOP=datetime.datetime.fromisoformat('2026-10-14T19:16:00+00:00').timestamp();END=datetime.datetime.fromisoformat('2026-10-14T19:16:45+00:00').timestamp()
def verify(items):
 for n,h in items.items():assert sha(Path(n))==h,n
def main():
 p=argparse.ArgumentParser();p.add_argument('--capability-report',type=Path,required=True);p.add_argument('--capability-sha256',required=True);p.add_argument('--tag',default='tt-p2-drt-onepass-route-01');a=p.parse_args();started=time.monotonic();P=read(H/'prepared.json');verify(P['source_sha256']);verify(P['tool_sha256']);assert sha(a.capability_report)==a.capability_sha256;C=read(a.capability_report);assert C['status']=='passed' and C['image_id']==P['image_id'] and C['detailed_route_default_pin_access_included'] is True and len(C['native_binary_sha256'])==64
 assert set(P['required_native_detailed_route_options'])<=set(C['detailed_route_supported_options'])
 assert a.tag=='tt-p2-drt-onepass-route-01' and STOP-time.time()>=1201;O=ROOT/'build/physical'/a.tag;assert not O.exists();O.mkdir()
 for n in ['common.py','native_inventory.py','native-script-hashes.json','load.tcl','native.py','coordinator.py']:shutil.copyfile(H/n,O/n)
 for original,target in P['staged_inputs'].items():shutil.copyfile(original,O/target)
 shutil.copyfile(a.capability_report,O/'capability-admission.json');shutil.copytree(ROOT/P['reference_root']/'lib',O/'lib')
 write(O/'corner-env.tcl','') if False else None
 (O/'corner-env.tcl').write_text('source /work/diagnostic/baseline-env.tcl\nset ::env(CURRENT_ODB) /work/diagnostic/input.odb\nset ::env(_SDC_IN) /work/diagnostic/core.sdc\nforeach key [array names ::env _LIB_CORNER_*] {unset ::env($key)}\nset ::env(_LIB_CORNER_0) {nom_typ_1p20V_25C /work/diagnostic/lib/sg13cmos5l_stdcell_typ_1p20V_25C.lib /work/diagnostic/lib/sg13cmos5l_io_typ_1p2V_3p3V_25C.lib /work/diagnostic/lib/RM_IHPSG13_1P_64x64_c2_bm_bist_typ_1p20V_25C.lib}\nset ::env(_PNR_EXCLUDED_CELLS) {}\nset ::env(OPENROAD_THREADS) 4\n')
 write(O/'phase-inputs.json',{str(Path('/work/diagnostic')/f.relative_to(O)):sha(f) for f in O.rglob('*') if f.is_file()});paths=[H/'prepared.json',a.capability_report,*map(Path,P['source_sha256']),*map(Path,P['tool_sha256']),*[f for f in O.rglob('*') if f.is_file()]]
 r=execute(O,paths,['python3','-B','/work/diagnostic/coordinator.py'],seconds=1260,cpus=4,memory='6g',schema='pinwheel-no-ECO-P2-DRT-onepass-v1',scope='Saved P2 native ODB+guides, actual pin access and one zero-based iteration0 detailed-routing probe (end_iter0 max1), all original inventory/RTL/ABI/SDC/PG/macros/NDR fixed; detailedCLOCK geometry legitimate.',extra={'source_database_sha256':P['source_database_sha256'],'source_guides_sha256':P['source_guides_sha256'],'prepared_sha256':sha(H/'prepared.json'),'native_capability_admission_sha256':a.capability_sha256},expected_hashes={O/'input.odb':P['source_database_sha256'],O/'input.guide':P['source_guides_sha256']},absolute_work_stop=STOP,all_in_deadline_monotonic=min(started+1320,time.monotonic()+END-time.time()))
 r['all_in_elapsed_seconds']=round(time.monotonic()-started,3);verify(P['source_sha256']);verify(P['tool_sha256']);write(O/'report.json',r);print(O/'report.json',r['status']);return 0 if r['status']=='passed' else 1
if __name__=='__main__':raise SystemExit(main())
