"""Read-only pinned executable verification; no GRT/ECO/incremental execution."""
import json,os,sys,hashlib,ctypes
from pathlib import Path
from openroad import Tech,Design
from native_inventory import snapshot
R=Path('/work/diagnostic');design=Design(Tech())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def tcl(s):
    r=design.evalTclString('if {[catch {\n'+s+'\n} msg opts]} {puts stderr $msg; exit 2}; set ::pw_check PINWHEEL_TCL_OK');assert r=='PINWHEEL_TCL_OK',r

def pointer():
    q=design.getGlobalRouter();return int(q.this if hasattr(q,'this') else q)

tcl('source /work/diagnostic/load.tcl\nsource $::env(SCRIPTS_DIR)/openroad/common/set_rc.tcl\nread_global_route_segments /work/diagnostic/after_grt.segments')
before=snapshot(design.getDb(),design.getBlock(),'verify-before');p1=pointer();p2=pointer();assert p1==p2
# Exact report/check command options used by the LIVE worker.
tcl('estimate_parasitics -global_routing -spef_file /work/diagnostic/verified.spef\nreport_checks -sort_by_slack -path_delay min -fields {slew cap input net fanout} -format full_clock_expanded -group_path_count 1000 -digits 6 > /work/diagnostic/min.rpt\nreport_checks -sort_by_slack -path_delay max -fields {slew cap input net fanout} -format full_clock_expanded -group_path_count 1000 -digits 6 > /work/diagnostic/max.rpt\nset f [open /work/diagnostic/numbers.txt w]\nputs $f [worst_slack -min]\nputs $f [worst_slack -max]\nclose $f\nset_debug_level GRT incr 2\nset_debug_level GRT incr 0\nhelp global_route')
after=snapshot(design.getDb(),design.getBlock(),'verify-after');assert before==after,'Physical/logical geometry mutated by report-only verification'
assert pointer()==p1
nums=[float(x) for x in (R/'numbers.txt').read_text().splitlines()];assert len(nums)==2
for kind in ('min','max'):
    text=(R/(kind+'.rpt')).read_text();assert 'Startpoint:' in text and 'Endpoint:' in text and 'slack (' in text
sys.stdout.flush();ctypes.CDLL(None).fflush(None)
log=(R/'native.log').read_text();assert all(x in log for x in ('-start_incremental','-end_incremental','-allow_congestion'))
assert 'Global routing runtime' not in log and 'PINWHEEL_EXACT_ECO' not in log
receipt={'schema':'pinwheel-buffered-tt-incremental-eco-executable-verification-v1','status':'measured','native_report_redirection_verified':True,'exact_min_max_report_options_verified':True,'worst_slack_commands_verified':True,'typ_hold_worst_slack_ns':nums[0],'typ_setup_worst_slack_ns':nums[1],'stable_native_CPP_router_pointer':str(p1),'pointer_repeated_three_times_identical':True,'set_debug_level_global_command_verified':True,'global_route_incremental_flags_verified_in_executable_help':True,'incremental_calls_executed':0,'routing_calls_executed':0,'ECO_mutations_executed':0,'native_inventory_before_after_identical':True,'loaded_baseline_ODB_sha256':sha(R/'postcts.odb'),'loaded_exact_segments_sha256':sha(R/'after_grt.segments'),'native_binary_version':design.evalTclString('ord::openroad_version'),'boundary':'Read-only coldroute reader verifies command/API plumbing and RC reports; it does not qualify live no-op/incremental resource preservation.'}
(R/'measurement.json').write_text(json.dumps(receipt,indent=2)+'\n');print('PINWHEEL_EXECUTABLE_REPORT_API_VERIFICATION_PASSED',flush=True)
