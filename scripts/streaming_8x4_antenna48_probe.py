"""Two separately admitted antenna observations; no physical policy is selected.

The final-target leaf only reads f516.  The initial leaf repeats the exact
historical wrapped command (including its frozen PG hook), captures its
failure state, then propagates the original Tcl error.  Root alone launches.
"""
import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time
import uuid

sys.dont_write_bytecode = True
import streaming_8x4_prepare as P
import streaming_8x4_run as R
import streaming_8x4_pg_diode as G
import streaming_8x4_pg_flow24 as PG
import streaming_8x4_route_replay as RR
import streaming_8x4_closure24_signoff_execute as V
from streaming_8x4_geometry import require, regular, sha
from streaming_tt_intake import dependency_closure
from streaming_tt_physical import inspect_runtime

ROOT = Path(__file__).resolve().parents[1]
CAMPAIGN = 'build/campaigns/8x4-20261025-01'
OLD = ROOT / 'build/campaigns/8x4-20261024-01'
SOURCE = ROOT / 'build/campaigns/8x4-20261022-01/intake/routing-replay-source-02'
ODB = 'f516ffbca3cd86e5cd214c515ca0be457a91a517dbe715caa47336aec907eee0'
# Actual pinned-image executable witness in the preserved replay journal.
OPENROAD_SHA = 'b2159d4a99a9b236a6e95bbf6efc88bcfd2b843df273e97f169b456bc3b0453b'
NET = 'engine.core._0083_.Y'
TOP = 'tt_um_pinwheel_streaming_ready_d2'
MODES = ('final-observe', 'initial-failure-capture')
LIMITS = {'final-observe': 120, 'initial-failure-capture': 180}
OUTER_LIMITS = {'final-observe': 150, 'initial-failure-capture': 240}
OWN = 'scripts/streaming_8x4_antenna48_probe.py'
ENTRIES = (OWN, 'scripts/streaming_8x4_antenna48_probe_readback.py')
SOURCE_FILES = ('GlobalRouter.cpp', 'GlobalRouter.tcl', 'RepairAntennas.cpp',
                'AntennaChecker.cc', 'AntennaChecker.tcl')
FALSE_SCOPE = dict(physical_acceptance=False, antenna_acceptance=False,
    eligible_final_target=False, physical_policy_registered=False,
    model_qualified=False, qualified_timing=False, tapeout_ready=False)


def bound(path):
    path = regular(path).resolve()
    return dict(path=str(path), sha256=sha(path))


def write(path, value):
    path = Path(path)
    with path.open('x') as stream:
        stream.write(json.dumps(value, sort_keys=True, indent=2, allow_nan=False) + '\n')


def owned(path):
    path = Path(path).absolute()
    require(path.resolve().is_relative_to((ROOT / CAMPAIGN).resolve()) and
            not path.is_symlink(), 'New48 owned output required')
    return path


def source_context():
    """Retained primary source is data, never imported or executed."""
    RR.source_evidence(SOURCE)
    odb_root=OLD/'pg-blocked-layer-source-02';manifest=P.read(odb_root/'manifest.json')
    require(sha(odb_root/'manifest.json')==G.BLOCKED_RULE['source_manifest_sha256'] and
            manifest['commit']=='dcf36133a369abc8f3c5e5738cd4d82e4903c0e0',
            'Pinned OpenDB guide API source manifest differs')
    data=(odb_root/'db.h').read_bytes();item=manifest['files']['db.h']
    require(item['bytes']==len(data) and item['sha256']==sha(odb_root/'db.h') and
            item['git_blob']==hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest(),
            'Pinned OpenDB guide API header/blob differs')
    return {name: bound(SOURCE / name) for name in SOURCE_FILES} | {
        'db.h': bound(odb_root/'db.h'),
        'odb-manifest.json':bound(odb_root/'manifest.json'),
        'routing-manifest.json':bound(SOURCE/'manifest.json')}


def old_context(views_path, initial_path):
    # Keep the original closed-view authority's globals/65-source contract intact.
    views_path = regular(views_path).resolve()
    views, _ = V.closed_views(views_path)
    require(views['target']['actual_odb']['sha256'] == ODB,
            'Only the preserved final f516 baseline is admitted')
    initial_path = regular(initial_path).resolve()
    initial = PG.verify(initial_path.parent)
    require(initial['mode'] == 'initial-smoke' and initial['diagnostic_config_version'] == 2 and
            initial['resource_policy'] == PG.NATIVE_RESOURCES,
            'Exact executed initial02 config/resource authority required')
    full_path = Path(views['target']['pg_preparation']['path'])
    full = PG.verify(full_path.parent)
    require(full['mode'] == 'full' and full['resource_policy'] == PG.NATIVE_RESOURCES,
            'Exact final full01 config/resource authority required')
    failed_path = OLD / 'native-pg-B-initial-02/report.json'
    failed = P.read(failed_path)
    require(failed['status'] == 'failed' and failed['exit_code'] == 1 and
            failed['preparation'] == bound(initial_path) and
            failed['inputs_pdk_runtime_unchanged'] is True and
            failed['container_termination']['status'] == 'absent',
            'Preserve the closed failed initial94 attempt')
    log = failed_path.parent / 'native.log'
    text = log.read_text()
    require(all(token in text for token in ('Inserted 94 diodes.',
            'Found 71 antenna violations.', 'Found 62 antenna violations.',
            'Found 27 antenna violations.', 'Found 0 antenna violations.', 'GRT-0116')),
            'Original initial failure does not match the retained symptoms')
    require(all(sha(failed_path.parent / name) == pin for name, pin in
                failed['artifact_sha256'].items()), 'Original initial failure artifacts changed')
    call=failed_path.parent/'flow/step/pg-diode/call-001'
    call_files={name:bound(call/name) for name in
                ('before.tsv','postcanonical.tsv','postcanonical.def','plan.json','moves.tsv')}
    require(not (call/'applied.tsv').exists() and not (call/'verified.json').exists(),
            'Retained failure phase differs')
    hook=initial_path.parent/'inputs/hook.tcl'
    require(sha(hook)=='844eba7df7e1227de1292b78f22daf5a9881821f7e7a5d3fb5de960a137d577e' and
            sha(hook)==initial['input_sha256']['hook.tcl'], 'Exact executed original PG hook differs')
    return views, full, initial, dict(views_report=bound(views_path),
        initial_preparation=bound(initial_path), full_preparation=bound(full_path),
        failed_initial_report=bound(failed_path), failed_initial_log=bound(log),
        original_initial_hook=bound(hook),failed_initial_call=call_files)


def capture_definitions():
    # Exact previously executed v2 census: instance/terminal/PG/special/blockages.
    seam = 'proc ::pgd::directory {} {'
    require(G.TCL.count(seam) == 1, 'Executed capture definition seam changed')
    return 'namespace eval ::pgd {}\n' + G.TCL.split(seam)[0]


GUIDES = r'''
proc antenna48_guides {path} {
    set f [open $path w]
    foreach net [[ord::get_db_block] getNets] {
        foreach guide [$net getGuides] {
            set box [$guide getBox]
            set via [$guide getViaLayer];set via_name ""
            if {$via ne "NULL"} {set via_name [$via getName]}
            ::pgd::row $f GUIDE [$net getName] [[$guide getLayer] getName] $via_name [$box xMin] [$box yMin] [$box xMax] [$box yMax] [$guide isCongested] [$guide isJumper] [$guide isConnectedToTerm]
        }
    }
    close $f
}
proc antenna48_capture {prefix odb} {
    ::pgd::capture ${prefix}.tsv
    write_def ${prefix}.def
    antenna48_guides ${prefix}.guides.tsv
    if {$odb} {write_db ${prefix}.odb}
}
'''


def tcl(mode, canonical):
    require(mode in MODES, 'Unknown diagnostic mode')
    prefix = ('source $::env(SCRIPTS_DIR)/openroad/common/io.tcl\nread_current_odb\n' +
              capture_definitions() + GUIDES + '\nset out $::env(STEP_DIR)\n')
    if mode == 'final-observe':
        return prefix + r'''
antenna48_capture $out/baseline 0
check_placement -verbose -report_file_name $out/placement.json
set count [tee -variable all_antenna_log {check_antennas -report_file $out/all-antenna.rpt}]
set f [open $out/all-antenna.log w];puts $f $all_antenna_log;close $f
set target_count [tee -variable target_antenna_log {check_antennas -net engine.core._0083_.Y -verbose -report_file $out/target-antenna.rpt}]
set f [open $out/target-antenna.log w];puts $f $target_antenna_log;close $f
set f [open $out/observation.tsv w]
::pgd::row $f OBSERVATION final-observe $count $target_count
close $f
::pgd::capture $out/after.tsv
antenna48_guides $out/after.guides.tsv
'''
    # All original command preparation/flags are copied verbatim.  Only the
    # call is caught to save diagnostics; the original error/options propagate.
    needle = 'log_cmd repair_antennas {*}$arg_list\n'
    require(canonical.count('read_current_odb\n') == 1 and canonical.count(needle) == 1,
            'Canonical initial command/read seam changed')
    head = canonical.split('read_current_odb\n', 1)[1].split(needle, 1)[0]
    call = r'''
antenna48_capture $out/before 0
set status [catch {log_cmd repair_antennas {*}$arg_list} result options]
set f [open $out/canonical-result.tcllist w]
puts $f [list $status $result $options];close $f
set f [open $out/canonical-result.tsv w]
::pgd::row $f STATUS $status
::pgd::row $f RESULT_HEX [binary encode hex [encoding convertto utf-8 $result]]
::pgd::row $f OPTIONS_HEX [binary encode hex [encoding convertto utf-8 $options]]
close $f
# Capture errors must not erase the canonical failure.  Preserve both.
set capture_status [catch {antenna48_capture $out/postcanonical 1} capture_result capture_options]
set f [open $out/capture-result.tcllist w]
puts $f [list $capture_status $capture_result $capture_options];close $f
set f [open $out/capture-status.tsv w];::pgd::row $f CAPTURE $capture_status;close $f
if {$status != 0} {return -options $options $result}
if {$capture_status != 0} {return -options $capture_options $capture_result}
set f [open $out/unexpected-canonical-success.tsv w];puts $f {unexpected-success};close $f
error {Initial94 expected GRT-0116 was not reproduced; no physical pass}
'''
    return prefix + 'source /work/probe/inputs/frozen-initial-hook.tcl\n' + head + call


def stage(inputs):
    closure = dependency_closure(ROOT, ENTRIES)
    head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True, timeout=30).strip()
    sources = {}
    for name in closure['files']:
        raw = subprocess.check_output(['git', 'show', head + ':' + name], cwd=ROOT, timeout=30)
        require(hashlib.sha256(raw).hexdigest() == sha(ROOT / name), 'Commit new48 source first: ' + name)
        target = inputs / 'producer' / name
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(raw); sources[name] = sha(target)
    return head, closure, sources


def prepare(mode, views_path, initial_path, output):
    require(mode in MODES, 'Unknown diagnostic mode')
    views, full, initial, context = old_context(views_path, initial_path)
    baseline = full if mode == 'final-observe' else initial
    config_path = Path(context['full_preparation' if mode == 'final-observe' else 'initial_preparation']['path']).parent / 'inputs/config.json'
    canonical_root = ROOT / PG.PRIOR / 'intake/librelane-native-source/librelane/scripts/openroad'
    canonical_path = canonical_root / 'antenna_repair.tcl'
    require(sha(canonical_path) == baseline['native_package_sha256']['scripts/openroad/antenna_repair.tcl'],
            'Canonical initial Tcl changed')
    output = owned(output)
    require(not output.exists(), 'Preserve previous new48 preparation')
    inputs = output / 'inputs'; inputs.mkdir(parents=True)
    head, closure, producers = stage(inputs)
    shutil.copyfile(config_path, inputs / 'config.json')
    shutil.copyfile(canonical_path, inputs / 'canonical-initial.tcl')
    shutil.copyfile(context['original_initial_hook']['path'], inputs/'frozen-initial-hook.tcl')
    (inputs / 'observe.tcl').write_text(tcl(mode, canonical_path.read_text()))
    evidence = source_context()
    for name, row in evidence.items():
        target = inputs / 'source' / name; target.parent.mkdir(exist_ok=True)
        shutil.copyfile(row['path'], target)
    source_odb = views['target']['actual_odb'] if mode == 'final-observe' else initial['source_odb']
    packet = dict(schema='pinwheel.antenna48-probe-preparation.v1', mode=mode,
        context=context, source_odb=source_odb, source_evidence=evidence,
        source_config=bound(config_path), canonical_initial=bound(canonical_path),
        target=views['target'], original_preparation=full['original_preparation'],
        native_package_sha256=baseline['native_package_sha256'], runtime=baseline['runtime'],
        original_initial_inputs_sha256=initial['input_sha256'],
        pdk_root=baseline['pdk_root'], producer_commit=head, producer_dependency_closure=closure,
        producer_sha256=producers, inputs_sha256=P.inventory(inputs),
        leaf_timeout_seconds=LIMITS[mode], outer_timeout_seconds=OUTER_LIMITS[mode],
        resources=dict(cpus=2, openroad_threads=2, memory_bytes=6*1024**3,
            extra_swap_bytes=0, pids=256, tmpfs_mib=512),
        maximum_combined_work_seconds=330, maximum_combined_outer_seconds=390,
        source_database_mutated=False, expected_initial_failure='GRT-0116' if mode != 'final-observe' else None,
        **FALSE_SCOPE)
    write(output / 'preparation.json', packet)
    verify_preparation(output)
    return packet


def verify_preparation(output):
    output = owned(output); packet = P.read(output / 'preparation.json')
    require(packet.get('schema') == 'pinwheel.antenna48-probe-preparation.v1' and
            packet.get('mode') in MODES and all(packet.get(k) is v for k,v in FALSE_SCOPE.items()),
            'New48 diagnostic authority/scope differs')
    require(P.inventory(output / 'inputs') == packet['inputs_sha256'], 'Prepared input membership/bytes changed')
    views, full, initial, context = old_context(packet['context']['views_report']['path'],
                                              packet['context']['initial_preparation']['path'])
    require(context == packet['context'] and views['target'] == packet['target'], 'Baseline authority changed')
    mode = packet['mode']; baseline = full if mode == 'final-observe' else initial
    actual = views['target']['actual_odb'] if mode == 'final-observe' else initial['source_odb']
    require(bound(actual['path']) == actual == packet['source_odb'], 'Exact selected/initial ODB changed')
    require(bound(packet['source_config']['path']) == packet['source_config'] and
            sha(output / 'inputs/config.json') == packet['source_config']['sha256'], 'Config byte identity changed')
    expected_config = Path(context['full_preparation' if mode == 'final-observe' else 'initial_preparation']['path']).parent / 'inputs/config.json'
    require(packet['source_config'] == bound(expected_config), 'Different canonical config selected')
    require(bound(packet['canonical_initial']['path']) == packet['canonical_initial'] and
            sha(output / 'inputs/canonical-initial.tcl') == packet['canonical_initial']['sha256'] ==
            baseline['native_package_sha256']['scripts/openroad/antenna_repair.tcl'], 'Canonical Tcl changed')
    require((output / 'inputs/observe.tcl').read_text() == tcl(mode, (output / 'inputs/canonical-initial.tcl').read_text()),
            'Observation/catch overlay differs')
    require(packet['source_evidence'] == source_context() and
            all(sha(output/'inputs/source'/n) == row['sha256'] for n,row in packet['source_evidence'].items()),
            'Retained primary API evidence changed')
    require(packet['runtime'] == baseline['runtime'] and packet['pdk_root'] == baseline['pdk_root'] and
            packet['native_package_sha256'] == baseline['native_package_sha256'] and
            packet['original_preparation'] == full['original_preparation'], 'Native baseline changed')
    require(sha(output/'inputs/frozen-initial-hook.tcl')==context['original_initial_hook']['sha256'] and
            packet['original_initial_inputs_sha256']==initial['input_sha256'], 'Original wrapped-call inputs differ')
    require(packet['leaf_timeout_seconds'] == LIMITS[mode] and packet['outer_timeout_seconds'] == OUTER_LIMITS[mode] and
            packet['resources'] == dict(cpus=2,openroad_threads=2,memory_bytes=6*1024**3,extra_swap_bytes=0,pids=256,tmpfs_mib=512) and
            packet['maximum_combined_work_seconds'] == 330 and packet['maximum_combined_outer_seconds'] == 390,
            'Diagnostic budget/resource policy changed')
    require(dependency_closure(ROOT, ENTRIES) == packet['producer_dependency_closure'] and
            set(packet['producer_sha256']) == set(packet['producer_dependency_closure']['files']), 'Producer closure differs')
    for name, pin in packet['producer_sha256'].items():
        raw = subprocess.check_output(['git','show',packet['producer_commit']+':'+name],cwd=ROOT,timeout=30)
        require(hashlib.sha256(raw).hexdigest() == sha(ROOT/name) == sha(output/'inputs/producer'/name) == pin,
                'Committed producer/staged bytes changed: '+name)
    return packet


def native_step(mode):
    """Called only in Root's pinned, offline, bounded container."""
    from librelane.steps import openroad
    from librelane.steps.tclstep import TclStep
    from librelane.state import State
    inputs = Path('/work/probe/inputs'); packet = P.read('/work/preparation.json')
    require(packet['schema']=='pinwheel.antenna48-probe-preparation.v1' and packet['mode']==mode,
            'Native diagnostic mode differs')
    require(P.inventory(inputs)==packet['inputs_sha256'] and sha('/work/seed.odb')==packet['source_odb']['sha256'],
            'Native input/ODB seals differ')
    if mode=='initial-failure-capture':
        require(P.inventory(Path('/work/closure/inputs'))==packet['original_initial_inputs_sha256'],
                'Original PG hook/helper/request input bytes differ')
    limits = {n:Path('/sys/fs/cgroup',n).read_text().strip() for n in
              ('cpu.max','memory.max','memory.swap.max','pids.max')}
    cpu = limits['cpu.max'].split()
    require(len(cpu)==2 and all(v.isdigit() for v in cpu) and int(cpu[0])==2*int(cpu[1]) and
            limits['memory.max']==str(6*1024**3) and limits['memory.swap.max']=='0' and limits['pids.max']=='256',
            'Native resource policy differs')
    write('/work/metadata/native-limits.json',limits)
    RR.package_unchanged(Path(openroad.__file__).resolve().parents[1],packet['native_package_sha256'])
    config=P.read(inputs/'config.json')
    require(sha(inputs/'config.json')==packet['source_config']['sha256'] and
            config.get('OPENROAD_THREADS')==2 and config.get('CLOCK_PERIOD')==20 and
            config.get('DESIGN_NAME')==TOP and config.get('PNR_SDC_FILE')=='/work/inputs/core.sdc',
            'Native exact executed config differs')
    write('/work/metadata/config-binding.json',dict(mode=mode,source_config=packet['source_config'],
        actual_sha256=sha(inputs/'config.json'),exact_membership_and_values=True,
        added_config_fields=[],changed_config_fields=[],physical_acceptance=False))
    base=openroad.DetailedRouting if mode=='final-observe' else openroad._DiodeInsertion
    journal=Path('/work/metadata/native-journal.jsonl')
    delegate=TclStep.run_subprocess
    def observed(self,argv,*args,**kwargs):
        env=kwargs['env'];selected=shutil.which(str(argv[0]),path=env.get('PATH'))
        require(selected is not None,'Canonical executable absent from actual child PATH')
        executable=Path(selected).resolve();pin=sha(executable)
        start=dict(event='start',step=self.id,argv=[str(x) for x in argv],
            resolved_executable=str(executable),executable_sha256=pin,
            env={str(k):str(v) for k,v in env.items()})
        with journal.open('a') as stream:stream.write(json.dumps(start,sort_keys=True)+'\n')
        code=None
        try:
            require(str(argv[0])=='openroad' and executable.is_absolute() and
                    executable.name=='openroad' and pin==OPENROAD_SHA,
                    'Canonical executable token/resolved payload differs from pinned actual image')
            result=delegate(self,argv,*args,**kwargs);code=result['returncode'];return result
        except subprocess.CalledProcessError as error:
            code=error.returncode
            raise
        finally:
            with journal.open('a') as stream:stream.write(json.dumps(dict(event='finish',
                exit_code=code,resolved_executable_after=str(executable.resolve()),
                executable_sha256_after=sha(executable)),sort_keys=True)+'\n')
    class Observe(base):
        id='Pinwheel.Antenna48Observe'
        name='Read-only final observation' if mode=='final-observe' else 'Expected initial canonical failure capture'
        outputs=[]
        def get_script_path(self):return str(inputs/'observe.tcl')
        run_subprocess=observed
    start=time.monotonic(); result=dict(schema='pinwheel.antenna48-native.v1',mode=mode,
        completed=False,source_odb_sha256=packet['source_odb']['sha256'],**FALSE_SCOPE)
    try:
        loaded=Observe._load_config_from_file(inputs/'config.json','/work/pdk')
        step=Observe(loaded,State.load(dict(odb='/work/seed.odb',metrics={})))
        step.start(step_dir='/work/run/step');result.update(completed=True,exit_code=0)
    except BaseException as error:
        result.update(exit_code=1,error=type(error).__name__+': '+str(error))
    finally:
        result['wall_seconds']=time.monotonic()-start
        result['source_odb_unchanged']=sha('/work/seed.odb')==packet['source_odb']['sha256']
        result['inputs_unchanged']=P.inventory(inputs)==packet['inputs_sha256']
        if mode=='initial-failure-capture':
            result['original_hook_inputs_unchanged']=P.inventory(Path('/work/closure/inputs'))==packet['original_initial_inputs_sha256']
        RR.package_unchanged(Path(openroad.__file__).resolve().parents[1],packet['native_package_sha256'])
        write('/work/metadata/native.json',result)
    return result['exit_code']


def command(preparation,output,packet,name,owner):
    require(re.fullmatch(r'pinwheel-[A-Za-z0-9_-]+',name) and str(uuid.UUID(owner))==owner,
            'Invalid owned container identity')
    base=Path(packet['original_preparation']['path']).parent
    argv=['docker','run','--rm','--pull','never','--name',name,
        '--label','org.pinwheel.streaming8_owner='+owner,'--network','none',
        '--cpus','2','--memory','6g','--memory-swap','6g','--pids-limit','256',
        '--read-only','--tmpfs','/tmp:rw,size=512m','--cap-drop','ALL','--security-opt','no-new-privileges',
        '--env','PYTHONDONTWRITEBYTECODE=1','--env',
        'PYTHONPATH=/work/probe/inputs/producer/scripts:/work/inputs',
        '--mount',f'type=bind,source={preparation/"inputs"},target=/work/probe/inputs,readonly',
        '--mount',f'type=bind,source={preparation/"preparation.json"},target=/work/preparation.json,readonly',
        '--mount',f'type=bind,source={base/"inputs"},target=/work/inputs,readonly',
        '--mount',f'type=bind,source={packet["pdk_root"]},target=/work/pdk,readonly',
        '--mount',f'type=bind,source={packet["source_odb"]["path"]},target=/work/seed.odb,readonly',
        '--mount',f'type=bind,source={output/"flow"},target=/work/run',
        '--mount',f'type=bind,source={output/"metadata"},target=/work/metadata',
        '--workdir','/work/inputs',packet['runtime']['image_id'],'python3','-B',
        '/work/probe/inputs/producer/'+OWN,'native-step','--mode',packet['mode']]
    if packet['mode']=='initial-failure-capture':
        original=Path(packet['context']['initial_preparation']['path']).parent/'inputs'
        index=argv.index('--workdir');argv[index:index]=[
            '--mount',f'type=bind,source={original},target=/work/closure/inputs,readonly']
    return argv


def artifacts(output):
    return {str(p.relative_to(output)):sha(p) for p in sorted(output.rglob('*'))
            if p.is_file() and p!=output/'report.json'}


def guide_census(text):
    rows=[];layers=Counter();congested=Counter();target=[]
    for line in text.splitlines():
        row=line.split('\t')
        require(len(row)==11 and row[0]=='GUIDE' and row[1] and
                re.fullmatch(r'Metal[1-5]|TopMetal[12]',row[2]) and
                (row[3]=='' or re.fullmatch(r'Metal[1-5]|TopMetal[12]',row[3])) and
                all(re.fullmatch(r'-?\d+',v) for v in row[4:8]) and
                all(v in ('0','1') for v in row[8:]), 'Malformed/unobserved DB-guide record')
        box=list(map(int,row[4:8]));require(box[0]<box[2] and box[1]<box[3], 'Nonpositive DB-guide rectangle')
        value=dict(net=row[1],layer=row[2],via_layer=row[3],box=box,
            congested=row[8]=='1',jumper=row[9]=='1',connected_to_term=row[10]=='1')
        rows.append(value);layers[row[2]]+=1;congested[row[2]]+=row[8]=='1'
        if row[1]==NET:target.append(value)
    return dict(stored_guides=len(rows),layers=dict(sorted(layers.items())),
        congested_by_layer=dict(sorted(congested.items())),target_net_guides=target,
        scope='Stored DB-guide observations; absence is not proof that no in-memory router route existed')


def classify(mode,step,native,execution,previous_call=None):
    require(native.get('mode')==mode and native.get('source_odb_unchanged') is True and
            native.get('inputs_unchanged') is True and
            execution.get('container_termination',{}).get('status')=='absent', 'Native input/cleanup did not close')
    require(execution.get('status')=='completed', 'Interrupted/timed-out attempt is not a closed observation')
    before=G.read_snapshot(step/('baseline.tsv' if mode=='final-observe' else 'before.tsv'))
    if mode=='final-observe':
        require(native.get('completed') is True and native.get('exit_code')==0 and
                execution.get('status')=='completed' and execution.get('exit_code')==0,
                'Final observation process did not close normally')
        row=(step/'observation.tsv').read_text().strip().split('\t')
        require(row==['OBSERVATION','final-observe','1','1'], 'Exact residual one-net ARC reproduction differs')
        detailed=(step/'target-antenna.rpt').read_text()
        require(NET in detailed and 'fanout276' in detailed and 'Metal3' in detailed and
                'VIOLATED' in detailed and '213.80' in detailed, 'Target detailed antenna residual differs')
        require((step/'placement.json').is_file() and (step/'baseline.def').is_file() and
                (step/'baseline.guides.tsv').is_file(), 'Final geometry/placement/guide captures missing')
        require(G.read_snapshot(step/'after.tsv')==before and
                (step/'after.guides.tsv').read_bytes()==(step/'baseline.guides.tsv').read_bytes(),
                'Read-only query changed instance/PG/public/connection/guide census')
        return dict(measurement_complete=True,expected_failure_captured=False,
            antenna_failure_reproduced=True,full_net_violations=1,target_net_violations=1,
            instances=len(before['instances']),terminals=len(before['terminals']),
            pg_shapes=len(before['pg']),special_shapes=len(before['special']),
            guides=guide_census((step/'baseline.guides.tsv').read_text()),**FALSE_SCOPE)
    require(native.get('completed') is False and native.get('exit_code')==1 and
            native.get('original_hook_inputs_unchanged') is True and
            execution.get('status')=='completed' and execution.get('exit_code')==1,
            'Initial canonical physical failure must stay a failed process')
    require((step/'capture-status.tsv').read_text()=='CAPTURE\t0\n', 'Postfailure capture did not complete')
    rows=[r.split('\t') for r in (step/'canonical-result.tsv').read_text().splitlines()]
    require(len(rows)==3 and rows[0]==['STATUS','1'] and rows[1][0]=='RESULT_HEX' and rows[2][0]=='OPTIONS_HEX',
            'Original Tcl result/options inventory differs')
    result=bytes.fromhex(rows[1][1]).decode('utf-8');options=bytes.fromhex(rows[2][1]).decode('utf-8')
    require('GRT-0116' in result and '-errorinfo' in options and '-code' in options and
            'grt::end_incremental' in options,
            'Exact strict-congestion Tcl failure was not retained')
    after=G.read_snapshot(step/'postcanonical.tsv')
    require(set(before['instances'])<=set(after['instances']), 'Initial repair removed original instances')
    added=sorted(set(after['instances'])-set(before['instances']))
    require(len(added)==94 and all(after['instances'][n]['master']==G.MASTER for n in added),
            'Canonical94 diode insertion reproduction differs')
    require(before['pg']==after['pg'] and before['special']==after['special'] and before['ports']==after['ports'] and
            before['public']==after['public'], 'Initial diagnostic changed PG/public geometry')
    require((step/'postcanonical.odb').is_file() and (step/'postcanonical.def').is_file() and
            (step/'postcanonical.guides.tsv').is_file() and (step/'canonical-result.tcllist').is_file() and
            (step/'capture-result.tcllist').is_file(), 'Initial error-state captures incomplete')
    require(type(previous_call) is dict and set(previous_call)==
            {'before.tsv','postcanonical.tsv','postcanonical.def','plan.json','moves.tsv'},
            'Exact original post-return PG stage authority required')
    require(all(bound(row['path'])==row for row in previous_call.values()), 'Original PG-stage evidence changed')
    current_call=step/'pg-diode/call-001'
    require(all((current_call/name).is_file() for name in previous_call) and
            not (current_call/'applied.tsv').exists() and not (current_call/'verified.json').exists(),
            'Reproduction did not reach the same post-return/pre-applied PG phase')
    previous_plan=P.read(previous_call['plan.json']['path']);plan=P.read(current_call/'plan.json')
    require(plan['schema']==previous_plan['schema'] and plan['policy']==previous_plan['policy']=='B' and
            plan['policy_definition']==previous_plan['policy_definition'] and
            len(plan['targets'])==len(plan['moves'])==94 and
            set(plan['targets'])==set(previous_plan['targets'])==set(added) and
            plan['physical_acceptance'] is False, 'Original94-target B-plan scope differs')
    projection=lambda value:[{key:row[key] for key in ('instance','x','y','orient','box')} for row in value['moves']]
    require(projection(plan)==projection(previous_plan), 'Original94 ordered PG assignments differ')
    canonical=G.read_snapshot(current_call/'postcanonical.tsv')
    require(canonical==G.read_snapshot(previous_call['postcanonical.tsv']['path']),
            'Canonical post-return snapshot differs from original failed initial02')
    targets=set(added)
    require(all(after['instances'][row['instance']]['box']==tuple(row['box']) and
                after['instances'][row['instance']]['orient']==row['orient'] for row in plan['moves']) and
            all(value==after['instances'][name] for name,value in canonical['instances'].items() if name not in targets),
            'Actual postfailure placements do not match complete planned targets/nontarget conservation')
    moved=[row for row in plan['moves'] if list(row['before']['box'])!=row['box'] or row['before']['orient']!=row['orient']]
    return dict(measurement_complete=True,expected_failure_captured=True,
        original_physical_failure_preserved=True,canonical_tcl_status=1,canonical_error=result,
        canonical_options=options,new_diodes=added,diode_count=94,diagnostic_only=True,
        canonical_repair_returned=True,original_pg_hook_reached=True,
        failed_phase='PG grt::end_incremental after applying planned diode assignments',
        original_ordered_assignment_plan_reproduced=True,physically_moved_diodes=len(moved),
        unchanged_target_assignments=94-len(moved),original_stage_evidence=previous_call,
        before_guides=guide_census((step/'before.guides.tsv').read_text()),
        after_guides=guide_census((step/'postcanonical.guides.tsv').read_text()),**FALSE_SCOPE)


def native_evidence(output,packet):
    limits=P.read(output/'metadata/native-limits.json');cpu=limits['cpu.max'].split()
    require(len(cpu)==2 and all(v.isdigit() for v in cpu) and int(cpu[0])==2*int(cpu[1]) and
            limits['memory.max']==str(6*1024**3) and limits['memory.swap.max']=='0' and limits['pids.max']=='256',
            'Actual cgroup policy differs')
    binding=P.read(output/'metadata/config-binding.json')
    require(binding==dict(mode=packet['mode'],source_config=packet['source_config'],
        actual_sha256=packet['source_config']['sha256'],exact_membership_and_values=True,
        added_config_fields=[],changed_config_fields=[],physical_acceptance=False), 'Actual exact config audit differs')
    rows=[json.loads(line) for line in (output/'metadata/native-journal.jsonl').read_text().splitlines()]
    require(len(rows)==2 and rows[0].get('event')=='start' and rows[1].get('event')=='finish',
            'Exactly one actual OpenROAD invocation required')
    start,finish=rows;argv=start['argv'];env=start['env']
    require(start['step']=='Pinwheel.Antenna48Observe' and len(argv)==8 and
            argv[0]=='openroad' and argv[1:]==
            ['-exit','-threads','2','-no_splash','-metrics','/work/run/step/or_metrics_out.json',
             '/work/probe/inputs/observe.tcl'] and
            Path(start['resolved_executable']).is_absolute() and Path(start['resolved_executable']).name=='openroad' and
            finish['resolved_executable_after']==start['resolved_executable'] and
            start['executable_sha256']==finish['executable_sha256_after']==OPENROAD_SHA,
            'Actual OpenROAD command/executable differs')
    expected=0 if packet['mode']=='final-observe' else 1
    require(finish['exit_code']==expected, 'Canonical OpenROAD raw exit differs')
    config=P.read(Path(packet['source_config']['path']));corner=config['DEFAULT_CORNER']
    require(all(env.get(k)==v for k,v in dict(CURRENT_ODB='/work/seed.odb',
        PNR_SDC_FILE='/work/inputs/core.sdc',_SDC_IN='/work/inputs/core.sdc',OPENROAD_THREADS='2').items()) and
        env.get('_LIB_CORNER_0','').split()==[corner]+config['CELL_LIBS'][corner] and
        '_LIB_CORNER_1' not in env, 'Actual ODB/SDC/default-cell-corner environment differs')
    return dict(actual_cgroups=limits,exact_config_binding=binding,native_journal=rows)


def run(preparation,output,name):
    preparation=owned(preparation);packet=verify_preparation(preparation);output=owned(output)
    require(not output.exists(), 'Preserve previous new48 Native attempt')
    output.mkdir();(output/'flow').mkdir();(output/'metadata').mkdir()
    runtime=inspect_runtime(P.read(ROOT/'tools/physical-toolchain.json'))
    RR.validate_runtime(runtime,packet['runtime']);owner=str(uuid.uuid4())
    argv=command(preparation,output,packet,name,owner)
    start=time.monotonic()
    execution=V.owned_native(argv,output,owner,packet['leaf_timeout_seconds'])
    row=dict(schema='pinwheel.antenna48-probe-run.v1',mode=packet['mode'],
        preparation=bound(preparation/'preparation.json'),runtime=runtime,execution=execution,
        measurement_complete=False,passed=False,**FALSE_SCOPE)
    try:
        native=P.read(output/'metadata/native.json')
        row['native_evidence']=native_evidence(output,packet)
        row['observation']=classify(packet['mode'],output/'flow/step',native,execution,
            packet['context']['failed_initial_call'])
        require(verify_preparation(preparation)==packet and
                inspect_runtime(P.read(ROOT/'tools/physical-toolchain.json'))==runtime,
                'Inputs/PDK/runtime changed after observation')
        row['measurement_complete']=True;row['inputs_pdk_runtime_unchanged']=True
    except BaseException as error:
        row['error']=type(error).__name__+': '+str(error)
    row['wall_seconds']=time.monotonic()-start;row['artifact_sha256']=artifacts(output)
    write(output/'report.json',row)
    return row


def reopen(path):
    path=regular(path).resolve();output=owned(path.parent);row=P.read(path)
    require(row.get('schema')=='pinwheel.antenna48-probe-run.v1' and
            all(row.get(k) is v for k,v in FALSE_SCOPE.items()) and row.get('passed') is False,
            'Diagnostic report cannot grant acceptance')
    require(row['artifact_sha256']==artifacts(output), 'Complete diagnostic artifact membership/bytes differ')
    require(bound(row['preparation']['path'])==row['preparation'], 'Prepared authority changed')
    preparation=Path(row['preparation']['path']).parent;packet=verify_preparation(preparation)
    require(row['mode']==packet['mode'] and row['runtime']==packet['runtime'], 'Mode/runtime differs')
    execution=P.read(output/'execution.json')
    require(execution==row['execution'] and execution['timeout_seconds']==packet['leaf_timeout_seconds'] and
            execution['argv']==command(preparation,output,packet,
                execution['argv'][execution['argv'].index('--name')+1],execution['owner']),
            'Actual command/resources/mounts/execution receipt differ')
    observed=classify(packet['mode'],output/'flow/step',P.read(output/'metadata/native.json'),execution,
        packet['context']['failed_initial_call'])
    require(row.get('measurement_complete') is True and row.get('inputs_pdk_runtime_unchanged') is True and
            observed==row.get('observation') and native_evidence(output,packet)==row.get('native_evidence') and
            row['wall_seconds']<=packet['outer_timeout_seconds'],
            'Closed diagnostic measurement/budget differs')
    return row


def main():
    parser=argparse.ArgumentParser();sub=parser.add_subparsers(dest='command',required=True)
    p=sub.add_parser('prepare');p.add_argument('--mode',choices=MODES,required=True)
    p.add_argument('--views-report',required=True);p.add_argument('--initial-preparation',required=True);p.add_argument('--output',required=True)
    p=sub.add_parser('verify-preparation');p.add_argument('--prepared',required=True)
    p=sub.add_parser('native-step');p.add_argument('--mode',choices=MODES,required=True)
    p=sub.add_parser('run');p.add_argument('--prepared',required=True);p.add_argument('--output',required=True);p.add_argument('--name',required=True)
    p=sub.add_parser('verify');p.add_argument('--report',required=True)
    args=parser.parse_args()
    if args.command=='prepare':result=prepare(args.mode,args.views_report,args.initial_preparation,args.output)
    elif args.command=='verify-preparation':result=verify_preparation(args.prepared)
    elif args.command=='native-step':return native_step(args.mode)
    elif args.command=='run':
        result=run(args.prepared,args.output,args.name)
        print(json.dumps(dict(report=str(Path(args.output)/'report.json'),measurement_complete=result['measurement_complete'],passed=False)))
        code=result['execution'].get('exit_code')
        return code if type(code) is int and code!=0 else (0 if result['measurement_complete'] else 2)
    else:result=reopen(args.report)
    print(json.dumps(dict(schema=result['schema'],mode=result['mode'],physical_acceptance=False)))
    return 0


if __name__=='__main__':raise SystemExit(main())
