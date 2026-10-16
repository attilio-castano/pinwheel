"""Offline regression and adverse-admission checks. Never imports the executor."""
import ast, copy, hashlib, json, tempfile, time
from pathlib import Path
from admission import (Options, ODB_SHA, PRODUCER_SHA, validate_deadlines,
    validate_libraries, validate_producer, validate_fresh_control, validate_selection_deadlines, contained, merge_hashes)

TOOLS=Path(__file__).resolve().parent
ROOT=TOOLS.parents[2]
IMAGE='sha256:5825633bea1f9cbc705ece2de2bc31de6e4ec83d233739205a0f265ef9d92f92'
PRODUCER=ROOT/'build/physical/tt-buffered-hold30712-route-02'
PREFLIGHT=ROOT/'build/physical/tt-buffered-hold30712-preflight-01'
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def read(path):return json.loads(path.read_text())

def main():
    started=time.monotonic();prepared=read(TOOLS/'prepared.json')
    for name,digest in prepared['tool_sha256'].items():assert sha(TOOLS/name)==digest
    for name,digest in prepared['source_sha256'].items():assert sha(Path(name))==digest
    cases=[]
    def reject(name,callback):
        try:callback()
        except (AssertionError,KeyError,ValueError):cases.append(dict(name=name,expected='rejected',passed=True))
        else:raise AssertionError('Negative admission accepted: '+name)
    producer=read(PRODUCER/'report.json');assert sha(PRODUCER/'report.json')==PRODUCER_SHA
    validate_producer(producer,IMAGE)
    producer_libs={p.name:sha(p) for p in (PRODUCER/'lib').glob('*.lib')}
    timing_libs={p.name:sha(p) for p in (PREFLIGHT/'preflight/lib').glob('*.lib')}
    validate_libraries(producer_libs,timing_libs)
    cases.append(dict(name='real5-native-files-exact-subset-of9-timing',expected='accepted',passed=True))
    reject('native-library-content-drift',lambda:validate_libraries({**producer_libs,next(iter(producer_libs)):'0'*64},timing_libs))
    reject('missing-timing-view',lambda:validate_libraries(producer_libs,dict(list(timing_libs.items())[:-1])))
    reject('unknown-native-view',lambda:validate_libraries({**dict(list(producer_libs.items())[:-1]),'unknown.lib':'0'*64},timing_libs))
    for name,edit in [
        ('failed-producer',lambda d:d.update(status='failed')),
        ('nonzero-producer-exit',lambda d:d.update(exit_code=1)),
        ('source-drift',lambda d:d.update(inputs_unchanged=False)),
        ('live-owned-container',lambda d:d['container_termination'].update(status='running',owned_container_ids=['a'*64])),
        ('wrong-producer-schema',lambda d:d.update(schema='other')),
        ('clock-route-drift',lambda d:d['measurement'].update(native_clock_route_preservation_passed=False)),
        ('additional-moved-cell',lambda d:d['measurement'].update(moved_instance_count=2))]:
        changed=copy.deepcopy(producer);edit(changed)
        reject(name,lambda changed=changed:validate_producer(changed,IMAGE))
    now=time.time();validate_deadlines(now+600,now+900,now)
    reject('expired-nativeSTOP',lambda:validate_deadlines(now-1,now+900,now))
    reject('insufficient-native-window',lambda:validate_deadlines(now+299,now+900,now))
    reject('missing-closeout-reserve',lambda:validate_deadlines(now+600,now+650,now))
    reject('naive-source-traversal',lambda:contained(ROOT,ROOT/'../../../etc/passwd'))
    reject('conflicting-source-hash',lambda:merge_hashes({str((ROOT/'README.md').resolve()):'a'*64},{str(ROOT/'README.md'):'b'*64}))
    # A real old host-only reuse receipt must never admit the fresh candidate.
    reuse=read(ROOT/'build/physical/tt-buffered-hold30712-control-timing-04/report.json')
    reject('host-only-control-reuse-not-fresh',lambda:validate_fresh_control(reuse))
    opts=Options('control',ROOT/'physical/experiments/example.json','a'*64,TOOLS/'verification.json',now+600,now+900)
    # This is the historical shadow trigger: loop over actual geometry using
    # distinct names, then prove the immutable typed arm remains available.
    for stage in ['baseline','noop']:
        geometry_current=read(PRODUCER/stage/'geometry.json')
        geometry_reference=read(PRODUCER/'baseline/geometry.json')
        assert geometry_current['layers']==geometry_reference['layers']
    assert opts.arm=='control'
    from datetime import datetime,timezone
    selected_deadlines={'native_stop_utc':datetime.fromtimestamp(opts.native_stop,timezone.utc).isoformat(),'deadline_utc':datetime.fromtimestamp(opts.deadline,timezone.utc).isoformat()}
    validate_selection_deadlines(opts,selected_deadlines)
    reject('CLI-nativeSTOP-outside-selection',lambda:validate_selection_deadlines(opts,{**selected_deadlines,'native_stop_utc':datetime.fromtimestamp(opts.native_stop+1,timezone.utc).isoformat()}))
    reject('CLI-full-deadline-outside-selection',lambda:validate_selection_deadlines(opts,{**selected_deadlines,'deadline_utc':datetime.fromtimestamp(opts.deadline+1,timezone.utc).isoformat()}))
    cases.append(dict(name='real-geometry-loop-preserves-typed-control-arm',expected='accepted',passed=True))
    for file in TOOLS.glob('*.py'):ast.parse(file.read_text())
    native=(TOOLS/'route-corner.tcl').read_text()
    import re
    assert not re.search(r'(?m)^\s*(global_route|detailed_route|global_placement|detailed_placement|repair_timing|repair_design)\b',native)
    assert 'read_global_route_segments' in native and 'estimate_parasitics -global_routing' in native
    assert 'estimate_parasitics -placement' not in native
    for name,digest in prepared['tool_sha256'].items():assert sha(TOOLS/name)==digest
    out=ROOT/'build/physical/tt-buffered-hold30712-sta-helper-verification-02';out.mkdir()
    receipt=dict(schema='pinwheel-buffered-tt-hold30712-sta-helper-verification-v1',status='passed',
        no_CAD_launched=True,prepared_sha256=sha(TOOLS/'prepared.json'),
        source_sha256=prepared['source_sha256'],tool_sha256=prepared['tool_sha256'],cases=cases,
        negative_controls_passed=sum(case['expected']=='rejected' for case in cases),
        healthy_real_input_controls_passed=sum(case['expected']=='accepted' for case in cases),
        syntax_all_helpers=True,native_scope_read_segments_estimateRC_STA_only=True,
        elapsed_seconds=round(time.monotonic()-started,3),
        scope='Offline host admission regressions with actual saved inputs and adverse fixtures; no native evaluator or Docker was launched. Fresh control3corner measurement is the end-to-end evaluator verification.')
    (out/'report.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(out/'report.json',sha(out/'report.json'),receipt['elapsed_seconds'])
if __name__=='__main__':main()
