"""Pure host admission rules. Importing this module cannot launch CAD."""
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path

PRODUCER_SHA = '147cf82e46f295260d128440f30ef73f86986d078d69460d20a4189ae5fc3a8a'
ODB_SHA = {
    'control': 'e0a0059bed3869367dccb72cc4e7d9029d81e5d735447668ae0b420b2889d629',
    'candidate': '8c3079c61f73f0f2819d4e0d21d0af2775d4afb76c620494e2841ace4b1dd063',
}
PREFLIGHT_SHA = '2d12d6a906cf7f3a7a6e91961688d95615a09a16155fe30a8710696b6116283e'
NATIVE_SECONDS = 300
ALL_IN_SECONDS = 420

@dataclass(frozen=True)
class Options:
    arm: str
    selection: Path
    selection_sha256: str
    verification: Path
    native_stop: float
    deadline: float
    control_report: Path | None = None

def utc_epoch(value):
    parsed = datetime.fromisoformat(value.replace('Z', '+00:00'))
    assert parsed.tzinfo is not None, 'Deadline must include UTC offset'
    return parsed.timestamp()

def validate_deadlines(native_stop, deadline, now):
    assert native_stop < deadline, 'Native STOP must precede full deadline'
    assert deadline - native_stop >= 120, 'Insufficient fixed cleanup/closeout reserve'
    assert now + NATIVE_SECONDS <= native_stop, 'Insufficient conservative native admission window'

def validate_libraries(producer, timing):
    assert len(producer) == 5 and len(timing) == 9, 'Unexpected native/timing library inventory'
    assert all(timing.get(name) == digest for name, digest in producer.items()), 'Native library not identical to timing basis'

def validate_producer(receipt, image):
    assert receipt['schema'] == 'pinwheel-buffered-tt-hold30712-route-v1'
    assert receipt['status'] == 'passed' and receipt['exit_code'] == 0
    assert receipt['image_id'] == image and receipt['inputs_unchanged']
    absence = receipt['container_termination']
    assert absence['status'] == 'absent' and not absence['owned_container_ids']
    assert absence['ownership_label'] == receipt['ownership_label']
    measured = receipt['measurement']
    assert measured['status'] == 'measured'
    for key in ['qualified_control_reproduction_passed','dirty_noop_pre_edit_gate_passed',
                'candidate_exact_edit_gate_passed','native_pure_placement_scope_passed',
                'native_clock_route_preservation_passed','all_unrelated_route_preservation_passed',
                'native_raw_capacity_preservation_passed','logical_netlist_bytes_identical',
                'fresh_PSM_both_nets_passed']:
        assert measured[key], ('Producer gate failed', key)
    assert measured['moved_instance_count'] == 1
    assert measured['allowed_route_change_nets'] == ['_03216_', 'timing_eco_hold_30712_D']
    assert measured['actual_changed_original_route_nets'] == measured['allowed_route_change_nets']

def validate_fresh_control(receipt):
    assert receipt['schema'] == 'pinwheel-buffered-tt-hold30712-fresh-sta-v1'
    assert receipt['arm'] == 'control' and receipt['status'] == 'passed' and receipt['exit_code'] == 0
    assert receipt['inputs_unchanged'] and receipt['container_termination']['status'] == 'absent'
    assert receipt['measurement']['native_process_count'] == 3
    assert receipt['measurement']['fresh_computational_control'] is True
    assert receipt['measurement']['routed_database_sha256'] == ODB_SHA['control']
    assert all(c['prior_qualified_global_timing_reproduced'] is True for c in receipt['measurement']['corners'].values())

def contained(root, path):
    resolved = Path(path).resolve()
    assert resolved.is_relative_to(root.resolve()) and resolved.is_file(), 'Source outside workspace or missing'
    return resolved

def merge_hashes(target, additions):
    for path, digest in additions.items():
        resolved = str(Path(path).resolve())
        assert len(digest) == 64 and all(c in '0123456789abcdef' for c in digest)
        assert target.get(resolved, digest) == digest, ('Conflicting input bindings', path)
        target[resolved] = digest
