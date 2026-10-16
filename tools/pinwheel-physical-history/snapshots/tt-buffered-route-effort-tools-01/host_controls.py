"""Host-only route-effort guard checks and immutable preparation; no CAD."""
from copy import deepcopy
import ast
import hashlib
import json
from pathlib import Path
import time
from driver import corner_environment, iterations_for
from route_checks import audit_route

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    started = time.monotonic()
    assert not (HERE / 'host-controls.json').exists() and not (HERE / 'prepared.json').exists()
    before = {
        'instances': {'clockbuf': {'bbox': [0, 0, 2, 4], 'orientation': 'R0', 'master': 'buf1', 'status': 'PLACED', 'terminals': ['clock']}, 'data': {'bbox': [4, 0, 6, 4], 'orientation': 'R0', 'master': 'buf1', 'status': 'PLACED', 'terminals': ['data']}},
        'nets': {'clock': {'sig_type': 'CLOCK', 'ports': ['clk'], 'terminals': [['clockbuf', 'A', 'INPUT']], 'nondefault_rule': 'CTS_NDR_0'}, 'data': {'sig_type': 'SIGNAL', 'ports': [], 'terminals': [['data', 'A', 'INPUT']], 'nondefault_rule': None}},
        'nondefault_rules': [['CTS_NDR_0', True, False, [['Metal2', True, 400, 200, 0, 0, 0, 0]], []]],
        'canonical_all_TechLEF_sha256': [['tech', 'unchanged']], 'routing_layer_defaults': {'Metal2': {'width_dbu': 400, 'spacing_dbu': 200}}, 'pins': ['clk'], 'special_wires': ['power'], 'macros': ['R0'], 'rows': ['row'], 'regions': [], 'groups': [], 'placement_blockages': [], 'die_bbox_dbu': [0, 0, 10, 10]}
    results = []
    assert audit_route(before, deepcopy(before))['all_frozen_native_invariants_passed']; results.append('identical native inventory admitted')
    natural = deepcopy(before); natural['nets']['clock']['nondefault_rule'] = None
    assert len(audit_route(before, natural)['CLOCK_NDR_association_changes']) == 1; results.append('native CLOCK-only NDR disable admitted and recorded')

    def reject(label, mutate):
        after = deepcopy(before); mutate(after)
        try: audit_route(before, after)
        except AssertionError: results.append(label); return
        raise AssertionError('Incorrectly admitted ' + label)

    for key, value in [('bbox', [1, 0, 3, 4]), ('orientation', 'MX'), ('master', 'buf2'), ('status', 'FIRM'), ('terminals', ['other'])]:
        reject('instance ' + key + ' mutation rejected', lambda a, k=key, v=value: a['instances']['data'].__setitem__(k, v))
    reject('clock placement mutation rejected', lambda a: a['instances']['clockbuf'].__setitem__('bbox', [1, 0, 3, 4]))
    for key in ('pins', 'special_wires', 'macros', 'rows', 'regions', 'groups', 'placement_blockages', 'canonical_all_TechLEF_sha256'):
        reject(key + ' mutation rejected', lambda a, k=key: a[k].append('changed'))
    reject('NDR width definition mutation rejected', lambda a: a['nondefault_rules'][0][3][0].__setitem__(2, 800))
    reject('nonclock NDR mutation rejected', lambda a: a['nets']['data'].__setitem__('nondefault_rule', 'CTS_NDR_0'))
    reject('unknown CLOCK NDR mutation rejected', lambda a: a['nets']['clock'].__setitem__('nondefault_rule', 'UNKNOWN'))
    reject('net terminal mutation rejected', lambda a: a['nets']['clock']['terminals'].append(['data', 'A', 'INPUT']))
    selection = {'schema': 'pinwheel-buffered-tt-route-effort-selection-v1', 'routing_effort': {'control_iterations': 5, 'probe_iterations': 10}}
    assert iterations_for(selection, 'control') == 5 and iterations_for(selection, 'probe') == 10
    for bad in [6, 9, 50]:
        changed = deepcopy(selection); changed['routing_effort']['probe_iterations'] = bad
        try: iterations_for(changed, 'probe')
        except AssertionError: pass
        else: raise AssertionError('Unselected iteration limit admitted')
    results.append('only exact control5/probe10 iteration policy admitted')
    prior = ROOT / 'build/physical/tt-buffered-access-incremental-control-route-01/corner-env.tcl'
    text = prior.read_text(); control = corner_environment(text, 5); probe = corner_environment(text, 10)
    assert control == text and probe.replace('set ::env(GRT_OVERFLOW_ITERS) 10', 'set ::env(GRT_OVERFLOW_ITERS) 5') == text
    results.append('actual retained environment differs solely by iteration value; newline bytes retained')
    route = (HERE / 'route.tcl').read_text(); commands = [line.strip().split()[0] for line in route.splitlines() if line.strip()]
    assert commands.count('global_route') == commands.count('write_global_route_segments') == 1
    assert route.index('global_route -') < route.index('write_global_route_segments') < route.index('write_guide') < route.index('write_db')
    assert not set(commands) & {'detailed_placement', 'global_placement', 'clock_tree_synthesis', 'repair_timing', 'repair_design', 'insert_buffer', 'set_global_routing_layer_adjustment'}
    results.append('one nativeGRT, postGRT segments/guide/ODB, no physical optimization or manual NDR waiver')
    for path in HERE.glob('*.py'): ast.parse(path.read_text())
    controls = {'schema': 'pinwheel-route-effort-host-controls-v1', 'status': 'passed', 'CAD_launched': False, 'controls_passed': len(results), 'controls': results,
        'source_sha256': {str(path.relative_to(ROOT)): sha(path) for path in HERE.iterdir() if path.is_file()}, 'host_elapsed_seconds': round(time.monotonic()-started, 3)}
    (HERE / 'host-controls.json').write_text(json.dumps(controls, indent=2) + '\n')
    intake_path = ROOT / 'build/physical/tt-buffered-route-effort-intake-01/report.json'; intake = json.loads(intake_path.read_text())
    assert intake['status'] == 'passed' and intake['schema'] == 'pinwheel-buffered-tt-route-effort-intake-v1'
    assert intake['source_checkpoint']['database_sha256'] == '95f0fdb260de137d5b4f77669c9aaa5eb3bf56e7dc55f4c9b7d51b2b8a16556e'
    derivation = json.loads((HERE / 'derivation.json').read_text())
    for name, digest in derivation['source_sha256'].items(): assert sha(ROOT/name) == digest
    tools = {str(path.relative_to(HERE)): sha(path) for path in sorted(HERE.iterdir()) if path.is_file()}
    prepared = {'schema': 'pinwheel-buffered-tt-route-effort-tools-v1', 'status': 'prepared_not_launched',
        'tool_sha256': tools, 'derivation_sha256': derivation['source_sha256'], 'intake': {'path': str(intake_path.relative_to(ROOT)), 'sha256': sha(intake_path)},
        'source_database_sha256': intake['source_checkpoint']['database_sha256'], 'allowed_arms': {'control': 5, 'probe': 10}, 'all_in_cap_seconds_per_arm': 230,
        'native_work_cap_seconds_per_arm': 175, 'cleanup_reserve_seconds': 50, 'host_staging_reserve_seconds': 5, 'cpus': 4, 'memory': '3g', 'network': 'none',
        'all_instances_fixed_by_invariant': True, 'post_GRT_CLOCK_NDR_association_response_recorded': True, 'segments_export_required': True,
        'host_controls_sha256': sha(HERE/'host-controls.json'), 'controls_passed': len(results), 'boundary': 'Tools only; root owns both CAD launches. Exact original95f0 both arms, one variable5/10 iterations. Initial definitions/associations, Metal2–4 resources, libs/SDC and source geometry frozen. Native automatic CLOCK NDR response recorded, not masked. No accepted routing/timing/signoff claim.'}
    (HERE / 'prepared.json').write_text(json.dumps(prepared, indent=2) + '\n')
    print(json.dumps({'prepared_sha256': sha(HERE/'prepared.json'), 'controls_passed': len(results), 'host_elapsed_seconds': round(time.monotonic()-started, 3), 'CAD_launched': False}))


if __name__ == '__main__': main()
