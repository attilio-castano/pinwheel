"""Single-use source-bound 5/10 original-R0 routing diagnostic; root owns CAD launch."""
import argparse
import math
from pathlib import Path
import re
import shutil
import sys
import time
from common import ROOT, execute, read, sha, write

SOURCE = '95f0fdb260de137d5b4f77669c9aaa5eb3bf56e7dc55f4c9b7d51b2b8a16556e'
TOOLS = Path(__file__).resolve().parent


def hashes(values, base=ROOT):
    for name, digest in values.items():
        path = Path(name)
        assert sha(path if path.is_absolute() else base / path) == digest, name


def iterations_for(selection, arm):
    assert selection['schema'] == 'pinwheel-buffered-tt-route-effort-selection-v1'
    assert selection['routing_effort'] == {'control_iterations': 5, 'probe_iterations': 10}
    assert arm in ('control', 'probe')
    return selection['routing_effort'][arm + '_iterations']


def corner_environment(text, iterations):
    pattern = r'^(set ::env\(GRT_OVERFLOW_ITERS\) )(\d+)([ \t]*)$'
    assert [m[1] for m in re.findall(pattern, text, re.M)] == ['5']
    result = re.sub(pattern, lambda m: m[1] + str(iterations) + m[3], text, flags=re.M)
    # Restoring the sole value must recover the byte-exact retained environment.
    assert re.sub(pattern, lambda m: m[1] + '5' + m[3], result, flags=re.M) == text
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--selection', type=Path, required=True)
    parser.add_argument('--arm', choices=('control', 'probe'), required=True)
    parser.add_argument('--tag', required=True)
    args = parser.parse_args(); started = time.monotonic()
    assert re.fullmatch(r'tt-buffered-route-effort-[A-Za-z0-9_-]+', args.tag)
    prepared = read(TOOLS / 'prepared.json')
    hashes(prepared['tool_sha256'], TOOLS)
    hashes(prepared['derivation_sha256'])
    selection = read(args.selection); iterations = iterations_for(selection, args.arm)
    for key, path in [('intake', ROOT / prepared['intake']['path']), ('routing_tools', TOOLS / 'prepared.json')]:
        entry = selection['references'][key]
        assert (ROOT / entry['path']).resolve() == path.resolve() and entry['sha256'] == sha(path)
    for entry in selection['references'].values(): assert sha(ROOT / entry['path']) == entry['sha256']
    intake_path = ROOT / prepared['intake']['path']; intake = read(intake_path)
    assert sha(intake_path) == prepared['intake']['sha256']
    assert intake['schema'] == 'pinwheel-buffered-tt-route-effort-intake-v1' and intake['status'] == 'passed'
    hashes(intake['custody_sha256'])
    for key in ('protected_sources_sha256', 'prior_current_source_sha256', 'references_sha256', 'original_checkpoint_views_sha256', 'original_recipe_sha256'):
        hashes(intake[key])
    for name, prior in intake['prior_manifests'].items():
        assert sha(ROOT / name) == prior['sha256']; hashes(prior['evidence_sha256'])
    reference = intake['source_checkpoint']; recipe = ROOT / reference['design']
    database, state, env = [ROOT / reference[key] for key in ('database', 'state', 'environment')]
    assert sha(database) == reference['database_sha256'] == SOURCE
    assert sha(state) == reference['state_sha256'] and sha(env) == reference['environment_sha256']
    source = read(state); producer = read(recipe / 'continuation-invocation.json')
    assert producer['status'] == 'failed' and producer['exit_code'] == 2
    assert source['metrics']['design__power_grid_violation__count'] == 30396
    assert source['metrics']['design__power_grid_violation__count__net:VGND'] == 10392
    assert source['metrics']['design__power_grid_violation__count__net:VPWR'] == 20004
    assert re.findall(r'^set ::env\(CURRENT_ODB\) (\S+)\s*$', env.read_text(), re.M) == [source['odb']]
    out = ROOT / 'build/physical' / args.tag; out.mkdir()
    paths = [database, state, env, intake_path, args.selection, TOOLS / 'prepared.json',
        *[TOOLS / name for name in prepared['tool_sha256']], recipe / 'core.json', recipe / 'core.sdc',
        recipe / 'continuation-invocation.json', ROOT / 'scripts/run-buffered-tt-physical.py',
        ROOT / 'tools/physical-toolchain.json', ROOT / 'build/physical/pdk/installed.json',
        *[Path(name) for name in intake['protected_sources_sha256']]]
    expected = {str(database.resolve()): SOURCE}

    def copy(path, name):
        target = out / name; target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(path, target); assert sha(path) == sha(target)
        paths.extend((path, target)); expected[str(target.resolve())] = sha(path)
        return target

    prior = ROOT / 'build/physical/tt-buffered-access-incremental-control-route-01'
    receipt = read(prior / 'report.json')
    assert receipt['status'] == 'passed' and receipt['source_database_sha256'] == SOURCE and receipt['native_extra_iterations'] == 5
    paths.append(prior / 'report.json')
    for name in ('baseline-env.tcl', 'core.sdc'):
        assert sha(prior / name) == receipt['artifact_sha256'][name]; copy(prior / name, name)
    assert sha(recipe / 'core.sdc') == sha(prior / 'core.sdc')
    assert sha(prior / 'corner-env.tcl') == receipt['artifact_sha256']['corner-env.tcl']
    corner = out / 'corner-env.tcl'; corner.write_text(corner_environment((prior / 'corner-env.tcl').read_text(), iterations))
    paths.extend((prior / 'corner-env.tcl', corner)); expected[str(corner.resolve())] = sha(corner)
    for path in sorted((prior / 'lib').glob('*.lib')):
        name = str(path.relative_to(prior)); assert sha(path) == receipt['artifact_sha256'][name]; copy(path, name)
    assert len(list((out / 'lib').glob('*.lib'))) == 3
    copy(database, 'postcts.odb'); copy(state, 'source-state.json'); copy(recipe / 'core.json', 'source-config.json')
    for name in ('route.tcl', 'export_geometry.py', 'native_inventory.py', 'route_checks.py'): copy(TOOLS / name, name)
    copy(TOOLS / 'route-coordinator.py', 'coordinator.py')
    parameters = {'schema': 'pinwheel-route-effort-parameters-v1', 'arm': args.arm,
        'native_iterations_per_segment': iterations, 'source_database_sha256': SOURCE,
        'cpus': 4, 'memory': '3g', 'network': 'none', 'only_treatment': 'GRT_OVERFLOW_ITERS',
        'initial_NDR_rules_and_associations_frozen': True, 'native_automatic_NDR_fallback': True}
    write(out / 'parameters.json', parameters); paths.append(out / 'parameters.json')
    stage = time.monotonic() - started; assert stage <= 5, ('Staging exceeded reserve', stage)
    work = min(175, math.floor(230 - stage - 50)); assert work > 0
    report = execute(out, paths, ['python3', '-B', '/work/diagnostic/coordinator.py'], seconds=work, cpus=4, memory='3g',
        schema='pinwheel-buffered-tt-route-effort-route-v1',
        scope='Matched original95f0 routing-only diagnostic; sole 5/10 per-segment iteration variable, all placements/topology/PG/pins/technology/rule definitions frozen. Native CLOCK NDR association response recorded. No accepted route or signoff.',
        expected_hashes=expected,
        extra={'network': 'none', 'arm': args.arm, 'source_database': str(database.relative_to(ROOT)), 'source_database_sha256': SOURCE,
            'source_state': str(state.relative_to(ROOT)), 'source_state_sha256': sha(state), 'reference_database_sha256': SOURCE,
            'selection_sha256': sha(args.selection), 'native_extra_iterations': iterations, 'accepted_route': False,
            'initial_NDR_rules_and_associations_frozen': True, 'post_GRT_CLOCK_NDR_response_allowed_and_recorded': True,
            'native_fallback_policy': 'Unchanged native automatic clock-NDR retries; each segment uses selected iteration limit',
            'route_segments_required': True, 'source_reference_native_flow_status': 'failed', 'source_reference_native_flow_exit_code': 2,
            'source_reference_inherited_power_count': 30396, 'fresh_native_checks_waived': False})
    if report['status'] == 'passed':
        assert report['measurement']['native_iterations_per_segment'] == iterations
        assert report['measurement']['native_frozen_inventory']['all_frozen_native_invariants_passed']
        assert report['measurement']['route_segments']['sha256'] == report['artifact_sha256']['after_grt.segments']
    report['all_in_elapsed_seconds'] = round(time.monotonic() - started, 3)
    report['host_staging_seconds'] = round(stage, 3); report['overall_bound_seconds'] = 230
    report['all_in_scope'] = 'Source staging<=5s, native work<=175s, owned cleanup<=50s, source recustody and artifact hashes; final receipt write/print excluded.'
    if report['all_in_elapsed_seconds'] > 230: report['status'] = 'bound_exceeded'
    write(out / 'report.json', report); print(out / 'report.json', flush=True)
    return 0 if report['status'] == 'passed' else 1


if __name__ == '__main__': raise SystemExit(main())
