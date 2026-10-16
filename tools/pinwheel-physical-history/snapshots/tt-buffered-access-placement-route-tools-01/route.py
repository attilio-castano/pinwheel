"""Single immutable diagnostic route for either arm of one SRAM access comparison."""
import argparse
import math
from pathlib import Path
import shutil
import sys
import time
from common import ROOT, execute, read, resolve_view, sha, write
from checkpoint_admission import validate

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--state', type=Path, required=True)
parser.add_argument('--design', type=Path, required=True)
parser.add_argument('--tag', required=True)
parser.add_argument('--arm', choices=['control', 'candidate'], required=True)
parser.add_argument('--selection', type=Path, required=True)
parser.add_argument('--work-seconds', type=int, required=True)
parser.add_argument('--container-design-root', choices=['/work/core','/work/recovery'], required=True)
parser.add_argument('--checkpoint-admission', type=Path)
args = parser.parse_args()
started = time.monotonic()
assert 1 <= args.work_seconds <= 180
assert Path(args.tag).name == args.tag and args.tag not in ('.', '..')
assert args.state.resolve().is_relative_to(args.design.resolve())
tools = Path(__file__).resolve().parent
prepared = read(tools / 'prepared.json')
for path, expected in prepared['tool_sha256'].items():
    assert sha(tools / path) == expected, path
state = read(args.state)
prefix=args.container_design_root+'/'
assert state['odb'].startswith(prefix)
relative=Path(state['odb'][len(prefix):]);assert not relative.is_absolute() and '..' not in relative.parts
database=(args.design/relative).resolve();assert database.is_relative_to(args.design.resolve()) and database.is_file()
expected_database = sha(database)
prior = ROOT / 'build/physical/tt-buffered-congestion-map-01'
intake = ROOT / 'build/physical/tt-buffered-access-placement-intake-01/report.json'
intake_data = read(intake)
assert args.selection.resolve().is_relative_to(ROOT / 'physical/experiments')
selection = read(args.selection)
assert sha(intake) == selection['references']['intake']['sha256']
assert sha(tools / 'prepared.json') == selection['references']['route_tools']['sha256']
for key in ('previous_mirrored_source_sha256', 'previous_mirrored_evidence_sha256',
            'older_evidence_sha256', 'protected_sources_sha256', 'references_sha256'):
    for path, expected in intake_data[key].items():
        assert sha(Path(path) if Path(path).is_absolute() else ROOT / path) == expected, path
core = read(args.design / 'core.json')
assert core['MACROS']['RM_IHPSG13_1P_64x64_c2_bm_bist']['instances'] == {
    'engine.memory.storage0': {'location': [252, 30], 'orientation': 'N'},
    'engine.memory.storage1': {'location': [252, 144], 'orientation': 'N'}}
admitted_paths, admission = {}, {}
if args.arm == 'control':
    reference = intake_data['matched_repaired_control']
    assert args.state.resolve() == (ROOT / reference['state']).resolve()
    assert expected_database == reference['database_sha256']
else:
    assert args.checkpoint_admission is not None, 'Candidate needs exact completed-checkpoint admission'
    admitted_paths, admission = validate(args.design, args.state, args.checkpoint_admission)
prior_invocation = read(prior / 'invocation.json')
for name in ['baseline-env.tcl', 'corner-env.tcl', 'core.sdc'] + [str(p.relative_to(prior)) for p in sorted((prior / 'lib').glob('*.lib'))]:
    assert sha(prior / name) == prior_invocation['artifacts_sha256'][name], name
assert sha(args.design / 'core.sdc') == sha(prior / 'core.sdc')
assert state['metrics']['timing__setup__ws__corner:nom_typ_1p20V_25C'] is not None
out = ROOT / 'build/physical' / args.tag
out.mkdir()
paths = [database, args.state.resolve(), args.design / 'core.sdc', args.design / 'core.json',
         intake, args.selection.resolve(), tools / 'prepared.json', ROOT / 'tools/physical-toolchain.json',
         ROOT / 'scripts/run-buffered-tt-physical.py', ROOT / 'build/physical/pdk/installed.json']
paths += [Path(name) for name in admitted_paths]
if args.checkpoint_admission is not None:
    paths += [args.checkpoint_admission, tools / 'checkpoint_admission.py']
for source, target in [(database, 'postcts.odb'), (args.design / 'core.sdc', 'core.sdc'),
                       (args.state, 'source-state.json'), (args.design / 'core.json', 'source-config.json'),
                       (prior / 'baseline-env.tcl', 'baseline-env.tcl'),
                       (prior / 'corner-env.tcl', 'corner-env.tcl')]:
    shutil.copyfile(source, out / target)
    assert sha(source) == sha(out / target)
    paths += [source.resolve(), out / target]
with (out/'corner-env.tcl').open('a') as file:file.write('set ::env(GRT_OVERFLOW_ITERS) 5\n')
for source in sorted((prior / 'lib').glob('*.lib')):
    target = out / 'lib' / source.name
    target.parent.mkdir(exist_ok=True)
    shutil.copyfile(source, target)
    assert sha(source) == sha(target)
    paths += [source.resolve(), target]
for name in ['route.tcl', 'coordinator.py', 'export_geometry.py']:
    shutil.copyfile(tools / name, out / name)
    paths += [tools / name, out / name]
paths += [Path(__file__).resolve(), tools / 'common.py', tools / 'checkpoint_admission.py']
all_in_cap = args.work_seconds + 50
work_bound = min(args.work_seconds, math.floor(all_in_cap - (time.monotonic() - started) - 50))
assert work_bound > 0
report = execute(out, paths, ['python3', '-B', '/work/diagnostic/coordinator.py'],
    seconds=work_bound, cpus=4, memory='3g', schema='pinwheel-buffered-tt-access-placement-route-v1',
    scope='Matched coarse5-iteration-per-segment native congestion-allowed route of a source-bound accepted postCTS ODB. Same libraries/SDC/capacity settings as retained2255 replay;5 iterations is not equivalent to the50-iteration benchmark. Normal native clock-NDR fallback retained; no resizing or routing acceptance.',
    extra={**admission, 'arm': args.arm, 'source_database': str(database.relative_to(ROOT)),
           'source_database_sha256': expected_database, 'source_state': str(args.state.resolve().relative_to(ROOT)),
           'older_reference_overflow': 2255, 'native_extra_iterations':5, 'container_design_root':args.container_design_root, 'native_fallback_policy': 'unchanged native automatic retries'},
    expected_hashes={database: expected_database, out / 'postcts.odb': expected_database, args.selection.resolve(): sha(args.selection)})
report['invocation_elapsed_seconds'] = round(time.monotonic() - started, 3)
report['invocation_elapsed_scope'] = 'Host staging, Docker execution and owned cleanup/rehash. Selected Docker cap; canonical owned cleanup may take50s outside subprocess cap, total charged to shared comparison allocation.'
report['overall_budget_seconds'] = args.work_seconds + 50
report['accepted_route'] = False
if report['invocation_elapsed_seconds'] > all_in_cap:
    report['status'] = 'bound_exceeded'
write(out / 'report.json', report)
print(out / 'report.json', flush=True)
sys.exit(0 if report['status'] == 'passed' else 1)
