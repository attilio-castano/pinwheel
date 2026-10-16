"""Single immutable diagnostic route for either arm of one SRAM access comparison."""
import argparse
from pathlib import Path
import shutil
import sys
import time
from common import ROOT, execute, read, resolve_view, sha, write

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--state', type=Path, required=True)
parser.add_argument('--design', type=Path, required=True)
parser.add_argument('--tag', required=True)
parser.add_argument('--arm', choices=['control', 'candidate'], required=True)
parser.add_argument('--selection', type=Path, required=True)
args = parser.parse_args()
started = time.monotonic()
assert Path(args.tag).name == args.tag and args.tag not in ('.', '..')
assert args.state.resolve().is_relative_to(args.design.resolve())
tools = Path(__file__).resolve().parent
prepared = read(tools / 'prepared.json')
for path, expected in prepared['tool_sha256'].items():
    assert sha(tools / path) == expected, path
state = read(args.state)
database = resolve_view(state, args.design, 'odb')
expected_database = sha(database)
prior = ROOT / 'build/physical/tt-buffered-congestion-map-01'
intake = ROOT / 'build/physical/tt-buffered-sram-access-intake-01/report.json'
intake_data = read(intake)
assert args.selection.resolve().is_relative_to(ROOT / 'physical/experiments')
selection = read(args.selection)
assert sha(intake) == selection['references']['intake']['sha256']
assert sha(tools / 'prepared.json') == selection['references']['route_tools']['sha256']
for path, expected in {**intake_data['prior_source_sha256'], **intake_data['prior_evidence_sha256']}.items():
    assert sha(ROOT / path) == expected, path
prior_invocation = read(prior / 'invocation.json')
for name in ['baseline-env.tcl', 'corner-env.tcl', 'core.sdc'] + [str(p.relative_to(prior)) for p in sorted((prior / 'lib').glob('*.lib'))]:
    assert sha(prior / name) == prior_invocation['artifacts_sha256'][name], name
assert sha(args.design / 'core.sdc') == sha(prior / 'core.sdc')
assert state['metrics']['timing__setup__ws__corner:nom_typ_1p20V_25C'] is not None
out = ROOT / 'build/physical' / args.tag
out.mkdir()
paths = [database, args.state.resolve(), args.design / 'core.sdc', args.design / 'core.json',
         intake, tools / 'prepared.json', ROOT / 'tools/physical-toolchain.json',
         ROOT / 'scripts/run-buffered-tt-physical.py', ROOT / 'build/physical/pdk/installed.json']
for source, target in [(database, 'postcts.odb'), (args.design / 'core.sdc', 'core.sdc'),
                       (args.state, 'source-state.json'), (args.design / 'core.json', 'source-config.json'),
                       (prior / 'baseline-env.tcl', 'baseline-env.tcl'),
                       (prior / 'corner-env.tcl', 'corner-env.tcl')]:
    shutil.copyfile(source, out / target)
    assert sha(source) == sha(out / target)
    paths += [source.resolve(), out / target]
for source in sorted((prior / 'lib').glob('*.lib')):
    target = out / 'lib' / source.name
    target.parent.mkdir(exist_ok=True)
    shutil.copyfile(source, target)
    assert sha(source) == sha(target)
    paths += [source.resolve(), target]
for name in ['route.tcl', 'coordinator.py', 'export_geometry.py']:
    shutil.copyfile(tools / name, out / name)
    paths += [tools / name, out / name]
paths += [Path(__file__).resolve(), tools / 'common.py']
report = execute(out, paths, ['python3', '-B', '/work/diagnostic/coordinator.py'],
    seconds=180, cpus=4, memory='3g', schema='pinwheel-buffered-tt-sram-access-route-v1',
    scope='One50-iteration native congestion-allowed route of a source-bound accepted postCTS ODB. Same script/libraries/SDC/capacity settings as retained2255 replay. No fallback retries, resizing or routing acceptance.',
    extra={'arm': args.arm, 'source_database': str(database.relative_to(ROOT)),
           'source_database_sha256': expected_database, 'source_state': str(args.state.resolve().relative_to(ROOT)),
           'older_reference_overflow': 2255, 'native_fallback_retries_allowed': 0},
    expected_hashes={database: expected_database, out / 'postcts.odb': expected_database})
report['invocation_elapsed_seconds'] = round(time.monotonic() - started, 3)
report['invocation_elapsed_scope'] = 'Host staging, Docker execution and owned cleanup/rehash. Docker180s cap; canonical owned cleanup may take50s outside subprocess cap, total charged to shared comparison allocation.'
report['overall_budget_seconds'] = 230
report['accepted_route'] = False
write(out / 'report.json', report)
print(out / 'report.json', flush=True)
sys.exit(0 if report['status'] == 'passed' else 1)
