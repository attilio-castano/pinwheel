#!/usr/bin/env python3
"""Stage or explicitly launch optional check-only antenna diagnostics."""
import argparse
import importlib.util
import json
from pathlib import Path
import shutil
import sys

from audits import sha, write

HERE = Path(__file__).resolve().parent


def stage(prepared_path, out):
    prepared_path, out = Path(prepared_path).resolve(), Path(out).resolve()
    p = json.loads(prepared_path.read_text())
    assert p['schema'] == 'pinwheel-isolated-postroute-qualification-v1'
    for relative, digest in p['staged_sha256'].items():
        assert sha(prepared_path.parent / relative) == digest
    assert not out.exists()
    shutil.copytree(prepared_path.parent, out)
    origins = {}
    for name in ['antenna_host_v2.py', 'antenna_coordinator_v2.py', 'antenna_native_v2.py']:
        shutil.copyfile(HERE / name, out / name)
        origins[str(HERE / name)] = sha(HERE / name)
    write(out / 'antenna-plan.json', {'schema': 'pinwheel-optional-check-only-antenna-v2',
        'prepared_origin': str(prepared_path), 'prepared_origin_sha256': sha(prepared_path),
        'helper_origin_sha256': origins, 'source_sha256': p['source_sha256'],
        'actual_detailed_wire_and_API_and_metadata_admission_required': True,
        'no_repairs_or_guide_wire_synthesis_allowed': True,
        'pinned_checker_source': 'https://github.com/The-OpenROAD-Project/OpenROAD/blob/dcf36133a369abc8f3c5e5738cd4d82e4903c0e0/src/ant/src/AntennaChecker.cc#L1088',
        'antenna_pass_qualified': False})
    return out


def job_spec(out, seconds=300):
    out = Path(out).resolve()
    prepared = json.loads((out / 'prepared.json').read_text())
    plan = json.loads((out / 'antenna-plan.json').read_text())
    sources = dict(plan['source_sha256'])
    sources[plan['prepared_origin']] = plan['prepared_origin_sha256']
    sources.update({str(path): sha(path) for path in out.rglob('*') if path.is_file()})
    loader = importlib.util.spec_from_file_location('frozen_check_only_antenna_runner', out / 'campaign_runner.py')
    module = importlib.util.module_from_spec(loader)
    sys.modules[loader.name] = module
    loader.loader.exec_module(module)
    assert 60 <= seconds <= 600, 'Antenna is an optional cheap bounded diagnostic'
    spec = module.JobSpec(output_dir=out, heavy_lock_path=Path(prepared['heavy_lock']),
        image_id=prepared['image_id'], command=['python3', '-B', '/work/diagnostic/antenna_coordinator_v2.py'],
        campaign_id=prepared['campaign_id'],
        hard_end_epoch=min(prepared['hard_stop_epoch'], prepared['native_work_stop_epoch']+45),
        input_sha256=sources, native_seconds=seconds, max_job_seconds=seconds+45,
        minimum_native_seconds=60, closeout_reserve_seconds=45, cpus=4, memory='6g',
        readonly_mounts=[(Path(prepared['PDK_root']), '/work/pdk')],
        environment={'PYTHONPATH': '/work/diagnostic'},
        scope='Optional check_antennas only on actual detailed wires; require exact full scope/TAPER and nonvacuous metadata coverage; no repair/insert/reroute')
    return module, spec


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--prepared', type=Path)
    parser.add_argument('--out', type=Path)
    parser.add_argument('--staged-root', type=Path)
    parser.add_argument('--native-seconds', type=int, default=300)
    parser.add_argument('--run', action='store_true', help='Root-only; requires copied staged helper')
    args = parser.parse_args()
    if args.staged_root:
        assert args.prepared is None and args.out is None
        out = args.staged_root.resolve()
        assert Path(__file__).resolve() == out / 'antenna_host_v2.py'
    else:
        assert args.prepared is not None and args.out is not None and not args.run
        out = stage(args.prepared, args.out)
    module, spec = job_spec(out, args.native_seconds)
    if args.run:
        result = module.run_owned_job(spec)
        print(json.dumps({'status': result['status'], 'receipt': str(out / 'report.json')}))
        if result['status'] != 'passed':
            raise SystemExit(1)
    else:
        print(json.dumps({'status': 'staged_only_no_CAD', 'out': str(out),
            'root_only_run_argv': ['python3', '-B', str(out / 'antenna_host_v2.py'), '--staged-root', str(out),
                                  '--native-seconds', str(args.native_seconds), '--run']}))


if __name__ == '__main__':
    main()
