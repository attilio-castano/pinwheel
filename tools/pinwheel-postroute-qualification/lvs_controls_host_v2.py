#!/usr/bin/env python3
"""Stage copied-input native LVS sensitivity controls; --run is root-only."""
import argparse
import importlib.util
import json
from pathlib import Path
import shutil
import sys

from audits import sha, write
from lvs_mutants_v2 import native_verdict, reference_faults

HERE = Path(__file__).resolve().parent


def stage(positive, out):
    positive, out = Path(positive).resolve(), Path(out).resolve()
    assert not out.exists(), 'Immutable controls destination already exists'
    receipt = json.loads((positive / 'report.json').read_text())
    measured = json.loads((positive / 'measurement.json').read_text())
    prepared = json.loads((positive / 'prepared.json').read_text())
    assert receipt['status'] == 'passed' and receipt['inputs_unchanged'] is True
    assert receipt['container_termination']['status'] == 'absent' and receipt['within_absolute_and_job_deadlines']
    assert measured['status'] == 'measured' and measured['phase'] in ('lef-lvs', 'gds-lvs')
    assert receipt['image_id'] == prepared['image_id']
    assert native_verdict((positive / 'netgen-lvs/reports/lvs.netgen.rpt').read_text())['match_uniquely']
    for relative, digest in receipt['artifact_sha256'].items():
        assert sha(positive / relative) == digest, 'Changed completed positive artifact: ' + relative
    prefix = '/work/diagnostic/'
    reference = Path(measured['views']['pnl'])
    assert str(reference).startswith(prefix)
    source_reference = positive / reference.relative_to('/work/diagnostic')
    assert source_reference.resolve().is_relative_to(positive)
    assert sha(source_reference) == measured['view_sha256']['pnl']
    inventory = json.loads((positive / 'input/inventory.json').read_text())
    mutants, detail = reference_faults(source_reference.read_text(), inventory)
    out.mkdir(parents=True)
    shutil.copytree(positive, out / 'positive')
    shutil.copyfile(positive / 'campaign_runner.py', out / 'campaign_runner.py')
    helpers = ['lvs_controls_host_v2.py', 'lvs_controls_native_v2.py', 'lvs_mutants_v2.py', 'lvs_execute_staged_v2.py', 'audits.py']
    for name in helpers:
        shutil.copyfile(HERE / name, out / name)
    for case, text in mutants.items():
        target = out / 'controls' / case
        target.mkdir(parents=True)
        (target / 'reference.v').write_text(text)
    source_script = (positive / 'netgen-lvs/lvs_script.lvs').read_text()
    copied_reference = str(reference).replace(prefix, prefix + 'positive/')
    copied_report = '/work/diagnostic/positive/netgen-lvs/reports/lvs.netgen.rpt'
    for case in mutants:
        target = out / 'controls' / case
        script = source_script.replace(prefix, prefix + 'positive/')
        assert script.count('readnet verilog ' + copied_reference) == 1
        assert copied_report in script
        script = script.replace(copied_reference, '/work/diagnostic/controls/' + case + '/reference.v')
        script = script.replace(copied_report, '/work/diagnostic/controls/' + case + '/lvs.rpt')
        (target / 'run.lvs').write_text(script)
    assert sha(out / 'controls/positive/reference.v') == sha(source_reference)
    sources = dict(prepared['source_sha256'])
    sources.update({str(positive / 'report.json'): sha(positive / 'report.json')})
    sources.update({str(positive / relative): digest for relative, digest in receipt['artifact_sha256'].items()})
    config = {'schema': 'pinwheel-native-LVS-sensitivity-controls-v2',
        'positive_root': str(positive), 'positive_receipt_sha256': sha(positive / 'report.json'),
        'prepared': prepared, 'source_sha256': sources,
        'source_reference_sha256': sha(source_reference),
        'cases': {case: {'reference_sha256': sha(out / 'controls' / case / 'reference.v'),
                        'script_sha256': sha(out / 'controls' / case / 'run.lvs'),
                        'expected_unique_match': case == 'positive',
                        'mutation': detail.get(case, {'changed_terminal_count': 0})} for case in mutants},
        'helpers_origin_sha256': {str(HERE / name): sha(HERE / name) for name in helpers},
        'physical_connectivity_claim': False, 'internal_SRAM_qualified': False,
        'native_negative_controls_not_yet_run': True}
    write(out / 'controls-config.json', config)
    return out


def spec(out, native_seconds=600):
    out = Path(out).resolve()
    cfg = json.loads((out / 'controls-config.json').read_text())
    p = cfg['prepared']
    loader = importlib.util.spec_from_file_location('frozen_lvs_controls_runner', out / 'campaign_runner.py')
    module = importlib.util.module_from_spec(loader)
    sys.modules[loader.name] = module
    loader.loader.exec_module(module)
    sources = dict(cfg['source_sha256'])
    sources.update({str(path): sha(path) for path in out.rglob('*') if path.is_file()})
    assert 60 <= native_seconds <= 5355
    job = module.JobSpec(output_dir=out, heavy_lock_path=Path(p['heavy_lock']), image_id=p['image_id'],
        command=['python3', '-B', '/work/diagnostic/lvs_controls_native_v2.py'], campaign_id=p['campaign_id'],
        hard_end_epoch=min(p['hard_stop_epoch'], p['native_work_stop_epoch']+45),
        input_sha256=sources, native_seconds=native_seconds, max_job_seconds=native_seconds+45,
        minimum_native_seconds=60, closeout_reserve_seconds=45, cpus=4, memory='6g',
        readonly_mounts=[(Path(p['PDK_root']), '/work/pdk')], environment={'PYTHONPATH': '/work/diagnostic'},
        scope='Native Netgen sensitivity controls on copied positive extraction/reference only; original layout and inputs immutable')
    return module, job


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--positive-root', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--native-seconds', type=int, default=600)
    parser.add_argument('--run', action='store_true', help='Root-only explicit bounded native launch')
    args = parser.parse_args()
    out = stage(args.positive_root, args.out)
    module, job = spec(out, args.native_seconds)
    if args.run:
        result = module.run_owned_job(job)
        print(json.dumps({'status': result['status'], 'receipt': str(out / 'report.json')}))
        if result['status'] != 'passed':
            raise SystemExit(1)
    else:
        print(json.dumps({'status': 'staged_only_no_CAD', 'output': str(out),
            'command': list(job.command), 'native_seconds': job.native_seconds,
            'all_in_seconds': job.max_job_seconds, 'cases': ['positive', 'removed-terminal', 'bridged-nets']}))


if __name__ == '__main__':
    main()
