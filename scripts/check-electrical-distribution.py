#!/usr/bin/env python3
"""Bounded fanout repair probe of the retained combined chip, without routing.

Keep the exact mapped logic, registers, SRAM terminals and clock connectivity.
Insert noninverting distribution buffers, then independently read back, prove
the complete controller transition, and measure Liberty timing and electrical
limits. This is a cost probe, not a placement-aware repair or backend promotion.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import shutil
import time

from map_distribution import BUFFER, boundary_loads, distribute
from tiled_chip import chip_metrics, macro_binding, state_cut
from validation_run import Commands, fresh_directory, sha

ROOT = Path(__file__).resolve().parents[1]
YOSYS = ROOT / 'build/tools/oss-cad-suite/bin/yosys'


def write(path, data):
    path.write_text(json.dumps(data, indent=2) + '\n')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--comparison', type=Path, required=True, help='Selected combined-chip receipt')
    parser.add_argument('--timing', type=Path, required=True, help='Passed retained timing report')
    parser.add_argument('--tag', required=True)
    args = parser.parse_args()
    out = fresh_directory(ROOT / 'build/storage/electrical-distribution', args.tag)
    started = time.monotonic()
    run = Commands(ROOT, out, default_timeout=120)
    report = dict(schema=1, status='running', commands=run.records, variants={}, containers={},
                  inputs_sha256={}, per_command_timeout_seconds=120)
    frozen = report['inputs_sha256']

    def freeze(path):
        path = Path(path).resolve()
        frozen[str(path.relative_to(ROOT)) if path.is_relative_to(ROOT) else str(path)] = sha(path)
        return path

    def yosys(label, lines, negative=False):
        script = out / (label + '.ys')
        script.write_text('\n'.join(lines) + '\n')
        return run([YOSYS, '-s', script], label,
                   reject='proof did fail' if negative else None)

    try:
        for rel in ('scripts/check-electrical-distribution.py', 'scripts/check-sram-timing.py',
                    'scripts/map_distribution.py', 'scripts/tiled_chip.py',
                    'scripts/validation_run.py', 'scripts/process_group.py', 'tools/physical-toolchain.json'):
            freeze(ROOT / rel)
        freeze(YOSYS.resolve())
        spec = importlib.util.spec_from_file_location('timing', ROOT / 'scripts/check-sram-timing.py')
        timing = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(timing)
        selected = json.loads(freeze(args.comparison).read_text())
        source_path = freeze(ROOT / selected['report'])
        if sha(source_path) != selected['report_sha256']:
            raise ValueError('Changed combined comparison')
        source = json.loads(source_path.read_text())
        if source['status'] != 'passed' or source['organization'] != 'combined':
            raise ValueError('Require a validated combined comparison')
        time_path = freeze(args.timing)
        prior_timing = json.loads(time_path.read_text())
        if prior_timing['status'] != 'passed' or prior_timing['inputs_sha256'][str(source_path.relative_to(ROOT))] != sha(source_path):
            raise ValueError('Timing comparison does not cover the retained mapping')
        report['comparison'] = str(source_path.relative_to(ROOT))
        report['timing_comparison'] = str(time_path.relative_to(ROOT))
        manifest_path = freeze(source_path.parent / 'assembly.json')
        if sha(manifest_path) != source['artifacts_sha256']['assembly.json']:
            raise ValueError('Changed state manifest')
        manifest = json.loads(manifest_path.read_text())['chip']
        lock = json.loads((ROOT / 'tools/physical-toolchain.json').read_text())
        info = json.loads(run(['docker', 'image', 'inspect', lock['container_tag']], 'image-inspect'))[0]
        runtime = {k: v for k, v in info['Config'].items() if v is not None}
        if (info['Architecture'] != 'arm64' or info['Os'] != 'linux' or
                info['RootFS']['Layers'] != lock['container_rootfs_diff_ids'] or
                hashlib.sha256(json.dumps(runtime, sort_keys=True).encode()).hexdigest() != lock['container_runtime_config_sha256']):
            raise ValueError('Unpinned timing image')
        report['tool_image'] = info['Id']
        for corner, suffix in [('typical', 'typ_1p20V_25C'), ('slow', 'slow_1p08V_125C')]:
            path = freeze(source_path.parent / f'tiled-{corner}.json')
            if sha(path) != source['artifacts_sha256'][path.name]:
                raise ValueError('Changed retained mapping')
            data = json.loads(path.read_text())
            before = chip_metrics(data)
            if before != source['variants'][corner]['tiled']:
                raise ValueError('Retained metrics do not reproduce')
            lib = freeze(ROOT / f'build/tools/ihp-cmos5l/sg13cmos5l_stdcell_{suffix}.lib')
            macro = freeze(ROOT / f'build/storage/macros/RM_IHPSG13_1P_64x64_c2_bm_bist_{suffix}.lib')
            if sha(lib) != source['libraries_sha256'][corner] or sha(macro) != source['macro_views_sha256']['lib/' + macro.name]:
                raise ValueError('Changed timing library')
            text = lib.read_text()
            limit = re.findall(r'\bdefault_max_fanout\s*:\s*([0-9.]+)\s*;', text)
            load = re.findall(r'\bdefault_fanout_load\s*:\s*([0-9.]+)\s*;', text)
            if limit != ['8'] or load != ['1'] or re.search(r'\b(?:max_fanout|fanout_load)\s*:', text):
                raise ValueError('This bounded probe requires uniform library fanout eight and unit loads')
            original = data['modules']['tt_um_pinwheel']
            fixed = set(macro_binding(original))
            repaired, distribution = distribute(data, 'tt_um_pinwheel', {}, limit=8,
                fixed_cells=fixed, prefix='electrical_distribution_')
            if any(n['loads'] > 8 for n in boundary_loads(repaired['modules'], 'tt_um_pinwheel', fixed)):
                raise ValueError('Fanout distribution did not meet the budget')
            if any(repaired['modules'][n] != m for n, m in data['modules'].items() if n != 'tt_um_pinwheel'):
                raise ValueError('Library or child implementation changed')
            if macro_binding(repaired['modules']['tt_um_pinwheel']) != macro_binding(original):
                raise ValueError('SRAM terminals changed')
            folder = out / corner
            folder.mkdir()
            write(folder / 'distributed.json', repaired)
            write(folder / 'distribution.json', distribution)
            yosys(corner + '-export', [f'read_json {folder}/distributed.json',
                'hierarchy -check -top tt_um_pinwheel', 'check -assert',
                f'write_verilog -noattr -noexpr {folder}/design.v'])
            yosys(corner + '-readback', [f'read_liberty -lib {lib}', f'read_liberty -lib {macro}',
                f'read_verilog {folder}/design.v', 'hierarchy -check -top tt_um_pinwheel',
                'check -assert', f'write_json {folder}/readback.json'])
            back = json.loads((folder / 'readback.json').read_text())
            after = chip_metrics(back)
            if after != chip_metrics(repaired) or after['maximum_signal_fanout'] > 8:
                raise ValueError('Mapped Verilog read-back disagrees')
            reference, projection = state_cut(original, manifest, True, True)
            candidate, candidate_projection = state_cut(back['modules']['tt_um_pinwheel'], manifest, True, True)
            if projection != candidate_projection:
                raise ValueError('Distribution changed the state projection')
            write(folder / 'reference-cut.json', {'modules': {'reference': reference}})

            def prove(label, cut, negative=False):
                cut_path = folder / (label + '.json')
                write(cut_path, {'modules': {'candidate': cut}})
                log = yosys(corner + '-' + label, [f'read_liberty -ignore_miss_func {lib}',
                    f'read_json {folder}/reference-cut.json', f'read_json {cut_path}',
                    'miter -equiv -flatten -make_outputs reference candidate miter',
                    'hierarchy -check -top miter', 'flatten', 'opt -full',
                    'sat -verify -prove trigger 0 -set-def-inputs miter'], negative)
                if not negative and 'SAT proof finished - no model found: SUCCESS!' not in log:
                    raise ValueError('Incomplete transition equivalence proof')

            prove('proof', candidate)
            if corner == 'typical':
                negative = json.loads(json.dumps(candidate))
                name = distribution['trees'][0]['buffers'][0]['cell']
                cell = negative['cells'][name]
                if cell['type'] != BUFFER:
                    raise ValueError('Missing diagnostic buffer')
                cell['type'] = 'sg13cmos5l_inv_1'
                cell['connections']['Y'] = cell['connections'].pop('X')
                cell['port_directions']['Y'] = cell['port_directions'].pop('X')
                prove('inverted-buffer-negative', negative, negative=True)
            shutil.copyfile(lib, folder / 'cells.lib')
            shutil.copyfile(macro, folder / 'macro.lib')
            extra = timing.fetch_paths(folder / 'design.v', back['modules']['tt_um_pinwheel'],
                                       'controller.engine.r_cached_word')
            (folder / 'timing.tcl').write_text(timing.timing_script(True, extra))
            log = timing.run_sta(run, folder, info['Id'], f'pinwheel-electrical-{args.tag}-{corner}',
                                 report['containers'], corner + '-sta')
            measured = timing.parse_timing(log, require_fetch_paths=True)
            report['variants'][corner] = dict(before=before, after=after, timing_before=prior_timing['metrics']['combined'][corner],
                timing_after=measured, added_buffers=distribution['added_buffers'],
                added_area_um2=distribution['added_area_um2'], state_projection=projection,
                fanout_limit=8, library_default_fanout_load=1)
            print(corner, distribution['added_buffers'], distribution['added_area_um2'], measured, flush=True)
        if any(sha(ROOT / p) != h for p, h in frozen.items()):
            raise ValueError('Input changed during electrical probe')
        report.update(status='passed', boundary='Arbitrary-state complete-controller transition and output equivalence, exact SRAM terminals and surviving state, mapped Verilog read-back and cell/SRAM Liberty STA. No wire parasitics, placement, clock tree or routed hold repair. No backend promotion.')
    except BaseException as error:
        report.update(status='failed', error=f'{type(error).__name__}: {error}')
        raise
    finally:
        report['elapsed_seconds'] = round(time.monotonic() - started, 3)
        report['artifacts_sha256'] = {str(p.relative_to(out)): sha(p) for p in sorted(out.rglob('*'))
                                    if p.is_file() and p.name != 'report.json'}
        write(out / 'report.json', report)
        print(out / 'report.json', flush=True)


if __name__ == '__main__':
    main()
