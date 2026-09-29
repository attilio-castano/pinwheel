#!/usr/bin/env python3
"""Bounded complete-chip tile comparison, independent of placement/routing."""
import argparse
from collections import Counter
import importlib.util
import json
from pathlib import Path
import re
import time

from validation_run import Commands, fresh_directory, sha
from map_distribution import BUFFER, boundary_loads, distribute
from tiled_chip import MACRO, controller_wrapper, state_cut, project_pruned_state, chip_metrics, macro_binding
from synthesis_hierarchy import tiled_policy, check_hierarchy, check_flattening

ROOT = Path(__file__).resolve().parents[1]
CAD = ROOT / 'build/tools/oss-cad-suite/bin'
CIRCT = ROOT / 'build/tools/firtool-1.159.0/bin/circt-opt'
VIEWS = ROOT / 'build/storage/macros'


def script_module(name, file):
    spec = importlib.util.spec_from_file_location(name, ROOT / 'scripts' / file)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


map_check = script_module('map_tile_check', 'check-map-tile.py')


def write(path, data):
    path.write_text(json.dumps(data, indent=2) + '\n')


def require_unit_fanout_budget(text, limit):
    """Sink counts represent electrical fanout only for this uniform library."""
    defaults = re.findall(r'\bdefault_max_fanout\s*:\s*([0-9.]+)\s*;', text)
    loads = re.findall(r'\bdefault_fanout_load\s*:\s*([0-9.]+)\s*;', text)
    if (len(defaults) != 1 or float(defaults[0]) != limit or
            len(loads) != 1 or float(loads[0]) != 1 or
            re.search(r'\b(?:max_fanout|fanout_load)\s*:', text)):
        raise ValueError('Require the requested uniform library fanout budget and unit loads')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--tag', required=True)
    parser.add_argument('--organization', choices=('separate', 'combined'), default='separate',
                        help='Combine controller and selection logic while retaining the 32 storage tiles')
    parser.add_argument('--fanout-limit', type=int, choices=(8, 10), default=10,
                        help='Eight uses the library budget during candidate ABC mapping and aggregate distribution; ten reproduces the historical flow')
    parser.add_argument('--compare-flat', action='store_true',
                        help='Also map the identical tiled RTL flat, using the same candidate mapping and load budget (requires combined)')
    args = parser.parse_args()
    combined = args.organization == 'combined'
    if args.fanout_limit == 8 and not combined:
        parser.error('Fanout eight requires the combined boundary to account for every consumer')
    if args.compare_flat and not combined:
        parser.error('Flat comparison requires the combined organization and aggregate load accounting')
    out = fresh_directory(ROOT / 'build/storage/tiled-chip', args.tag)
    started = time.monotonic()
    run = Commands(ROOT, out, default_timeout=180)
    sources = [*sorted((ROOT / 'Pinwheel').rglob('*.lean')), ROOT / 'Pinwheel.lean', ROOT / 'lakefile.toml',
               ROOT / 'lean-toolchain', *[ROOT / 'test' / p for p in (
                   'TiledChipEmit.lean', 'MapTileEmit.lean', 'ProofAudit.lean', 'sram_chip.sv', 'chip_tb.sv',
                   'sram_core_tb.sv', 'test_tiled_chip.py', 'test_map_distribution.py', 'test_map_tile.py',
                   'test_synthesis_hierarchy.py')],
               *[ROOT / 'scripts' / p for p in ('check-tiled-chip.py', 'tiled_chip.py', 'check-map-tile.py',
                   'map_distribution.py', 'synthesis_hierarchy.py', 'mapped_physical.py',
                   'validation_run.py', 'process_group.py')],
               *[ROOT / 'tools' / p for p in ('technology-library.json', 'storage-macros.json')]]
    report = {'schema': 1, 'status': 'running', 'commands': run.records, 'variants': {},
              'per_command_timeout_seconds': 180, 'organization': args.organization,
              'candidate_fanout_limit': args.fanout_limit, 'compare_flat': args.compare_flat,
              'hierarchy': {}}
    def yosys(label, lines):
        return map_check.yosys_command(run, out, label, lines)
    try:
        selected_path = ROOT / 'physical/experiments/sram-assembly-results.json'
        selected = json.loads(selected_path.read_text())
        original = ROOT / selected['source_comparison']
        original_report = original / 'report.json'
        if sha(original_report) != selected['source_comparison_report_sha256']:
            raise ValueError('Changed original complete-chip comparison')
        prior = json.loads(original_report.read_text())
        vector_paths = [original / name for name in prior['vectors_sha256']]
        for path in vector_paths:
            if sha(path) != prior['vectors_sha256'][path.name]:
                raise ValueError('Changed independent pin vectors')
        compile_record = next(c for c in prior['commands'] if c['label'] == 'hybrid-typical-gates-compile')
        cell_models = []
        for name, digest in prior['compatibility']['cell_models_sha256'].items():
            matches = [Path(arg) for arg in compile_record['argv'] if Path(arg).name == Path(name).name]
            if len(matches) != 1 or sha(matches[0]) != digest:
                raise ValueError('Changed physical cell simulation model')
            cell_models.extend(matches)
        sources += [selected_path, original_report, *vector_paths, *cell_models]
        map_selected_path = ROOT / 'physical/experiments/map-tile-results.json'
        map_selected = json.loads(map_selected_path.read_text())
        original_map_report = ROOT / map_selected['report']
        if sha(original_map_report) != map_selected['report_sha256']:
            raise ValueError('Changed original map comparison')
        original_map = original_map_report.parent
        map_receipt = json.loads(original_map_report.read_text())
        original_map_inputs = [original_map / name for name in ('tile.mlir', 'glue.mlir', 'flat.mlir', 'manifest.json')]
        for path in original_map_inputs:
            if sha(path) != map_receipt['artifacts_sha256'][path.name]:
                raise ValueError('Changed original map artifact: ' + path.name)
        sources += [map_selected_path, original_map_report, *original_map_inputs]
        if combined:
            previous_selected_path = ROOT / 'physical/experiments/tiled-chip-results.json'
            previous_selected = json.loads(previous_selected_path.read_text())
            previous_path = ROOT / previous_selected['report']
            if sha(previous_path) != previous_selected['report_sha256']:
                raise ValueError('Changed separated chip comparison')
            previous = json.loads(previous_path.read_text())
            if previous['status'] != 'passed':
                raise ValueError('Require a functionally validated separated chip')
            report['previous_comparison'] = {'report': str(previous_path.relative_to(ROOT)),
                'report_sha256': sha(previous_path), 'variants': {}}
            sources += [previous_selected_path, previous_path]
            for corner in ('typical', 'slow'):
                previous_map = previous_path.parent / f'tiled-{corner}.json'
                if sha(previous_map) != previous['artifacts_sha256'][previous_map.name]:
                    raise ValueError('Changed separated chip mapped artifact')
                metrics = chip_metrics(json.loads(previous_map.read_text()))
                if metrics != previous['variants'][corner]['tiled']:
                    raise ValueError('Separated chip metrics do not reproduce')
                report['previous_comparison']['variants'][corner] = metrics
                sources.append(previous_map)
        frozen = {str(p.relative_to(ROOT)) if p.is_relative_to(ROOT) else str(p): sha(p) for p in sources}
        report['inputs_sha256'] = frozen
        report['pin_oracle_source'] = {'report': str(original_report.relative_to(ROOT)), 'sha256': sha(original_report),
                                       'vectors_sha256': prior['vectors_sha256'], 'coverage': prior['coverage'],
                                       'cell_models_sha256': {str(p): sha(p) for p in cell_models}}
        report['tools_sha256'] = {str(p.relative_to(ROOT)): sha(p.resolve())
                                  for p in (CIRCT, CAD / 'yosys', CAD / 'yosys-abc', CAD / 'iverilog', CAD / 'vvp')}
        libraries = map_check.pinned_libraries()
        if args.fanout_limit == 8:
            for library in libraries.values():
                require_unit_fanout_budget(library.read_text(), args.fanout_limit)
            report['library_default_fanout_load'] = 1
        report['libraries_sha256'] = {k: sha(v) for k, v in libraries.items()}
        frozen.update({str(p.relative_to(ROOT)): sha(p) for p in libraries.values()})
        lock = json.loads((ROOT / 'tools/storage-macros.json').read_text())
        for rel, digest in lock['files_sha256'].items():
            if sha(VIEWS / Path(rel).name) != digest:
                raise ValueError('Changed macro view: ' + rel)
            frozen[str((VIEWS / Path(rel).name).relative_to(ROOT))] = digest
        report['macro_views_sha256'] = lock['files_sha256']
        if combined and any(report[k] != previous[k] for k in (
                'tools_sha256', 'libraries_sha256', 'macro_views_sha256')):
            raise ValueError('Combined comparison requires unchanged tools and libraries')
        run(['lake', 'build', 'Pinwheel', 'tiled_chip_emit', 'map_tile_emit'], 'build')
        run(['lake', 'env', 'lean', '-DwarningAsError=true', 'test/ProofAudit.lean'], 'axioms')
        run([ROOT / '.lake/build/bin/tiled_chip_emit', out], 'emit-chip')
        run([ROOT / '.lake/build/bin/map_tile_emit', out / 'map'], 'emit-map')
        manifest = json.loads((out / 'assembly.json').read_text())
        map_manifest = json.loads((out / 'map/manifest.json').read_text())
        map_check.validate_manifest(map_manifest)
        (out / 'map/tiled.sv').write_text(map_check.wrapper(map_manifest))
        for name in ('chip-logic', 'core-logic', 'baseline-chip', 'baseline-core', 'map/tile', 'map/glue'):
            text = run([CIRCT, out / (name + '.mlir'), '--canonicalize', '--lower-seq-to-sv',
                        '--lower-hw-to-sv', '--hw-legalize-modules', '--export-verilog', '-o', '/dev/null'], name.replace('/', '-') + '-export')
            (out / (name + '.sv')).write_text(text)
        for part in ('chip', 'core'):
            (out / (part + '-wrapper.sv')).write_text(controller_wrapper(part, manifest[part], map_manifest))
        for part in ('chip', 'core'):
            if sha(out / f'baseline-{part}.mlir') != sha(original / f'hybrid-{part}.mlir') or sha(out / f'baseline-{part}.sv') != sha(original / f'hybrid/{part}.sv'):
                raise ValueError('Original production controller emission changed')
        for name in ('tile.mlir', 'glue.mlir', 'flat.mlir', 'manifest.json'):
            if sha(out / 'map' / name) != sha(original_map / name):
                raise ValueError('Shared map extraction changed original emission: ' + name)
        if combined:
            for name in ('assembly.json', 'chip-logic.mlir', 'core-logic.mlir',
                         'chip-logic.sv', 'core-logic.sv', 'chip-wrapper.sv', 'core-wrapper.sv'):
                if sha(out / name) != previous['artifacts_sha256'][name]:
                    raise ValueError('Combined comparison changed emitted circuit: ' + name)
            report['unchanged_tiled_rtl_and_projection'] = True
        report['unchanged_emissions'] = {'production_hybrid_chip_and_core': True, 'original_map': True}
        files = {part: [out / f'{part}-logic.sv', out / f'{part}-wrapper.sv',
                        *[out / 'map' / (p + '.sv') for p in ('tiled', 'tile', 'glue')]] for part in ('chip', 'core')}
        wrapper = ROOT / 'test/sram_chip.sv'
        variants = ('baseline', 'tiled', 'tiled-flat') if args.compare_flat else ('baseline', 'tiled')
        policies = {variant: tiled_policy(variant, args.organization, map_manifest) for variant in variants}
        report['hierarchy_policies'] = {name: policy.describe() for name, policy in policies.items()}
        if args.compare_flat:
            report['matched_hierarchy_inputs'] = {
                'variants': ['tiled', 'tiled-flat'],
                'rtl_sha256': {str(p.relative_to(ROOT)): sha(p) for p in [*files['chip'], wrapper]},
                'candidate_fanout_limit': args.fanout_limit,
                'changed_factor': 'Retain storage tiles through mapping versus flatten before mapping.',
                'controls': 'Identical RTL, tools, corner libraries, macro views, ABC recipe and aggregate sink budget. '
                            'Distribution accounts for the resulting hierarchy in each variant.',
                'scope': 'Mapped cell cost, depth and load comparison with functional checks; no physical timing or placement.'}
        top = {'chip': 'pinwheel_sram_controller', 'core': 'pinwheel_sram_core_controller'}
        reference_cuts = {}
        report['state_projections'] = {}

        def prove(data, part, label, package=False, lib=None, negative=False, expected_pruned=None, invert_buffer=None):
            module = data['modules']['tt_um_pinwheel' if package else top[part]]
            cut, projection = state_cut(module, manifest[part], True, package)
            expected = report['state_projections'][part]['pruned_state_positions'] if expected_pruned is None else expected_pruned
            original_cut = json.loads(reference_cuts[part].read_text())['modules']['reference']
            reference = project_pruned_state(original_cut, cut, projection, expected)
            projected_reference = out / (label + '-reference-cut.json')
            write(projected_reference, {'modules': {'reference': reference}})
            if negative:
                # A real external SRAM-address mutation, including its JSON binding.
                cut['ports']['mem_addr1']['bits'] = cut['ports']['mem_addr0']['bits']
                cut['netnames']['mem_addr1'] = {'bits': cut['ports']['mem_addr0']['bits'], 'hide_name': 0, 'attributes': {}}
            if invert_buffer:
                cell = cut['cells'][invert_buffer]
                if cell['type'] != BUFFER:
                    raise ValueError('Expected a mapped distribution buffer')
                cell['type'] = 'sg13cmos5l_inv_1'
                cell['connections']['Y'] = cell['connections'].pop('X')
                cell['port_directions']['Y'] = cell['port_directions'].pop('X')
            write(out / (label + '-cut.json'), {'modules': {'candidate': cut}})
            lines = ([f'read_liberty -ignore_miss_func {lib}'] if lib else []) + [
                f'read_json {projected_reference}', f'read_json {out}/{label}-cut.json',
                'miter -equiv -flatten -make_outputs reference candidate miter',
                'hierarchy -check -top miter', 'flatten', 'opt -full',
                'sat -verify -prove trigger 0 -set-def-inputs miter']
            result = map_check.yosys_command(run, out, label, lines,
                                             reject='proof did fail' if negative or invert_buffer else None)
            if not (negative or invert_buffer) and 'SAT proof finished - no model found: SUCCESS!' not in result:
                raise ValueError('Incomplete whole-controller SAT check')
            return projection

        for part in ('core', 'chip'):
            ref = out / (part + '-reference-generic.json')
            yosys(part + '-reference-generic', [f'read_verilog -sv {out}/baseline-{part}.sv',
                f'synth -top {top[part]} -flatten -noabc', 'dffunmap', 'clean', 'check -assert', f'write_json {ref}'])
            data = json.loads(ref.read_text())
            cut, projection = state_cut(data['modules'][top[part]], manifest[part], False)
            report['state_projections'][part] = projection
            reference_cuts[part] = out / (part + '-reference-cut.json')
            write(reference_cuts[part], {'modules': {'reference': cut}})
            path = out / (part + '-candidate-generic.json')
            yosys(part + '-candidate-generic', ['read_verilog -sv ' + ' '.join(map(str, files[part])),
                f'synth -top {top[part]} -flatten -noabc', 'dffunmap', 'clean', 'check -assert', f'write_json {path}'])
            prove(json.loads(path.read_text()), part, part + '-rtl-proof')
        prove(json.loads((out / 'core-candidate-generic.json').read_text()), 'core', 'joined-address-negative', negative=True)
        (out / 'abc.constr').write_text('set_driving_cell sg13cmos5l_buf_2\nset_load 10\n')
        if args.fanout_limit == 8:
            # The pinned Yosys constrained default, including its -D 10000
            # retiming expansion. Change only ABC's default buffer limit (ten).
            (out / 'abc-eight.script').write_text(
                'strash; &get -n; &fraig -x; &put; scorr; dc2; dretime; '
                'retime -o -D 10000; strash; &get -n; &dch -f; &nf -D 10000; '
                '&put; buffer -N 8; upsize -D 10000; dnsize -D 10000; stime -p\n')
            report['candidate_abc_script'] = 'abc-eight.script'
        for corner, library in libraries.items():
            suffix = 'typ_1p20V_25C' if corner == 'typical' else 'slow_1p08V_125C'
            macro_lib = VIEWS / f'{MACRO}_{suffix}.lib'
            comparison = {}
            for variant in variants:
                prefix = variant + '-' + corner
                candidate = variant != 'baseline'
                policy = policies[variant]
                rtl = [out / 'baseline-chip.sv'] if variant == 'baseline' else files['chip']
                mapped = out / (prefix + '-hierarchy.json')
                lines = [f'read_liberty -lib {library}', f'read_liberty -lib {macro_lib}',
                         'read_verilog -sv -DSRAM_HYBRID ' + ' '.join(map(str, rtl + [wrapper])),
                         'hierarchy -check -top tt_um_pinwheel']
                lines += policy.mapping_commands() + [
                         f'dfflibmap -liberty {library}',
                         f'abc -liberty {library} -constr {out}/abc.constr -D 10000' +
                         (f' -script {out}/abc-eight.script' if candidate and args.fanout_limit == 8 else ''),
                         'clean', 'check -assert', f'write_json {mapped}']
                yosys(prefix + '-map', lines)
                data = json.loads(mapped.read_text())
                hierarchy = {'mapped': check_hierarchy(data, policy)}
                report['hierarchy'][prefix] = hierarchy
                if candidate:
                    boundary = 'tt_um_pinwheel' if combined else 'pinwheel_map_tiled'
                    banks = {('controller.map.' if combined else '') + t['name']: (t['bank'], t['low'])
                             for t in map_manifest['tiles']} if variant == 'tiled' else {}
                    original_children = {n: m for n, m in data['modules'].items() if n != boundary}
                    fixed = ()
                    if combined:
                        fixed = set(macro_binding(data['modules'][boundary]))
                        if variant == 'tiled':
                            comparison['retained_tile'] = map_check.metrics(data['modules']['pinwheel_map_tile'],
                                data['modules'], 'tile', map_manifest)
                    loads_before = boundary_loads(data['modules'], boundary, fixed)
                    data, distribution = distribute(data, boundary, banks, args.fanout_limit, fixed_cells=fixed)
                    if any(data['modules'][n] != value for n, value in original_children.items()):
                        raise ValueError('Distribution changed a child or library')
                    if any(n['loads'] > args.fanout_limit for n in boundary_loads(data['modules'], boundary, fixed)):
                        raise ValueError('Distribution boundary still exceeds budget')
                    distribution.update(boundary=boundary, fixed_cells=sorted(fixed), child_modules_unchanged=True)
                    write(out / (prefix + '-distribution.json'), distribution)
                    comparison['distribution' if variant == 'tiled' else 'flat_distribution'] = distribution
                    loads_path = out / (prefix + '-boundary-loads.json')
                    write(loads_path, dict(boundary=boundary, before=loads_before,
                        after=boundary_loads(data['modules'], boundary, fixed),
                        scope='Actual mapped signal sink pins, including child loads; excludes clock and wire capacitance.'))
                    hierarchy['boundary_loads'] = loads_path.name
                    hierarchy['distributed'] = check_hierarchy(data, policy)
                    mapped = out / (prefix + '-buffered.json')
                    write(mapped, data)
                retained = data
                flat = out / (prefix + '.json')
                yosys(prefix + '-flatten', [f'read_json {mapped}',
                    *policy.flatten_commands(), f'write_json {flat}',
                    f'write_verilog -norename -noattr -noexpr {out}/{prefix}.v'])
                data = json.loads(flat.read_text())
                identity_path = out / (prefix + '-flatten-identity.json')
                write(identity_path, check_flattening(retained, data))
                hierarchy['flat_connection_identity'] = identity_path.name
                hierarchy['flattened'] = check_hierarchy(data, policies['baseline'])
                metrics = chip_metrics(data)
                if candidate and combined:
                    if metrics['maximum_signal_fanout'] > args.fanout_limit:
                        raise ValueError('Complete-chip fanout exceeds the aggregate budget')
                    unbuffered = json.loads((out / (prefix + '-hierarchy.json')).read_text())
                    counts = Counter()
                    def count_cells(name):
                        for cell in unbuffered['modules'][name]['cells'].values():
                            kind = cell['type']
                            if kind == '$scopeinfo':
                                continue
                            if unbuffered['modules'][kind].get('cells'):
                                count_cells(kind)
                            else:
                                counts[kind] += 1
                    count_cells('tt_um_pinwheel')
                    counts[BUFFER] += distribution['added_buffers']
                    if dict(sorted(counts.items())) != metrics['cell_types']:
                        raise ValueError('Combined distribution cell census does not reconcile')
                readback = out / (prefix + '-readback.json')
                yosys(prefix + '-readback', [f'read_liberty -lib {library}', f'read_liberty -lib {macro_lib}',
                    f'read_verilog {out}/{prefix}.v', 'hierarchy -check -top tt_um_pinwheel',
                    'check -assert', f'write_json {readback}'])
                back = json.loads(readback.read_text())
                readback_identity = out / (prefix + '-readback-identity.json')
                write(readback_identity, check_flattening(retained, back, verilog_readback=True))
                hierarchy['readback_connection_identity'] = readback_identity.name
                hierarchy['readback'] = check_hierarchy(back, policies['baseline'])
                if chip_metrics(back) != metrics:
                    raise ValueError('Independent mapped Verilog metrics disagree')
                if variant == 'baseline':
                    _, baseline_projection = state_cut(back['modules']['tt_um_pinwheel'], manifest['chip'], False, True)
                    comparison['baseline_state_projection'] = baseline_projection
                else:
                    comparison[variant + '_state_projection'] = prove(back, 'chip', prefix + '-proof', package=True, lib=library,
                        expected_pruned=comparison['baseline_state_projection']['pruned_state_positions'])
                    if variant == 'tiled' and combined and corner == 'typical':
                        prove(back, 'chip', prefix + '-inverted-buffer-negative', package=True, lib=library,
                            expected_pruned=comparison['baseline_state_projection']['pruned_state_positions'],
                            invert_buffer=distribution['trees'][0]['buffers'][0]['cell'])
                comparison[variant] = metrics
                print(prefix, json.dumps({k: v for k, v in metrics.items() if k != 'cell_types'}), flush=True)
            base, tiled = comparison['baseline'], comparison['tiled']
            comparison['standard_cell_area_change_um2'] = round(tiled['standard_cell_area_um2'] - base['standard_cell_area_um2'], 4)
            comparison['standard_cell_area_change_percent'] = round(100 * (tiled['standard_cell_area_um2'] / base['standard_cell_area_um2'] - 1), 6)
            comparison['structural_screen_passed'] = (
                tiled['standard_cell_area_um2'] <= base['standard_cell_area_um2'] and
                max(tiled['macro_address_depth'].values()) < max(base['macro_address_depth'].values()) and
                tiled['maximum_signal_fanout'] <= base['maximum_signal_fanout'])
            if args.compare_flat:
                flat = comparison['tiled-flat']
                comparison['matched_hierarchy'] = {
                    'retained_minus_flat_area_um2': round(tiled['standard_cell_area_um2'] - flat['standard_cell_area_um2'], 4),
                    'retained_minus_flat_area_percent': round(100 * (tiled['standard_cell_area_um2'] / flat['standard_cell_area_um2'] - 1), 6),
                    'retained_macro_address_depth': tiled['macro_address_depth'],
                    'flat_macro_address_depth': flat['macro_address_depth'],
                    'retained_maximum_signal_fanout': tiled['maximum_signal_fanout'],
                    'flat_maximum_signal_fanout': flat['maximum_signal_fanout'],
                    'physical_winner_established': False}
            report['variants'][corner] = comparison

        model = [VIEWS / (MACRO + '.v'), VIEWS / 'RM_IHPSG13_1P_core_behavioral_bm_bist.v']
        report['pin_oracles'] = {}
        oracle_variants = [
                ('core-rtl-oracle', 'core', files['core'], [wrapper], []),
                ('chip-rtl-oracle', 'chip', files['chip'], [wrapper], []),
                ('typical-gates-oracle', 'chip', [out / 'tiled-typical.v'], [], cell_models),
                ('slow-gates-oracle', 'chip', [out / 'tiled-slow.v'], [], cell_models)]
        if args.compare_flat:
            oracle_variants += [(corner + '-flat-gates-oracle', 'chip', [out / f'tiled-flat-{corner}.v'], [], cell_models)
                                for corner in ('typical', 'slow')]
        for label, part, rtl, bindings, cells in oracle_variants:
            tb = ROOT / 'test' / ('chip_tb.sv' if part == 'chip' else 'sram_core_tb.sv')
            top_tb = 'chip_tb' if part == 'chip' else 'sram_core_tb'
            run([CAD / 'iverilog', '-g2012', '-DFUNCTIONAL', '-DSRAM_HYBRID', '-s', top_tb,
                 '-o', out / (label + '.vvp'), *rtl, *bindings, tb, *model, *cells], label + '-compile')
            vectors = original / ('vectors.txt' if part == 'chip' else 'core-vectors.txt')
            log = run([CAD / 'vvp', out / (label + '.vvp'), '+vectors=' + str(vectors)], label)
            expected = f'Passed {prior["coverage"][part]["edges"]} independent ' + ('whole-chip' if part == 'chip' else 'SRAM core') + ' edges'
            if expected not in log:
                raise ValueError('Incomplete independent pin-oracle trace')
            report['pin_oracles'][label] = prior['coverage'][part]
        if any(sha(ROOT / p) != digest for p, digest in frozen.items()):
            raise ValueError('Source changed during whole-chip experiment')
        report.update(status='passed',
            decision='eligible-for-timing-screen',
            structural_screen_role='Historical area/depth/fanout heuristic, retained as a diagnostic; strict depth improvement is not required for cheap STA.',
            scope='Experimental full-chip RTL/mapped controller output and surviving-state equivalence with arbitrary SRAM responses and reference state, exact external/macro terminals, independent macro-model/pin oracles and complete mapped cost. Only next values of state slots absent in both mapped chips are excluded; reference current inputs remain arbitrary. No physical run or backend promotion.')
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
