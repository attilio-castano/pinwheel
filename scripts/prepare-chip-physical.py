#!/usr/bin/env python3
"""Freeze a validated physical target and pinned macro views for a local experiment.

This consumes a completed SRAM comparison, never an unvalidated new emission.
Only --fetch downloads missing views; each is checked against the pinned Git
inventory before use. The shared PDK installation is never modified.
"""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import urllib.request

import physical_floorplan
import physical_checkpoint
import physical_target
from mapped_physical import selected_mapping
from validation_run import fresh_directory, sha

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / 'build/physical'
MACRO = 'RM_IHPSG13_1P_64x64_c2_bm_bist'


def blob(data):
    return hashlib.sha1(f'blob {len(data)}\0'.encode() + data).hexdigest()


def fetch_checked(path, url, verify, fetch):
    if not path.exists():
        if not fetch:
            raise RuntimeError(f'Missing {path}; use --fetch to install pinned inputs')
        with urllib.request.urlopen(url, timeout=90) as response:
            data = response.read()
        if not verify(data):
            raise RuntimeError(f'Unpinned download: {url}')
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)
    if not verify(path.read_bytes()):
        raise RuntimeError(f'Modified input: {path}')


def main():
    p = argparse.ArgumentParser(description=__doc__)
    source = p.add_mutually_exclusive_group(required=True)
    source.add_argument('--comparison', type=Path, help='Legacy validated hybrid comparison')
    source.add_argument('--target', type=Path, help='Checked physical target declaration')
    p.add_argument('--design', required=True)
    p.add_argument('--fetch', action='store_true')
    p.add_argument('--mapped-role', choices=('baseline', 'tiled'),
                   help='Treat --comparison as a selected validated mapping; bypass synthesis using its staged initial state')
    p.add_argument('--macro-placement', type=Path,
                   help='JSON mapping of existing macro instances to experimental locations/orientations')
    p.add_argument('--placement-exclusions', type=Path,
                   help='JSON list of rectangles where the floorplan must remove placement sites')
    args = p.parse_args()
    mapped_input = None
    target = None
    master = MACRO
    if args.target:
        if args.mapped_role or args.macro_placement or args.placement_exclusions:
            p.error('Target declarations own source, macro placement and exclusions')
        target, mapped_paths, mapped_input, ownership, roles = physical_target.resolve(args.target, ROOT)
        master = target['macro']['master']
        rtl = mapped_paths['netlist']
        args.comparison = ROOT / target['source']['selection']
    elif args.mapped_role:
        mapped_paths, mapped_input = selected_mapping(args.comparison, args.mapped_role, ROOT)
        rtl = mapped_paths['netlist']
    else:
        receipt = json.loads(args.comparison.read_text())
        for path, digest in receipt['source_sha256'].items():
            if sha(ROOT / path) != digest:
                raise RuntimeError(f'Stale comparison source: {path}')
        rtl = args.comparison.resolve().parent / 'hybrid/chip.sv'
        if sha(rtl) != receipt['variants']['hybrid']['artifacts']['chip']['rtl_sha256']:
            raise RuntimeError('Changed validated hybrid RTL')
    lock = json.loads((ROOT / 'tools/physical-toolchain.json').read_text())
    upstream = BASE / 'upstream'
    tree_path = upstream / 'pdk-tree.json'
    if not tree_path.exists() and args.fetch:
        url = f"https://api.github.com/repos/IHP-GmbH/IHP-Open-PDK/git/trees/{lock['pdk_revision']}?recursive=1"
        with urllib.request.urlopen(url, timeout=90) as response:
            # The locked inventory was stored with this serialization. GitHub
            # may change whitespace in the response; the complete digest must
            # still match after restoring the original serialization.
            data = (json.dumps(json.load(response), indent=2) + '\n').encode()
        if hashlib.sha256(data).hexdigest() != lock['pdk_tree_sha256']:
            raise RuntimeError('Unpinned PDK inventory')
        upstream.mkdir(parents=True, exist_ok=True)
        tree_path.write_bytes(data)
    if sha(tree_path) != lock['pdk_tree_sha256']:
        raise RuntimeError('Modified PDK inventory')
    tree = json.loads(tree_path.read_text())
    if tree['truncated'] or tree['sha'] != lock['pdk_revision']:
        raise RuntimeError('Incomplete PDK inventory')
    entries = {e['path']: e for e in tree['tree']}
    template = upstream / 'tt_block_6x4_pgvdd.def'
    fetch_checked(template,
        f"https://raw.githubusercontent.com/TinyTapeout/tt-support-tools/{lock['support_revision']}/{lock['allocation']['tt_def_template']}",
        lambda b: hashlib.sha256(b).hexdigest() == lock['allocation']['tt_def_template_sha256'], args.fetch)
    views = [f'lef/{master}.lef', f'gds/{master}.gds', f'cdl/{master}.cdl', f'verilog/{master}.v',
             *[f'lib/{master}_{suffix}.lib' for suffix in
               ['typ_1p20V_25C', 'slow_1p08V_125C', 'fast_1p32V_m55C']]]
    installed = []
    for relative in views:
        source = 'ihp-sg13g2/libs.ref/sg13g2_sram/' + relative
        path = upstream / 'macro' / Path(relative).name
        existing = ROOT / 'build/storage/macros' / path.name
        if not path.exists() and existing.exists() and blob(existing.read_bytes()) == entries[source]['sha']:
            path.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(existing, path)
        fetch_checked(path,
            f"https://raw.githubusercontent.com/IHP-GmbH/IHP-Open-PDK/{lock['pdk_revision']}/{source}",
            lambda b, expected=entries[source]['sha']: blob(b) == expected, args.fetch)
        installed.append(path)
    placements = json.loads(args.macro_placement.read_text()) if args.macro_placement else None
    exclusions = json.loads(args.placement_exclusions.read_text()) if args.placement_exclusions else None
    experiment_config = None
    if target:
        base_config = json.loads((ROOT / 'physical/chip.json').read_text())
        experiment_config = physical_target.configuration(base_config, target)
        geometry = physical_target.validate_views(target, upstream / 'macro', mapped_input, base_config)
        physical_target.validate_terminals(json.loads(mapped_paths['mapped'].read_text())['modules']['tt_um_pinwheel'], geometry)
        placements = target['macro']['instances']
        exclusions = target['placement_exclusions']
    elif args.macro_placement or args.placement_exclusions:
        experiment_config = json.loads((ROOT / 'physical/chip.json').read_text())
        if args.macro_placement:
            experiment_config = physical_floorplan.apply_placement(experiment_config, placements)
        if args.placement_exclusions:
            experiment_config = physical_floorplan.apply_exclusions(experiment_config, exclusions)
    out = fresh_directory(BASE, args.design)
    (out / 'macro').mkdir()
    for path in installed:
        shutil.copyfile(path, out / 'macro' / path.name)
    # The vendor model includes simulation timing constructs. The flow needs
    # only its exact interface; behavior and timing come from the independently
    # tested model and the pinned Liberty views, respectively.
    model = (out / 'macro' / (master + '.v')).read_text()
    header, separator, _ = model.partition('// ---- Simulation-only check:')
    if not separator or header.count('module ' + master + ' (') != 1:
        raise RuntimeError('Unrecognized pinned SRAM interface')
    header = header.replace('module ' + master, '(* blackbox *) module ' + master, 1)
    (out / 'macro' / (master + '.bb.v')).write_text(header + 'endmodule\n`endcelldefine\n')
    for source, name in [(rtl, 'design.sv'), (ROOT / 'test/sram_chip.sv', 'sram_chip.sv'),
                         (ROOT / 'physical/chip.json', 'core.json'),
                         (ROOT / 'physical/chip.sdc', 'core.sdc'), (template, template.name),
                         (args.comparison, 'validation.json')]:
        shutil.copyfile(source, out / name)
    if experiment_config is not None:
        (out / 'core.json').write_text(json.dumps(experiment_config, indent=2) + '\n')
    if placements is not None:
        (out / 'macro-placement.json').write_text(json.dumps(placements, indent=2) + '\n')
    if exclusions is not None:
        (out / 'placement-exclusions.json').write_text(json.dumps(exclusions, indent=2) + '\n')
    if mapped_input:
        shutil.copyfile(mapped_paths['mapped'], out / 'mapped.json')
        shutil.copyfile(mapped_paths['assembly'], out / 'assembly.json')
        state = dict(nl='/work/core/design.sv', json_h='/work/core/mapped.json', metrics={})
        (out / 'initial-state.json').write_text(json.dumps(state, indent=2) + '\n')
        physical_checkpoint.capture(out / 'initial-state.json', out / 'initial-manifest.json', out)
    if target:
        for name, value in [('target.json', target), ('state-ownership.json', ownership),
                            ('path-roles.json', roles), ('macro-geometry.json', geometry)]:
            (out / name).write_text(json.dumps(value, indent=2) + '\n')
    files = {str(f.relative_to(out)): sha(f) for f in sorted(out.rglob('*')) if f.is_file()}
    inputs = dict(rtl_sha256=sha(out / 'design.sv'), variant='hybrid-sram-chip',
        profile='chip', files_sha256=files, validation_receipt=str(args.comparison.resolve()),
        macro_placement=placements, placement_exclusions=exclusions,
        floorplan_helper_sha256=sha(Path(physical_floorplan.__file__)),
        validation_receipt_sha256=sha(args.comparison),
        source_sha256={str(p.relative_to(ROOT)): sha(p) for p in
                       [Path(__file__).resolve(), ROOT / 'physical/chip.json', ROOT / 'physical/chip.sdc']},
        boundary='Experimental complete result chip with two hybrid SRAM macros and the official 6x4 pin template. '
                 '20 ns clock and explicit 4/0.2 ns I/O assumptions. SRAM adapter refinement remains separate. '
                 'Fast screening combines -40 C cells with the available -55 C SRAM view; it is not a matched-temperature signoff corner. '
                 'The two-layer power grid uses TopMetal1 for SRAM access; shuttle power-grid compatibility remains to be qualified. '
                 'KLayout DRC/XOR remain disabled as in the existing pinned flow; no blanket signoff claim.')
    if mapped_input:
        inputs.update(mapped_input=mapped_input, variant='mapped-' + (target['name'] if target else 'hybrid-' + args.mapped_role),
            boundary='Retained complete-chip mapped netlist, bypassing synthesis with an exact staged NL/JSON checkpoint. '
                     'Two SRAM macros, official 6x4 template, matched 20 ns and 4/0.2 ns I/O constraints. '
                     'Physical import must pass connection identity before placement/clock/hold repair. '
                     'Fast screening mixes -40 C cells and -55 C SRAM; not a signoff corner. '
                     'Power-grid qualification, detailed routing, antenna closure and extracted timing remain separate.')
        for path in [ROOT / 'scripts/mapped_physical.py', ROOT / 'scripts/tiled_chip.py',
                     ROOT / 'scripts/validation_run.py', ROOT / 'scripts/physical_checkpoint.py']:
            inputs['source_sha256'][str(path.relative_to(ROOT))] = sha(path)
    if target:
        inputs['physical_target'] = dict(name=target['name'], declaration_sha256=sha(out / 'target.json'),
            platform_sha256={p: sha(ROOT / p) for p in ['physical/chip.json', 'physical/chip.sdc', 'tools/physical-toolchain.json']},
            helper_sha256=sha(ROOT / 'scripts/physical_target.py'))
        inputs['source_sha256']['scripts/physical_target.py'] = sha(ROOT / 'scripts/physical_target.py')
        inputs['boundary'] = ('Validated mapped physical target with exact state and semantic path roles. '
            'Official 6x4 template and retained clock/I/O assumptions. Physical import must preserve all connections. '
            'Geometry preflight does not establish routed pin access or power continuity. '
            'Fast screening mixes -40 C cells and -55 C SRAM. Power qualification and final physical checks remain separate.')
    (out / 'inputs.json').write_text(json.dumps(inputs, indent=2) + '\n')
    print(out / 'inputs.json')


if __name__ == '__main__':
    main()
