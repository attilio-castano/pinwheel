#!/usr/bin/env python3
"""Stage an immutable qualification package. No CAD or Docker is launched."""
from __future__ import annotations
import argparse
import json
import os
from pathlib import Path
import re
import shutil
import sys

from audits import port_map, sha, spice_headers, write
from bind import verify_admission

ROOT = next(parent for parent in Path(__file__).resolve().parents
            if (parent / 'tools/physical-toolchain.json').is_file())
HERE = Path(__file__).resolve().parent
MASTER = 'RM_IHPSG13_1P_64x64_c2_bm_bist'


def referenced_files(value):
    if isinstance(value, str) and value.startswith('dir::'):
        yield value[5:]
    elif isinstance(value, dict):
        for item in value.values():
            yield from referenced_files(item)
    elif isinstance(value, list):
        for item in value:
            yield from referenced_files(item)


def validate_overlay(pdkr, manifest_path):
    """Validate the approved byte-preserving, two-file official PDK completion."""
    pdkr, manifest_path = Path(pdkr).resolve(), Path(manifest_path).resolve()
    manifest = json.loads(manifest_path.read_text())
    assert manifest['schema'] == 'pinwheel-readonly-PDK-dependency-overlay-v1'
    assert manifest['revision'] == '2bbec755dc67ca3db0261c3d6163e15735d66710'
    assert Path(manifest['overlay_PDK_root']).resolve() == pdkr
    assert manifest['all_original_file_bytes_exact'] is True
    assert manifest['all_original_symlink_targets_exact'] is True
    assert manifest['all_original_symlink_resolved_file_bytes_exact'] is True
    assert len(manifest['only_added_files']) == 2
    regular = manifest['all_overlay_regular_files_sha256']
    links = manifest['all_overlay_symlink_targets']
    assert len(regular) == 405 and len(links) == 142
    actual_regular, actual_links = set(), set()
    for path in pdkr.rglob('*'):
        relative = str(path.relative_to(pdkr))
        if path.is_symlink():
            actual_links.add(relative)
            assert os.readlink(path) == links[relative]
        elif path.is_file():
            actual_regular.add(relative)
            assert sha(path) == regular[relative]
    assert actual_regular == set(regular) and actual_links == set(links)
    original = Path(manifest['installed_PDK_root']).resolve()
    additions = {row['path'] for row in manifest['only_added_files']}
    assert set(regular) - additions == {str(path.relative_to(original)) for path in original.rglob('*') if path.is_file() and not path.is_symlink()}
    for relative in set(regular) - additions:
        assert sha(original / relative) == regular[relative]
    for relative in links:
        assert os.readlink(original / relative) == links[relative]
        if (original / relative).is_file():
            assert sha(original / relative) == sha(pdkr / relative)
    for source, digest in manifest['source_sha256'].items():
        assert sha(ROOT / source) == digest
    return {'path': str(manifest_path), 'sha256': sha(manifest_path),
        'original_PDK_byte_and_symlink_identity': True, 'only_two_same_pinned_commit_files_added': True,
        'official_precheck_qualified': False}


def stage(args):
    out = args.out.resolve()
    if out.exists():
        raise FileExistsError('Immutable preparation destination already exists: ' + str(out))
    campaign_path = args.campaign.resolve()
    campaign = json.loads(campaign_path.read_text())
    assert campaign['single_heavy_CAD_process'] is True
    assert campaign['native_cpus'] == 4 and campaign['native_memory'] == '6g'
    bindings_path = args.source_bindings.resolve()
    bindings_raw = json.loads(bindings_path.read_text())
    admission = verify_admission(bindings_raw)
    assert json.loads(Path(admission['route_receipt']).read_text())['image_id'] == campaign['image_id']
    bindings = bindings_raw.get('source_sha256', bindings_raw)
    if not isinstance(bindings, dict) or not bindings:
        raise ValueError('Expected nonempty source_sha256 path→SHA256 map')
    bindings = {str((ROOT / p).resolve()): h for p, h in bindings.items()}
    required = {name: getattr(args, name).resolve() for name in
        ('odb', 'def_file', 'inventory', 'master_obs', 'via_definitions', 'core_config', 'sdc')}
    routed_names = {'odb': 'checkpoint.odb', 'def_file': 'checkpoint.def',
        'inventory': 'native-inventory.json', 'master_obs': 'master-OBS-signature.json',
        'via_definitions': 'via-definitions.json'}
    assert all(required[key] == Path(admission['after_root']) / name for key, name in routed_names.items())
    for path in required.values():
        if str(path) not in bindings or sha(path) != bindings[str(path)]:
            raise ValueError('Required routed input missing or changed in explicit source binding: ' + str(path))
    for path, digest in bindings.items():
        assert re.fullmatch(r'[0-9a-f]{64}', digest) and sha(path) == digest, path
    protected = dict(campaign['protected_sources_sha256'])
    protected.update(campaign['reference_files_sha256'])
    for path, digest in protected.items():
        assert sha(path) == digest, path
    core = required['core_config'].parent
    config = json.loads(required['core_config'].read_text())
    assert config['DESIGN_NAME'] == 'tt_um_pinwheel_buffered'
    assert config['CLOCK_PERIOD'] == 20 and config['RT_MAX_LAYER'] == 'Metal4'
    assert config['RUN_MAGIC_DRC'] is True and config['RUN_KLAYOUT_DRC'] is True
    core_files = sorted(set(referenced_files(config)))
    core_paths = []
    for relative in core_files:
        path = (core / relative).resolve()
        if not path.is_relative_to(core) or not path.is_file():
            raise ValueError('Unresolved/escaping frozen core reference: ' + relative)
        core_paths.append((path, relative))
    assert sha(core / 'core.sdc') == sha(required['sdc']), 'Frozen SDC and core SDC differ'
    lef = core / 'macro' / (MASTER + '.lef')
    cdl = core / 'macro' / (MASTER + '.cdl')
    lef_ports = re.findall(r'^\s*PIN\s+(\S+)\s*$', lef.read_text(), re.M)
    pairs = port_map(spice_headers(cdl.read_text())[MASTER], lef_ports)
    assert len(pairs) == 345, 'Wrong current macro source'
    native = json.loads(required['inventory'].read_text())
    standard_spice = ROOT / 'build/physical/pdk/ihp-sg13cmos5l/libs.ref/sg13cmos5l_stdcell/spice/sg13cmos5l_stdcell.spice'
    standard_models = spice_headers(standard_spice.read_text())
    master_pins = {}
    for instance in native['instances'].values():
        pins = sorted(t[0] for t in instance['terminals'])
        master = instance['master']
        assert master not in master_pins or master_pins[master] == pins
        master_pins[master] = pins
    assert len(native['instances']) == 28970 and len(master_pins) == 50
    for master, pins in master_pins.items():
        expected = lef_ports if master == MASTER else standard_models[master]
        assert set(pins) == set(expected), 'Native/source master pin mismatch: ' + master
    out.mkdir(parents=True)
    (out / 'input').mkdir()
    (out / 'core').mkdir()
    names = {'odb': 'checkpoint.odb', 'def_file': 'checkpoint.def', 'inventory': 'inventory.json',
             'master_obs': 'master-OBS.json', 'via_definitions': 'vias.json', 'sdc': 'core.sdc'}
    for key, name in names.items():
        shutil.copyfile(required[key], out / 'input' / name)
    shutil.copyfile(required['core_config'], out / 'core' / 'core.json')
    for path, relative in core_paths:
        target = out / 'core' / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(path, target)
    helper_sources = sorted([*HERE.glob('*.py'), *HERE.glob('*.tcl')])
    snapshot = HERE / 'native_inventory.py'
    if not snapshot.is_file():
        snapshot = ROOT / 'build/physical/tt-p2-drt-onepass-tools-04/native_inventory.py'
    campaign_runner = HERE / 'campaign_runner.py'
    if not campaign_runner.is_file():
        campaign_runner = ROOT / 'tools/pinwheel-physical-campaign/runner.py'
    for path in helper_sources:
        shutil.copyfile(path, out / path.name)
    shutil.copyfile(snapshot, out / 'native_inventory.py')
    shutil.copyfile(campaign_runner, out / 'campaign_runner.py')
    capability = HERE / 'native-assets.json'
    if not capability.is_file():
        capability = campaign_path.parent / 'qualification-probe-02/probe.json'
    assert capability.is_file(), 'Actual installed step/script capture required'
    shutil.copyfile(capability, out / 'native-assets.json')
    write(out / 'macro-port-map.json', {'master': MASTER, 'port_count': len(pairs), 'pairs': pairs,
        'status': 'bijective_source_spelling_map', 'internal_SRAM_LVS_proven': False})
    write(out / 'source-model-map.json', {'instances': len(native['instances']),
        'master_count': len(master_pins), 'native_master_pin_sets': master_pins,
        'all_native_to_source_model_pin_sets_exact': True, 'physical_connectivity_proven': False})
    pdkr = args.pdk_root.resolve() if getattr(args, 'pdk_root', None) is not None else ROOT / 'build/physical/pdk'
    overlay = None
    if getattr(args, 'pdk_root', None) is not None:
        assert args.pdk_overlay_manifest is not None
        overlay = validate_overlay(pdkr, args.pdk_overlay_manifest)
    else:
        assert getattr(args, 'pdk_overlay_manifest', None) is None
    pdk = pdkr / 'ihp-sg13cmos5l'
    pdk_files = [pdk / 'libs.ref/sg13cmos5l_stdcell/lef/sg13cmos5l_tech.lef',
        pdk / 'libs.ref/sg13cmos5l_stdcell/lef/sg13cmos5l_stdcell.lef',
        pdk / 'libs.ref/sg13cmos5l_stdcell/gds/sg13cmos5l_stdcell.gds',
        pdk / 'libs.ref/sg13cmos5l_stdcell/spice/sg13cmos5l_stdcell.spice',
        pdk / 'libs.tech/librelane/IHP_rcx_patterns.rules', pdk / 'libs.tech/magic/ihp-sg13cmos5l.tech',
        pdk / 'libs.tech/netgen/ihp-sg13cmos5l_setup.tcl',
        pdk / 'libs.tech/klayout/tech/drc/ihp-sg13cmos5l.drc']
    # Bind every local PDK file, including symlink targets and deck includes.
    # No installation or PDK edits occur during preparation or execution.
    pdk_files += sorted(p for p in pdkr.rglob('*') if p.is_file())
    sources = dict(protected)
    sources.update(bindings)
    sources.update({str(p): sha(p) for p, _ in core_paths})
    sources.update({str(p): sha(p) for p in [campaign_path, bindings_path, *pdk_files]})
    if overlay:
        sources[overlay['path']] = overlay['sha256']
        overlay_manifest = json.loads(Path(overlay['path']).read_text())
        sources.update({str((ROOT / path).resolve()): digest for path, digest in overlay_manifest['source_sha256'].items()})
    request = {'schema': 'pinwheel-isolated-postroute-qualification-v1',
        'design': config['DESIGN_NAME'], 'campaign_path': str(campaign_path),
        'campaign_sha256': sha(campaign_path), 'campaign_id': args.campaign_id,
        'heavy_lock': str(args.heavy_lock.resolve()), 'image_id': campaign['image_id'],
        'hard_stop_epoch': campaign['hard_stop_epoch'],
        'native_work_stop_epoch': campaign['hard_stop_epoch'] - campaign['budgets_seconds']['closeout'],
        'native_binary_sha256': args.native_binary_sha256,
        'route_admission': admission,
        'helper_origin_sha256': {str(p): sha(p) for p in [snapshot, campaign_runner, capability, *helper_sources]},
        'helper_origin_binding_scope': 'Origins are provenance only; actual copied immutable helper files are frozen in staged_sha256 and every phase receipt.',
        'source_sha256': sources,
        'staged_sha256': {str(p.relative_to(out)): sha(p) for p in out.rglob('*') if p.is_file()},
        'PDK_root': str(pdkr), 'PDK_overlay': overlay, 'source_bindings_path': str(bindings_path),
        'expected_corners': ['nom_typ_1p20V_25C', 'nom_slow_1p08V_125C', 'nom_fast_1p32V_m40C'],
        'FAST_qualification': 'logic -40C / SRAM -55C hybrid; conditional screening',
        'RCX_qualification': 'one nominal model0 from 7-layer SG13G2 source; used-layer index mapping and extraction coverage required; no min/max RC accuracy claim',
        'no_fill_no_ECO_no_RTL_or_ABI_change': True,
        'official_precheck_qualified': False}
    assert re.fullmatch(r'[0-9a-f]{64}', args.native_binary_sha256)
    write(out / 'prepared.json', request)
    return out / 'prepared.json'


def main():
    p = argparse.ArgumentParser(description=__doc__)
    for name in ('campaign', 'source-bindings', 'odb', 'inventory', 'master-obs', 'via-definitions', 'core-config', 'sdc', 'out', 'heavy-lock'):
        p.add_argument('--' + name, type=Path, required=True)
    p.add_argument('--def', dest='def_file', type=Path, required=True)
    p.add_argument('--campaign-id', required=True)
    p.add_argument('--native-binary-sha256', required=True)
    p.add_argument('--pdk-root', type=Path)
    p.add_argument('--pdk-overlay-manifest', type=Path)
    args = p.parse_args()
    result = stage(args)
    print(json.dumps({'status': 'prepared_only_no_CAD', 'prepared': str(result), 'sha256': sha(result)}))


if __name__ == '__main__':
    main()
