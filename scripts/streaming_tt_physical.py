"""Immutable intake and explicit boundaries for the streaming TT experiment."""
from dataclasses import asdict
import gzip
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / 'build/physical'
ARCHIVE = Path('/Users/attiliocastano/Developer/pinwheel/build/research-archives/2026-10-16-tt-buffered-8259/build/physical')
MANIFEST = ROOT / 'docs/research/evidence/streaming-mapped-continuation-20261017/manifest.json'
PRODUCERS = ('scripts/streaming_tt_physical.py', 'scripts/prepare-streaming-tt-physical.py',
    'scripts/run-streaming-tt-physical.py', 'physical/streaming-tt.json', 'physical/streaming-tt.sdc',
    'physical/streaming_tt/pdn.tcl', 'physical/streaming_tt/librelane_plugin_streaming_tt.py',
    'scripts/streaming_tt_pdn_geometry.py', 'test/test_streaming_tt_pdn_geometry.py',
    'test/test_streaming_tt_physical.py', 'tools/physical-toolchain.json')
FORBIDDEN_CONFIG = {'MACROS', 'PDN_MACRO_CONNECTIONS', 'VERILOG_DEFINES', 'MACRO_PLACEMENT_CFG',
    'PDN_CONNECT_MACROS_TO_GRID', 'FP_OBSTRUCTIONS'}
BOUNDARY = ('Fresh standard-cell-only physical experiment from a certified mapped artifact. '
    'Synthesis is bypassed; interface metadata alone is regenerated. Placement/CTS/repair '
    'do not inherit the source certificate: every new logical netlist/clock/state change '
    'needs independent readback/proof. A completed flow is not physical acceptance, '
    'official precheck, board/CDC or electrical qualification. Latest ODB is authoritative; '
    'a carried state.nl may precede later ODB-only repairs.')


def require(value, message):
    if not value: raise ValueError(message)


def read(path):
    def pairs(items):
        result = {}
        for key, value in items:
            require(key not in result, 'Duplicate physical input JSON key: ' + key)
            result[key] = value
        return result
    return json.loads(Path(path).read_bytes(), object_pairs_hook=pairs)


def sha(path):
    with Path(path).open('rb') as stream: return hashlib.file_digest(stream, 'sha256').hexdigest()


def write(path, value):
    path = Path(path)
    temporary = path.with_name(path.name + '.tmp')
    temporary.write_text(json.dumps(value, indent=2) + '\n')
    temporary.replace(path)


def safe_name(value):
    require(type(value) is str and re.fullmatch(r'[A-Za-z0-9_-]+', value), 'Unsafe physical stage/tag')
    return value


def regular(path):
    path = Path(path)
    require(path.is_file() and not path.is_symlink(), 'Missing or aliased physical input: ' + str(path))
    return path


def relative_path(value):
    path = Path(value)
    require(not path.is_absolute() and path.parts and '..' not in path.parts, 'Escaping physical relative path')
    return path


def committed(path):
    path = regular(path)
    relative = str(path.relative_to(ROOT))
    data = subprocess.check_output(['git', 'show', 'HEAD:' + relative], cwd=ROOT, timeout=30)
    require(path.read_bytes() == data, 'Commit unchanged physical producer/input first: ' + relative)
    return data


def producer_hashes(*, optimized=False):
    paths = set(PRODUCERS)
    # These parsers are executed by candidate intake and must belong to the producer.
    if optimized:
        from streaming_tt_intake import dependency_closure
        paths.update(('scripts/streaming_tt_candidate.py','scripts/streaming_tt_intake.py',
            'scripts/streaming_tt_pdk.py','scripts/streaming_tt_rc.py','scripts/streaming_tt_verilog.py',
            'physical/streaming-tt-candidate.json','tools/streaming-tt-signoff.json',
            'test/test_streaming_tt_intake.py','test/test_streaming_tt_candidate.py',
            'test/test_streaming_tt_pdk.py','test/test_streaming_tt_rc.py','test/test_streaming_tt_verilog.py'))
        paths = set(dependency_closure(ROOT,paths)['files'])
    else:
        paths.update(str(path.relative_to(ROOT)) for path in (ROOT / 'scripts').glob('streaming_mapped_*.py'))
    return {name: hashlib.sha256(committed(ROOT / name)).hexdigest() for name in sorted(paths)}


def verify_files(root, mapping):
    require(type(mapping) is dict and mapping, 'Missing immutable physical input map')
    for name, expected in mapping.items():
        path = regular(Path(root) / relative_path(name))
        require(sha(path) == expected, 'Physical input changed: ' + str(path))


def verify_pdk(directory, lock, tree_path=ARCHIVE / 'upstream/pdk-tree.json'):
    directory = Path(directory).resolve()
    receipt = read(regular(directory / 'installed.json'))
    require(receipt.get('revision') == lock['pdk_revision'] and receipt.get('tree_sha256') == lock['pdk_tree_sha256'],
        'Wrong retained PDK revision/tree')
    require(sha(regular(tree_path)) == lock['pdk_tree_sha256'], 'Wrong pinned PDK Git inventory')
    tree = read(tree_path)
    require(tree.get('truncated') is False, 'Truncated pinned PDK Git inventory')
    entries = {entry['path']: entry for entry in tree['tree']}
    verify_files(directory, receipt['files_sha256'])
    def blob(data): return hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
    for name in receipt['files_sha256']:
        require(name in entries and entries[name]['mode'] in ('100644', '100755') and
            blob((directory / name).read_bytes()) == entries[name]['sha'], 'PDK file differs from pinned Git blob: ' + name)
    for name, target in receipt['symlinks'].items():
        path = directory / relative_path(name)
        require(path.is_symlink() and os.readlink(path) == target and path.resolve().is_relative_to(directory) and
            path.resolve().exists(), 'Broken/escaping retained PDK symlink: ' + name)
        require(name in entries and entries[name]['mode'] == '120000' and blob(target.encode()) == entries[name]['sha'],
            'PDK symlink differs from pinned Git blob: ' + name)
    return dict(root=str(directory), installed_sha256=sha(directory / 'installed.json'),
        regular_files=len(receipt['files_sha256']), symlinks=len(receipt['symlinks']),
        revision=receipt['revision'], tree_sha256=receipt['tree_sha256'])


def stage_pdk(source, destination, lock):
    before = verify_pdk(source, lock)
    source, destination = Path(source).resolve(), Path(destination)
    destination.mkdir(parents=True, exist_ok=False)
    receipt = read(source / 'installed.json')
    for name in receipt['files_sha256']:
        target = destination / relative_path(name); target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source / name, target)
    for name, value in receipt['symlinks'].items():
        target = destination / relative_path(name); target.parent.mkdir(parents=True, exist_ok=True)
        target.symlink_to(value)
    shutil.copyfile(source / 'installed.json', destination / 'installed.json')
    after = verify_pdk(destination, lock)
    require(verify_pdk(source, lock) == before, 'Retained PDK changed during staging')
    return dict(source=before, staged=after)


def validate_config(config, depth):
    expected = read(ROOT / 'physical/streaming-tt.json')
    expected['DESIGN_NAME'] = 'tt_um_pinwheel_streaming_ready_d' + str(depth)
    require(config == expected, 'Physical config differs from the committed baseline')
    require(not FORBIDDEN_CONFIG.intersection(config), 'SRAM/macro configuration in standard-cell target')
    require(depth in (2, 4) and config['CLOCK_PERIOD'] == 20 and config['RT_MAX_LAYER'] == 'Metal4' and
        config['PDN_HORIZONTAL_LAYER'] == 'Metal3' and config['PDN_VERTICAL_LAYER'] == 'Metal4' and
        config['PDN_RAIL_LAYER'] == 'Metal1' and config['RUN_CTS'] is True and
        config['TIMING_VIOLATION_CORNERS'] == ['*'], 'Changed TT timing/layer boundary')


def certified_candidate(manifest_path, depth):
    from streaming_mapped_liberty import LIBRARY_SHA256, load_library
    from streaming_mapped_netlist import load_mapped
    manifest_path = Path(manifest_path).resolve()
    manifest = json.loads(committed(manifest_path))
    require(manifest.get('schema') == 'pinwheel.streaming-mapped-evidence.v1', 'Not mapped certificate evidence')
    selected = [item for item in manifest['receipts'] if item['kind'] == 'full']
    require(len(selected) == 1, 'Exactly one accepted mapped full receipt required')
    item = selected[0]
    payload_path = manifest_path.parent / relative_path(item['file'])
    payload = committed(payload_path)
    require(hashlib.sha256(payload).hexdigest() == item['compressed_sha256'], 'Mapped compressed receipt changed')
    raw = gzip.decompress(payload)
    require(hashlib.sha256(raw).hexdigest() == item['raw_sha256'], 'Mapped receipt raw bytes changed')
    report = json.loads(raw)
    require(report.get('passed') is True and report.get('full_qualification') is True and
        report.get('schema') == 'pinwheel.streaming-mapped-full.v1' and not report.get('error') and
        not report.get('closeout_error'), 'Mapped whole-device certificate is not accepted')
    worker = report['worker']; campaign = worker['campaign']
    require(worker['passed'] is True and campaign['passed'] is True and campaign['wrapper_checked'] is True and
        campaign['wrapper_axiom_audit_checked'] is True and campaign['wrapper_private_axiom_rejected'] is True and
        campaign['required_qnames_checked'] is True and campaign['extra_qnames_checked'] is True,
        'Incomplete mapped component/session audit')
    value = campaign['wrapper_metadata']['depths'][str(depth)]
    source_root = Path(item['retained_directory']) / 'worker'
    netlist = regular(Path(value['complete_json']))
    require(netlist.resolve().is_relative_to(source_root.resolve()), 'Mapped candidate escaped retained worker')
    sv = regular(netlist.with_suffix('.sv'))
    for path in (netlist, sv):
        relative = str(path.relative_to(source_root))
        require(worker['artifact_sha256'][relative] == sha(path), 'Certified mapped artifact changed: ' + relative)
    require(sha(netlist) == value['complete_sha256'], 'Whole mapped hierarchy hash differs')
    library = regular(Path(report['library']['staged']))
    require(sha(library) == LIBRARY_SHA256, 'Certified Liberty differs')
    graph = load_mapped(netlist, value['outer']['top'], load_library(library))
    expected_bits = {2: 6039, 4: 6195}[depth]
    require(len(graph.flipflops) == expected_bits and len(graph.state_bits) == expected_bits,
        'Source mapped FF inventory is not complete/bijective')
    # Old certificates cannot migrate silently across source/ISA/parser changes.
    for name, expected in report['source_sha256'].items():
        if name.startswith('Pinwheel/') or name.startswith('scripts/streaming_') or name in ('lean-toolchain', 'tools/hardware-toolchain.json'):
            require(sha(regular(ROOT / name)) == expected, 'Certified design/parser source changed: ' + name)
    return dict(manifest=str(manifest_path), manifest_sha256=sha(manifest_path),
        accepted_source_commit=report['source_commit'], accepted_receipt_sha256=item['raw_sha256'],
        source_root=str(source_root), netlist=str(netlist), netlist_sha256=sha(netlist),
        verilog=str(sv), verilog_sha256=sha(sv), library=str(library), liberty_sha256=sha(library),
        top=value['outer']['top'], source_ff_bits=expected_bits,
        source_cell_count=len(graph.gates) + len(graph.flipflops),
        source_state=[asdict(ff) for ff in graph.flipflops], inputs=graph.inputs, outputs=graph.outputs,
        post_pnr_equivalence_proved=False)


def prepare(design, *, depth=2, manifest=MANIFEST, pdk=ARCHIVE / 'pdk', template=ARCHIVE / 'upstream/tt_block_6x4_pgvdd.def'):
    from streaming_tt_pdn_geometry import admit
    safe_name(design); require(depth in (2, 4), 'Supported TT depth is2 or4')
    sources = producer_hashes()
    lock = read(ROOT / 'tools/physical-toolchain.json')
    candidate = certified_candidate(manifest, depth)
    template = regular(template)
    require(sha(template) == lock['allocation']['tt_def_template_sha256'], 'Wrong official6x4 template')
    geometry = admit(template, ROOT / 'physical/streaming_tt/pdn.tcl')
    out = BASE / design; out.mkdir(parents=True, exist_ok=False)
    staged = stage_pdk(pdk, out / 'pdk', lock)
    inputs = out / 'inputs'; inputs.mkdir()
    for source, name in [(candidate['verilog'], 'design.v'), (candidate['netlist'], 'certified.json'),
            (ROOT / 'physical/streaming-tt.sdc', 'core.sdc'), (template, 'tt_block_6x4_pgvdd.def'),
            (ROOT / 'physical/streaming_tt/pdn.tcl', 'pdn.tcl'),
            (ROOT / 'physical/streaming_tt/librelane_plugin_streaming_tt.py', 'librelane_plugin_streaming_tt.py')]:
        shutil.copyfile(source, inputs / name)
    config = read(ROOT / 'physical/streaming-tt.json'); config['DESIGN_NAME'] = candidate['top']
    validate_config(config, depth)
    require(admit(inputs / 'tt_block_6x4_pgvdd.def', inputs / 'pdn.tcl') == geometry, 'Staged PDN geometry changed')
    write(inputs / 'pdn-geometry-admission.json', geometry)
    write(inputs / 'core.json', config)
    write(inputs / 'seed.json', dict(nl='/work/inputs/design.v', metrics={}))
    write(inputs / 'source-state.json', dict(top=candidate['top'], source_ff_bits=candidate['source_ff_bits'],
        source_state=candidate['source_state'], inputs=candidate['inputs'], outputs=candidate['outputs']))
    files = {str(path.relative_to(inputs)): sha(path) for path in sorted(inputs.rglob('*')) if path.is_file()}
    receipt = dict(schema='pinwheel.streaming-tt-physical-input.v1', status='prepared', qualified=False,
        physical_acceptance_claim=False, producer_commit=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, timeout=30).decode().strip(),
        producer_sha256=sources, design=design, depth=depth, candidate=candidate, pdk=staged,
        input_sha256=files, template_sha256=sha(template), boundary=BOUNDARY,
        pdn_geometry_admission=geometry,
        synthesis_bypassed=True, physical_grid_status='designed_unvalidated',
        deferred_checks=['post-PNR kernel correspondence', 'official TT precheck', 'extracted signoff', 'board/CDC qualification'])
    write(out / 'inputs.json', receipt)
    verify_prepared(out)
    return out


def verify_prepared(design):
    from streaming_tt_pdn_geometry import admit
    design = Path(design).resolve(); receipt = read(regular(design / 'inputs.json'))
    if receipt.get('schema') == 'pinwheel.streaming-tt-physical-input.v2':
        from streaming_tt_candidate import verify_optimized
        return verify_optimized(design)
    require(receipt.get('schema') == 'pinwheel.streaming-tt-physical-input.v1' and receipt.get('qualified') is False and
        receipt.get('physical_acceptance_claim') is False, 'Invalid prepared physical claim boundary')
    verify_files(design / 'inputs', receipt['input_sha256'])
    verify_files(ROOT, receipt['producer_sha256'])
    require(admit(design / 'inputs/tt_block_6x4_pgvdd.def', design / 'inputs/pdn.tcl') == receipt.get('pdn_geometry_admission') ==
        read(design / 'inputs/pdn-geometry-admission.json'), 'Prepared PDN geometry admission changed')
    validate_config(read(design / 'inputs/core.json'), receipt['depth'])
    require(sha(design / 'inputs/design.v') == receipt['candidate']['verilog_sha256'] and
        sha(design / 'inputs/certified.json') == receipt['candidate']['netlist_sha256'], 'Prepared certificate binding changed')
    verify_pdk(design / 'pdk', read(ROOT / 'tools/physical-toolchain.json'))
    return receipt


def inspect_runtime(lock):
    value = subprocess.run(['docker', 'image', 'inspect', lock['container_tag']], capture_output=True, text=True, timeout=30)
    require(value.returncode == 0, 'Pinned Docker image unavailable: ' + value.stderr.strip())
    image = json.loads(value.stdout)[0]
    config = {key: data for key, data in image['Config'].items() if data is not None}
    config_sha = hashlib.sha256(json.dumps(config, sort_keys=True).encode()).hexdigest()
    require(image['Architecture'] == 'arm64' and image['Os'] == 'linux' and
        image['RootFS']['Layers'] == lock['container_rootfs_diff_ids'] and
        config_sha == lock['container_runtime_config_sha256'], 'Pinned physical runtime identity differs')
    return dict(image_id=image['Id'], architecture=image['Architecture'], os=image['Os'],
        rootfs_diff_ids=image['RootFS']['Layers'], runtime_config_sha256=config_sha)
