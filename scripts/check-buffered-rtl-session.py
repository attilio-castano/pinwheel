#!/usr/bin/env python3
"""Check buffered RTL artifacts in a fresh, retained archive of selected HEAD.

Frontend mode is a component gate. Full mode reconstructs both actual component
certificates, package wiring and initialized session corollaries. Every proof is checked by the pinned native Lean;
the emitter, CIRCT and SMT solver supply artifacts or proof hints only.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import sys
import tarfile
import time
import types

ROOT = Path(__file__).resolve().parents[1]
DRIVER = 'scripts/check-buffered-rtl-session.py'
REQUIRED = frozenset((DRIVER, 'lean-toolchain', 'lakefile.toml', 'lake-manifest.json',
    'tools/hardware-toolchain.json', 'scripts/buffered_serial_readback.py',
    'scripts/paired_readback.py', 'scripts/backend_readback.py', 'scripts/validation_run.py',
    'scripts/process_group.py', 'test/SerialArtifactEmit.lean', 'test/ProofAudit.lean',
    'test/test_buffered_serial_readback.py', 'test/test_buffered_rtl_session.py'))
SCHEMA = 'pinwheel.buffered-rtl-session.frontend.v1'
BUILD_ROOTS = ('Pinwheel.Hardware.Buffered.Serial',
               'Pinwheel.Hardware.Buffered.ArtifactPackage',
               'Pinwheel.Hardware.Readback.Boolean')
REQUIRED_TARGETS = ('Serial.next_correct: all 13 register fields',
                    'Serial.output_correct: all 19 output fields',
                    'Serial.behavior', 'all loaded Pinwheel constants including private declarations',
                    'one injected custom axiom rejection', 'unchanged universal RTL reimport',
                    'five distinguishing actual-Verilog mutation rejections')
FULL_REQUIRED = frozenset(('scripts/buffered_rtl_session_full.py',
    'scripts/buffered_sram_readback.py', 'scripts/buffered_sram_reference.py',
    'scripts/buffered_reactive_reference.py', 'scripts/buffered_sram_selection.py',
    'scripts/buffered_sram_mutations.py', 'scripts/artifact_wrapper_readback.py',
    'test/SramArtifactEmit.lean', 'test/test_buffered_sram_readback.py',
    'test/test_buffered_sram_reference.py', 'test/test_buffered_sram_selection.py',
    'test/test_buffered_sram_mutations.py',
    'test/test_artifact_wrapper_readback.py',
    'physical/buffered_sram_serial_wrapper.sv', 'physical/buffered_sram_memory.sv',
    'physical/tt_um_pinwheel_buffered.sv'))


def full_module():
    scripts = str(ROOT / 'scripts')
    if scripts not in sys.path:
        sys.path.insert(0, scripts)
    import buffered_rtl_session_full
    return buffered_rtl_session_full


def mode_contract(mode):
    if mode == 'frontend':
        return SCHEMA, list(REQUIRED_TARGETS), False
    if mode == 'full':
        return 'pinwheel.buffered-rtl-session.full.v1', list(full_module().FULL_TARGETS), True
    raise RuntimeError('Unknown artifact acceptance mode: ' + str(mode))


def check_worker_contract(child, mode, head, hashes):
    schema, targets, full = mode_contract(mode)
    if (child.get('schema') != schema or child.get('source_commit') != head or
            child.get('source_sha256') != hashes or child.get('full_session_proved') is not full or
            child.get('required_targets') != targets or not child.get('passed')):
        raise RuntimeError('Worker report does not match the selected ' + mode + ' contract')


def digest(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()


def write_json(path, value):
    path = Path(path)
    temporary = path.with_name(path.name + '.tmp')
    temporary.write_text(json.dumps(value, indent=2) + '\n')
    temporary.replace(path)


def load_commands(root):
    """Compile selected helper bytes directly, without borrowing Python pyc."""
    loaded = {}
    for name in ('process_group', 'validation_run'):
        path = Path(root) / 'scripts' / (name + '.py')
        data = path.read_bytes()
        loaded[str(path.relative_to(root))] = hashlib.sha256(data).hexdigest()
        module = types.ModuleType(name)
        module.__file__ = str(path)
        sys.modules[name] = module
        exec(compile(data, str(path), 'exec'), module.__dict__)
    return sys.modules['validation_run'], loaded


def check_environment(environment=None):
    environment = os.environ if environment is None else environment
    fixed = {'LEAN_PATH', 'LEAN_SRC_PATH', 'LEAN_SYSROOT', 'LAKE_HOME',
             'LAKE_PACKAGES_DIR', 'LAKE_CACHE_DIR', 'LD_PRELOAD', 'LD_LIBRARY_PATH'}
    bad = sorted(key for key, value in environment.items()
                 if value and (key in fixed or key.startswith('DYLD_')))
    if bad:
        raise RuntimeError('Refuse compiler/cache/loader environment overrides: ' + ', '.join(bad))


def parse_tree(text):
    tree = {}
    for item in text.split('\0'):
        if not item:
            continue
        metadata, path = item.split('\t', 1)
        mode, kind, oid = metadata.split()
        if path in tree or '\n' in path or '\r' in path:
            raise RuntimeError('Ambiguous selected Git path')
        tree[path] = dict(mode=mode, kind=kind, oid=oid)
    return tree


def select_inputs(tree, mode='frontend'):
    mode_contract(mode)
    paths = set(REQUIRED) | (set(FULL_REQUIRED) if mode == 'full' else set())
    paths.update(path for path in tree if path == 'Pinwheel.lean' or
                 path.startswith('Pinwheel/') and path.endswith('.lean') or
                 path.startswith('scripts/') and path.endswith('.py'))
    missing = paths - tree.keys()
    if missing:
        raise RuntimeError('Required input is not committed: ' + ', '.join(sorted(missing)))
    for path in paths:
        if tree[path]['kind'] != 'blob' or tree[path]['mode'] not in ('100644', '100755'):
            raise RuntimeError('Selected source is not a regular committed file: ' + path)
    return tuple(sorted(paths))


def source_identity(root, tree, paths, object_format):
    """Bind exact file bytes to the selected Git tree, not a mutable HEAD label."""
    result = {}
    for relative in paths:
        path = Path(root) / relative
        if path.is_symlink() or not path.is_file() or not path.resolve().is_relative_to(Path(root).resolve()):
            raise RuntimeError('Missing or redirected selected source: ' + relative)
        data = path.read_bytes()
        oid = hashlib.new(object_format, f'blob {len(data)}\0'.encode() + data).hexdigest()
        if oid != tree[relative]['oid']:
            raise RuntimeError('Input differs from selected committed source: ' + relative)
        result[relative] = hashlib.sha256(data).hexdigest()
    return result


def check_source_hashes(root, expected):
    for relative, value in expected.items():
        path = Path(root) / relative
        if path.is_symlink() or not path.is_file() or digest(path) != value:
            raise RuntimeError('Frozen source changed: ' + relative)


def assert_fresh_snapshot(snapshot):
    if any((Path(snapshot) / name).exists() for name in ('.git', '.lake', 'build')):
        raise RuntimeError('Archive contains prior Git/build/cache state')
    if any(Path(snapshot).rglob('*.olean')) or any(Path(snapshot).rglob('*.pyc')):
        raise RuntimeError('Archive contains a compiled proof or Python cache')


def tool_identity(paths, manifest):
    """Fingerprint wrappers, payloads and a conservative bundled runtime set."""
    tools = {name: Path(path) for name, path in paths.items()}
    if any(not p.is_absolute() for p in tools.values()):
        raise RuntimeError('All selected tool paths must be absolute')
    packages = manifest['packages']
    circt_root = tools['circt'].parent.parent
    oss_root = tools['yosys'].parent.parent
    if (tools['circt'].name != 'circt-opt' or circt_root.name != packages['circt']['directory'] or
            tools['yosys'].name != 'yosys' or tools['solver'] != oss_root / 'bin/z3' or
            oss_root.name != packages['oss-cad-suite']['directory']):
        raise RuntimeError('Selected tool paths do not match the pinned package layout')
    lean_root = tools['lean'].parent.parent
    if tools['lake'] != lean_root / 'bin/lake':
        raise RuntimeError('Lake and Lean must come from one native toolchain')
    expected_roots = dict(circt=circt_root, yosys=oss_root, solver=oss_root,
                          lean=lean_root, lake=lean_root)
    for name, package in expected_roots.items():
        if not tools[name].resolve().is_relative_to(package.resolve()):
            raise RuntimeError('Selected executable escapes its package: ' + name)
    native_magic = tools['lean'].read_bytes()[:4]
    if native_magic not in (b'\xcf\xfa\xed\xfe', b'\xfe\xed\xfa\xcf', b'\xca\xfe\xba\xbe', b'\x7fELF'):
        raise RuntimeError('Selected Lean is not a native executable')
    indexed = set(tools.values())
    for relative in ('libexec/yosys', 'libexec/z3', 'libexec/realpath'):
        indexed.add(oss_root / relative)
    roots = (circt_root, oss_root, lean_root)
    for package in roots:
        indexed.update((package / 'lib').glob('*.dylib'))
        indexed.update((package / 'lib').glob('*.so*'))
    indexed.update((lean_root / 'lib/lean').glob('*.dylib'))
    indexed.update((lean_root / 'lib/lean').glob('*.so*'))
    files = {}
    for path in sorted(indexed):
        if not path.is_file():
            raise RuntimeError('Missing selected tool dependency: ' + str(path))
        if path not in tools.values() and not any(path.resolve().is_relative_to(p.resolve()) for p in roots):
            raise RuntimeError('Tool dependency escapes its selected package: ' + str(path))
        files[str(path)] = dict(sha256=digest(path), resolved=str(path.resolve()))
    archives = {}
    for key, package_root in (('circt', circt_root), ('oss-cad-suite', oss_root)):
        package = packages[key]
        archive = package_root.parent / package['archive']
        if not archive.is_file() or digest(archive) != package['sha256']:
            raise RuntimeError('Missing or changed pinned official tool archive: ' + str(archive))
        archives[str(archive)] = package['sha256']
    return dict(files=files, archives=archives,
        scope='Selected native executables, OSS wrappers and realpath helper, all top-level bundled '
              'CIRCT/OSS/Lean dynamic libraries, Lean lib/lean dynamic libraries, and pinned archives. '
              'OS libraries, shell utilities and Python standard library remain host trust assumptions.',
        installed_payload_archive_membership_proved=False)


def check_versions(versions, expected_lean, manifest):
    if expected_lean != '4.33.1' or not re.search(
            r'Lean \(version ' + re.escape(expected_lean) + r'(?:,|\s)', versions['lean']):
        raise RuntimeError('Expected native Lean 4.33.1 matching lean-toolchain')
    if 'CIRCT ' + manifest['packages']['circt']['release'] not in versions['circt']:
        raise RuntimeError('Unexpected CIRCT version')
    if not versions['yosys'].startswith('Yosys 0.69+24 (git sha1 d0e71cfb7-dirty,'):
        raise RuntimeError('Unexpected Yosys version')
    if versions['solver'].strip() != 'Z3 version 4.15.5 - 64 bit':
        raise RuntimeError('Unexpected Z3 version')


def imports(path):
    result = []
    for line in Path(path).read_text().splitlines():
        match = re.match(r'^\s*(?:(?:public|private|meta)\s+)*import\s+(.+)', line)
        if not match:
            continue
        for module in match[1].split('--', 1)[0].split():
            if not re.fullmatch(r'[A-Za-z_][A-Za-z0-9_\']*(?:\.[A-Za-z_][A-Za-z0-9_\']*)*', module):
                raise RuntimeError('Unsupported Lean import spelling in ' + str(path))
            result.append(module)
    return result


def proof_closure(snapshot, generated, roots, committed, frozen_generated):
    """Reject local proof dependencies absent from either frozen input set."""
    snapshot = Path(snapshot)
    generated_roots = [Path(path) for path in generated] if isinstance(generated, (list, tuple)) else [Path(generated)]
    seen, queue = {}, list(roots)
    while queue:
        module = queue.pop()
        if module in seen:
            continue
        relative = module.replace('.', '/') + '.lean'
        source = snapshot / relative
        artifacts = [directory / relative for directory in generated_roots if (directory / relative).is_file()]
        if source.is_file():
            if relative not in committed or digest(source) != committed[relative]:
                raise RuntimeError('Uncommitted or changed proof dependency: ' + relative)
            path, origin = source, 'committed'
        elif artifacts:
            if len(artifacts) != 1:
                raise RuntimeError('Ambiguous generated proof dependency: ' + relative)
            artifact = artifacts[0]
            if relative not in frozen_generated or digest(artifact) != frozen_generated[relative]:
                raise RuntimeError('Unfrozen generated proof dependency: ' + relative)
            path, origin = artifact, 'generated'
        elif module.split('.')[0] in ('Init', 'Lean', 'Std', 'Lake'):
            seen[module] = dict(origin='pinned Lean toolchain')
            continue
        else:
            raise RuntimeError('Missing indexed proof dependency: ' + module)
        allowed = [snapshot] if origin == 'committed' else generated_roots
        if path.is_symlink() or not any(path.resolve().is_relative_to(directory.resolve()) for directory in allowed):
            raise RuntimeError('Redirected proof dependency: ' + str(path))
        seen[module] = dict(origin=origin, sha256=digest(path))
        queue.extend(imports(path))
    return dict(sorted(seen.items()))


def file_hashes(root, paths=None):
    root = Path(root)
    selected = sorted(root.rglob('*')) if paths is None else sorted(paths)
    result = {}
    for path in selected:
        if path.is_file():
            if path.is_symlink() or not path.resolve().is_relative_to(root.resolve()):
                raise RuntimeError('Artifact escapes retained directory: ' + str(path))
            result[str(path.relative_to(root))] = digest(path)
    return result


def assert_hashes(root, frozen):
    for relative, value in frozen.items():
        path = Path(root) / relative
        if not path.is_file() or path.is_symlink() or digest(path) != value:
            raise RuntimeError('Frozen artifact changed: ' + relative)


def freeze_inputs(report, root, paths):
    """Record first-created bytes before any consuming command or parser."""
    frozen = file_hashes(root, paths)
    previous = report.setdefault('proof_input_sha256_before', {})
    for path, value in frozen.items():
        if path in previous and previous[path] != value:
            raise RuntimeError('Already frozen proof input changed before reuse: ' + path)
    previous.update(frozen)
    return frozen


def compile_lean(run, tools, directory, name, *, reject=None, paths=()):
    # A fresh archive plus an explicit Lean path prevents borrowing workspace
    # oleans. Lake supplies only this archive's .lake and the pinned stdlib.
    return run(['env', 'LEAN_PATH=' + os.pathsep.join(map(str, [directory, *paths])), tools['lake'], 'env', 'lean',
                '--root=' + str(directory), '-DwarningAsError=true', '-DmaxErrors=1', '-o', directory / (name + '.olean'),
                directory / (name + '.lean')], name, timeout=900, reject=reject)


def import_rtl(run, rb, tools, directory, sv, label, *, freeze=None):
    script = directory / (label + '.ys')
    candidate = directory / (label + '.json')
    script.write_text('\n'.join([f'read_verilog -sv "{sv}"',
        f'hierarchy -check -top {rb.TOP}', 'proc', 'pmuxtree', 'opt_clean',
        'check -assert', f'write_json "{candidate}"', '']))
    if freeze:
        freeze([sv, script])
    run([tools['yosys'], '-Q', '-T', '-s', script], label, timeout=120)
    if freeze:
        freeze([candidate])
    import paired_readback
    paired_readback.read_json(candidate)
    return rb.read_rtl(candidate), candidate


def audit_source(template, proof_modules, root_module='SerialProof'):
    """Audit declaration ownership, including private generated helpers.

    Native Lean's own elaborator internals contain implementation axioms. They
    are outside the component proof roots. Module ownership avoids confusing
    those internals with a private helper from a generated certificate module.
    """
    source = template.replace('import Pinwheel\n', 'import ' + root_module + '\n')
    old = '    if text.startsWith "Pinwheel." || text.startsWith "_private.Pinwheel." then'
    modules = ', '.join(json.dumps(name) for name in sorted(proof_modules))
    replacement = '''    let owned := match env.getModuleIdxFor? name with
      | some idx =>
        let owner := env.header.modules[idx.toNat]!.module.toString
        owner == "Pinwheel" || owner.startsWith "Pinwheel." ||
          (#[MODULES] : Array String).contains owner
      | none => info.isAxiom || info.isTheorem
    if owned then'''.replace('MODULES', modules)
    if source == template or old not in source:
        raise RuntimeError('Unsupported axiom audit template; refuse a partial audit')
    return source.replace('    let text := name.toString\n', '').replace(old, replacement)


def frontend_worker(config, run, report, *, inject_axiom=True):
    import buffered_serial_readback as sr
    snapshot, out = Path(config['snapshot']), Path(config['worker_out'])
    tools = config['tool_paths']
    report['build_roots'] = list(BUILD_ROOTS)
    run([tools['lake'], 'build', *BUILD_ROOTS], 'fresh-component-build', timeout=1800)
    run([sys.executable, '-B', 'test/test_buffered_serial_readback.py'], 'adapter-boundary-tests', timeout=60)
    run([sys.executable, '-B', 'test/test_buffered_rtl_session.py'], 'provenance-boundary-tests', timeout=120)
    emitted, generated = out / 'emitted', out / 'proof'
    emitted.mkdir()
    generated.mkdir()
    run([tools['lake'], 'env', 'lean', '-DwarningAsError=true', '--run',
         'test/SerialArtifactEmit.lean', emitted], 'emit-frontend', timeout=300)
    freeze = lambda paths: freeze_inputs(report, out, paths)
    freeze(emitted.rglob('*'))
    sv = emitted / 'frontend.sv'
    text = run([tools['circt'], emitted / 'frontend.mlir', '--canonicalize', '--lower-seq-to-sv',
                '--lower-hw-to-sv', '--hw-legalize-modules', '--export-verilog', '-o', '/dev/null'],
               'circt-export', timeout=120)
    sv.write_text(text)
    freeze([sv])
    rb = sr.backend()
    sr.check_interface(rb, emitted / 'assembly.json')
    source = rb.read_hints(emitted / 'frontend.mlir')
    rtl, imported = import_rtl(run, rb, tools, generated, sv, 'import-frontend', freeze=freeze)
    queries = out / 'smt-proposals'
    queries.mkdir()
    count = 0
    def recorded_oracle(solver):
        def query(pair):
            nonlocal count
            count += 1
            label = f'smt-proposal-{count:05d}'
            path = queries / (label + '.smt2')
            path.write_text(rb.smt_suggestion(pair))
            freeze([path])
            output = run([solver, '-smt2', path, '-T:3'], label, timeout=5)
            return output.strip() == 'unsat'
        return query
    rb.cut_oracle = recorded_oracle
    pairs = sr.partitions(rb, source, rtl, tools['solver'])
    write_json(out / 'partitions.json', pairs)
    texts = sr.generate(rb, source, rtl, pairs, prefix='Serial')
    audit_template = (snapshot / 'test/ProofAudit.lean').read_text()
    proof_modules = set(texts)
    audit = audit_source(audit_template, proof_modules)
    texts['SerialAudit'] = audit
    audit_roots = ['SerialProof', 'SerialAudit', *BUILD_ROOTS]
    if inject_axiom:
        texts['SerialPrivateAxiomControl'] = 'import Init\nprivate axiom untrustedBufferedRtlSession : False\n'
        texts['SerialRejectAxiom'] = audit_source(audit_template, proof_modules | {'SerialPrivateAxiomControl'}).replace(
            'import SerialProof\n', 'import SerialProof\nimport SerialPrivateAxiomControl\n')
        audit_roots.append('SerialRejectAxiom')
    for name, value in texts.items():
        (generated / (name + '.lean')).write_text(value)
    frozen_generated = {p.name: digest(p) for p in generated.glob('*.lean')}
    report['proof_dependency_closure'] = proof_closure(snapshot, generated,
        audit_roots, config['source_sha256'], frozen_generated)
    freeze([*emitted.rglob('*'), imported,
        *(generated / (name + '.lean') for name in texts)])
    frozen_inputs = report['proof_input_sha256_before']
    report['smt_proposal_commands'] = count
    report['partitions'] = len(pairs)
    for name in ('SerialHints', 'SerialSources', 'SerialGraphs', 'SerialLocalProofs',
                 'SerialLinks', 'SerialModel', 'SerialEndpoints', 'SerialProof', 'SerialAudit'):
        output = compile_lean(run, tools, generated, name)
        if name == 'SerialAudit':
            matches = re.findall(r'Pinwheel audit: (\d+) declarations, (\d+) theorems; standard axioms only\.', output)
            if len(matches) != 1:
                raise RuntimeError('Missing unambiguous all-constant/private axiom audit result')
            report['audited_declarations'], report['audited_theorems'] = map(int, matches[0])
    if inject_axiom:
        compile_lean(run, tools, generated, 'SerialPrivateAxiomControl')
        rejected = compile_lean(run, tools, generated, 'SerialRejectAxiom',
            reject='Unapproved axioms in _private.')
        if 'untrustedBufferedRtlSession' not in rejected:
            raise RuntimeError('Private axiom control was rejected for an unrelated declaration')
    report['injected_axiom_rejections'] = int(inject_axiom)
    mutations = []
    for label, pattern, replacement, operation, port in sr.mutation_specs():
        directory = out / 'mutations' / label
        directory.mkdir(parents=True)
        candidate = directory / 'candidate.sv'
        value = sv.read_text()
        if pattern:
            value, changes = re.subn(pattern, replacement, value)
            if changes != 1:
                raise RuntimeError('Mutation must change exactly one actual RTL use: ' + label)
        candidate.write_text(value)
        freeze([candidate])
        actual, _ = import_rtl(run, rb, tools, directory, candidate, 'mutation-' + label, freeze=freeze)
        if pattern is None and (actual.nodes != rtl.nodes or actual.next != rtl.next or actual.outputs != rtl.outputs):
            raise RuntimeError('Unchanged reimport altered the complete imported graph')
        mutation_texts = sr.mutation_sources(rb, actual, operation, port, prefix='Serial')
        for name, value in mutation_texts.items():
            (directory / (name + '.lean')).write_text(value)
        mutation_roots = ['SerialMutantModel', 'SerialReject']
        if pattern is None:
            universal = ('import SerialProof\nimport SerialMutantModel\n' + rb.HEADER + '''
theorem unchanged_next (i : Values Serial.Input) (s : Values Serial.Register)
    (r : Serial.Register w) : mutantStep i s r = Serial.circuit.step i s r := by
  exact next_correct i s r
theorem unchanged_output (i : Values Serial.Input) (s : Values Serial.Register)
    (o : Serial.Output w) : mutantObserve i s o = Serial.circuit.observe i s o := by
  exact output_correct i s o
end Pinwheel.Artifact.Buffered.Serial
''')
            (directory / 'SerialUnchanged.lean').write_text(universal)
            mutation_roots.append('SerialUnchanged')
        mutation_frozen = {**frozen_generated, **{p.name: digest(p) for p in directory.glob('*.lean')}}
        report.setdefault('mutation_proof_closures', {})[label] = proof_closure(
            snapshot, [directory, generated], mutation_roots, config['source_sha256'], mutation_frozen)
        freeze([p for p in directory.iterdir() if p.suffix in ('.sv', '.ys', '.json', '.lean')])
        def mutant_check(name, reject=None):
            return run(['env', 'LEAN_PATH=' + str(directory) + ':' + str(generated), tools['lake'],
                'env', 'lean', '--root=' + str(directory), '-DwarningAsError=true', '-DmaxErrors=1', '-o',
                directory / (name + '.olean'), directory / (name + '.lean')],
                label + '-' + name, timeout=120, reject=reject)
        for name in ('SerialMutantGraphs', 'SerialMutantModel'):
            mutant_check(name)
        if pattern is None:
            mutant_check('SerialUnchanged')
            mutant_check('SerialReject')
        else:
            mutant_check('SerialReject', reject='error: Type mismatch')
        mutations.append(dict(name=label, status='passed',
            all_state_reimport=pattern is None, expected_rejection=pattern is not None))
    report['mutations'] = mutations
    assert_hashes(out, frozen_inputs)
    report['proof_input_sha256_after'] = {relative: digest(out / relative) for relative in frozen_inputs}
    current_closure = proof_closure(snapshot, generated, audit_roots,
                                  config['source_sha256'], frozen_generated)
    if current_closure != report['proof_dependency_closure']:
        raise RuntimeError('Generated proof dependency closure changed')
    report.update(frontend_registers=len(rb.REGISTERS), frontend_state_bits=sum(w for w, _ in rb.REGISTERS.values()),
                  frontend_outputs=len(rb.OUTPUTS), proof_inputs_unchanged=True)


def worker(config_path):
    config = json.loads(Path(config_path).read_text())
    snapshot, out = Path(config['snapshot']), Path(config['worker_out'])
    out.mkdir(parents=True, exist_ok=False)
    logs = out / 'logs'
    logs.mkdir()
    module, loaded = load_commands(snapshot)
    run = module.Commands(snapshot, logs, default_timeout=900)
    mode = config.get('mode', 'frontend')
    schema, targets, _ = mode_contract(mode)
    report = dict(schema=schema, mode=mode, passed=False, standalone_qualification=False,
        source_commit=config['source_commit'], source_sha256=config['source_sha256'], commands=run.records,
        full_session_proved=False, required_targets=targets)
    started = time.monotonic()
    failure = None
    try:
        check_environment()
        assert_fresh_snapshot(snapshot)
        check_source_hashes(snapshot, config['source_sha256'])
        if any(config['source_sha256'].get(name) != value for name, value in loaded.items()):
            raise RuntimeError('Loaded validation helper differs from committed input')
        manifest = json.loads((snapshot / 'tools/hardware-toolchain.json').read_text())
        if json.loads((snapshot / 'lake-manifest.json').read_text()).get('packages'):
            raise RuntimeError('This no-shared-cache gate expects no external Lake packages')
        observed = tool_identity(config['tool_paths'], manifest)
        if observed != config['tool_identity']:
            raise RuntimeError('Tool identity changed before worker use')
        tools = config['tool_paths']
        versions = {name: run([tools[name], *flags], name + '-version', timeout=30).strip()
                    for name, flags in [('lean', ['--version']), ('lake', ['--version']),
                                        ('circt', ['--version']), ('yosys', ['-V']), ('solver', ['-version'])]}
        expected = (snapshot / 'lean-toolchain').read_text().strip().split(':v')[-1]
        check_versions(versions, expected, manifest)
        report['tool_versions'] = versions
        selected_lean = run([tools['lake'], 'env', 'which', 'lean'], 'lake-selected-lean', timeout=30).strip()
        if Path(selected_lean).resolve() != Path(tools['lean']).resolve():
            raise RuntimeError('Lake does not execute the fingerprinted native Lean')
        search = run([tools['lake'], 'env', 'printenv', 'LEAN_PATH'], 'lake-proof-search-path', timeout=30).strip()
        allowed = {str(snapshot / '.lake/build/lib/lean'), str(Path(tools['lean']).parent.parent / 'lib/lean')}
        if set(search.split(os.pathsep)) != allowed:
            raise RuntimeError('Lake proof search path includes an unselected cache')
        report['base_lean_search_path'] = search.split(os.pathsep)
        if mode == 'frontend':
            frontend_worker(config, run, report)
        else:
            full_module().full_worker(config, run, report, sys.modules[__name__])
        report['passed'] = True
    except BaseException as error:
        failure = error
        report['error'] = type(error).__name__ + ': ' + str(error)
    finally:
        post_errors = []
        try:
            check_source_hashes(snapshot, config['source_sha256'])
            report['archived_inputs_unchanged'] = True
        except Exception as error:
            post_errors.append(str(error))
        try:
            if tool_identity(config['tool_paths'], json.loads((snapshot / 'tools/hardware-toolchain.json').read_text())) != config['tool_identity']:
                raise RuntimeError('Tool identity changed during worker execution')
            report['tool_identity_unchanged'] = True
        except Exception as error:
            post_errors.append(str(error))
        if post_errors:
            report.update(passed=False, postcheck_errors=post_errors)
        frozen = report.get('proof_input_sha256_before')
        if frozen:
            try:
                assert_hashes(out, frozen)
                report['proof_input_sha256_after'] = {relative: digest(out / relative) for relative in frozen}
            except Exception as error:
                report.update(passed=False, artifact_closeout_error=str(error))
        report['elapsed_seconds'] = round(time.monotonic() - started, 3)
        try:
            report['artifact_sha256'] = file_hashes(out)
            report['fresh_olean_sha256'] = file_hashes(snapshot, (snapshot / '.lake').rglob('*.olean'))
        except Exception as error:
            report.update(passed=False, artifact_inventory_error=str(error))
        if not report['passed']:
            report['full_session_proved'] = False
        write_json(out / 'worker-report.json', report)
    if failure is not None:
        raise failure
    if not report['passed']:
        raise RuntimeError('Worker closeout rejected the run')


def coordinator(args):
    module, loaded = load_commands(ROOT)
    out = module.fresh_directory(ROOT / 'build/validation', args.tag)
    logs = out / 'coordinator-logs'
    logs.mkdir()
    run = module.Commands(ROOT, logs, default_timeout=60)
    schema, targets, full = mode_contract(args.mode)
    boundary = ('Component-only: exact selected raw buffered serial frontend RTL, all 13 register fields '
        'and 19 output fields for arbitrary two-state inputs/state. No full initialized source session theorem. '
        if not full else
        'Both exact raw component RTL recurrences, actual parsed package/memory/Tiny Tapeout wiring, '
        'all finite pin histories and initialized repeated/interrupted carried source sessions, including '
        'every Fin256 duration/budget pair and heterogeneous reloads of statically certified program images. '
        'Closed synchronous digital memory specializations and generic '
        'exact-implementation memory-law corollaries; no electrical SRAM macro claim. ')
    boundary += ('No synthesis/ABC, physical timing or generic Verilog/CIRCT compiler proof. '
        'Yosys SV/proc interpretation and restricted artifact adapters remain explicit trust boundaries.')
    report = dict(schema=schema, passed=False, full_session_proved=False, mode=args.mode,
        started_utc=datetime.now(timezone.utc).isoformat(), required_targets=targets,
        coordinator_commands=run.records, producer_workspace='Fresh retained Git archive; no shared .lake/build cache',
        boundary=boundary)
    started = time.monotonic()
    tree, paths, object_format, source_hashes, tool_before = None, None, None, None, None
    failure = None
    try:
        check_environment()
        head = run(['git', 'rev-parse', 'HEAD'], 'selected-head').strip()
        if not re.fullmatch(r'[0-9a-f]{40}|[0-9a-f]{64}', head):
            raise RuntimeError('Invalid selected Git commit')
        tree = parse_tree(run(['git', 'ls-tree', '-r', '-z', head], 'selected-tree'))
        object_format = run(['git', 'rev-parse', '--show-object-format'], 'git-object-format').strip()
        paths = select_inputs(tree, args.mode)
        source_hashes = source_identity(ROOT, tree, paths, object_format)
        if any(source_hashes.get(name) != value for name, value in loaded.items()):
            raise RuntimeError('Loaded validation helper differs from selected commit')
        report.update(source_commit=head, source_sha256=source_hashes,
                      selected_git_objects={path: tree[path]['oid'] for path in paths},
                      committed_input_membership_verified_before=True)
        archive = out / 'selected-source.tar'
        run(['git', 'archive', '--format=tar', '--output', archive, head, '--', *paths], 'selected-archive')
        report['snapshot_archive_sha256'] = digest(archive)
        snapshot = out / 'snapshot'
        snapshot.mkdir()
        with tarfile.open(archive) as bundle:
            bundle.extractall(snapshot, filter='data')
        assert_fresh_snapshot(snapshot)
        check_source_hashes(snapshot, source_hashes)
        lake_proxy = shutil.which('lake')
        if not lake_proxy:
            raise RuntimeError('Pinned Lake/Lean must be installed')
        prefix = Path(run([lake_proxy, 'env', 'lean', '--print-prefix'], 'native-toolchain-prefix').strip())
        tools = dict(circt=str(Path(args.circt).absolute()), yosys=str(Path(args.yosys).absolute()),
                     solver=str(Path(args.solver).absolute()), lean=str(prefix / 'bin/lean'),
                     lake=str(prefix / 'bin/lake'), python=str(Path(sys.executable).resolve()))
        manifest = json.loads((snapshot / 'tools/hardware-toolchain.json').read_text())
        tool_before = tool_identity(tools, manifest)
        report.update(tool_paths=tools, tool_identity_before=tool_before,
                      discovery_lake_proxy=dict(path=lake_proxy, sha256=digest(lake_proxy)))
        config = dict(mode=args.mode, snapshot=str(snapshot), worker_out=str(out / 'worker'), source_commit=head,
                      source_sha256=source_hashes, tool_paths=tools, tool_identity=tool_before)
        config_path = out / 'worker-config.json'
        write_json(config_path, config)
        print('Fresh committed ' + args.mode + ' artifact gate: ' + head, flush=True)
        run([sys.executable, '-B', snapshot / DRIVER, '--worker-config', config_path],
            'snapshot-worker', timeout=args.timeout_seconds)
        child = json.loads((out / 'worker/worker-report.json').read_text())
        check_worker_contract(child, args.mode, head, source_hashes)
        report['worker'] = child
        report['passed'] = True
        report['full_session_proved'] = full
    except BaseException as error:
        failure = error
        report['error'] = type(error).__name__ + ': ' + str(error)
    finally:
        post_errors = []
        if source_hashes is not None:
            try:
                if source_identity(ROOT, tree, paths, object_format) != source_hashes:
                    raise RuntimeError('Selected working inputs changed during validation')
                report['committed_input_membership_verified_after'] = True
            except Exception as error:
                post_errors.append(str(error))
        if tool_before is not None:
            try:
                current = tool_identity(report['tool_paths'], json.loads((ROOT / 'tools/hardware-toolchain.json').read_text()))
                if current != tool_before:
                    raise RuntimeError('Selected tool inventory or bytes changed during validation')
                report['tool_identity_after'] = current
                report['tool_identity_unchanged'] = True
            except Exception as error:
                post_errors.append(str(error))
        if post_errors:
            report.update(passed=False, postcheck_errors=post_errors)
        report['elapsed_seconds'] = round(time.monotonic() - started, 3)
        try:
            report['artifact_sha256'] = file_hashes(out, [p for p in out.rglob('*') if p != out / 'report.json'])
        except Exception as error:
            report.update(passed=False, artifact_inventory_error=str(error))
        if not report['passed']:
            report['full_session_proved'] = False
        write_json(out / 'report.json', report)
    if failure is not None:
        raise failure
    if not report['passed']:
        raise RuntimeError('Final source/tool closeout rejected the run')
    print(args.mode.capitalize() + ' artifact receipt: ' + str(out / 'report.json'), flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--tag')
    parser.add_argument('--mode', choices=['frontend', 'full'], default='frontend')
    parser.add_argument('--circt', help='Absolute selected pinned circt-opt executable')
    parser.add_argument('--yosys', help='Absolute selected pinned Yosys wrapper')
    parser.add_argument('--solver', help='Absolute selected pinned Z3 wrapper')
    parser.add_argument('--timeout-seconds', type=int, default=7200)
    parser.add_argument('--worker-config', help=argparse.SUPPRESS)
    args = parser.parse_args()
    if args.worker_config:
        worker(args.worker_config)
        return
    if not args.tag or not all((args.circt, args.yosys, args.solver)):
        parser.error('--tag, --circt, --yosys and --solver are required')
    if any(not Path(path).is_absolute() for path in (args.circt, args.yosys, args.solver)):
        parser.error('Pass explicit absolute tool paths')
    if args.timeout_seconds <= 0 or args.timeout_seconds > 43200:
        parser.error('Worker timeout must be between 1 and 43200 seconds')
    coordinator(args)


if __name__ == '__main__':
    main()
