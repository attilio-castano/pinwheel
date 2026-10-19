"""Fresh mapped-component development worker; never a master qualification gate.

The caller owns committed-archive membership and the upstream SV/importer link.
This worker freezes every consumed artifact, compiles its generated proofs and
refuses a whole-device pass until both component and wrapper joins are checked.
"""
from copy import deepcopy
from datetime import datetime, timezone
from hashlib import sha256
import importlib
import json
import os
from pathlib import Path
import re
import sys
import time

from validation_run import Commands
from streaming_mapped_liberty import LIBRARY_SHA256, load_library, require
from streaming_mapped_netlist import load_mapped
from streaming_mapped_flow import mapping_script, source_state, state_inventory
from streaming_mapped_hierarchy import ARITHMETIC, FA, hierarchical_source
from streaming_mapped_arithmetic import generate_arithmetic
from streaming_mapped_certificate import bitwise_source, generate_full_adder, namespace_name
from streaming_mapped_reductions import REDUCTIONS, generate_reduction
import streaming_ready_readback

SCHEMA = 'pinwheel.streaming-mapped-campaign.v1'
LABELS = ('frontend', 'core-d2', 'core-d4')
BUILD_ROOTS = ('Pinwheel.Hardware.StreamingMapped.Comparison',
    'Pinwheel.Hardware.StreamingMapped.ReductionAnd', 'Pinwheel.Hardware.StreamingMapped.Ports',
    'Pinwheel.Hardware.StreamingMapped.Word', 'Pinwheel.Hardware.StreamingMapped.TinyWiring',
    'Pinwheel.Hardware.StreamingReady.Readback',
    'Pinwheel.Hardware.StreamingReady.Package',
    'Pinwheel.Hardware.StreamingReady.CoreEmit', 'Pinwheel.Hardware.Streaming.FrontendEmit')
BITWISE = frozenset(('$and', '$or', '$xor', '$not', '$mux'))
BOUNDARY = ('Exact unsigned raw word-JSON to interpreted pinned-Liberty mapped digital transitions. '
    'All named source FF bits are preserved. Native Lean checks local word functions and whole-component '
    'joins when available. The caller supplies committed-source membership and the upstream SV/importer '
    'binding. Library Boolean/FF interpretation is an explicit parser/model boundary. '
    'No routing, parasitics, electrical or guaranteed-frequency conclusion.')


def digest(path): return sha256(Path(path).read_bytes()).hexdigest()


def read_json(path):
    def pairs(items):
        result = {}
        for key, value in items:
            require(key not in result, 'Duplicate campaign JSON key')
            result[key] = value
        return result
    return json.loads(Path(path).read_bytes(), object_pairs_hook=pairs)


class Frozen:
    """First hash wins, including re-use within the same command pipeline."""
    def __init__(self): self.files = {}
    def add(self, *paths):
        for path in paths:
            path = Path(path).absolute()
            require(path.is_file() and not path.is_symlink(), 'Expected regular immutable input: ' + str(path))
            value = digest(path)
            require(str(path) not in self.files or self.files[str(path)] == value,
                'Already consumed input changed before reuse: ' + str(path))
            self.files[str(path)] = value
    def verify(self):
        for path, value in self.files.items():
            require(Path(path).is_file() and not Path(path).is_symlink() and digest(path) == value,
                'Consumed input changed at closeout: ' + path)
        return True


def validate_config(config):
    require(type(config) is dict and type(config.get('components')) is dict and
        set(config['components']) == set(LABELS), 'All three exact mapped components are required')
    require(type(config.get('root')) is str and Path(config['root']).is_absolute(), 'Absolute selected source root required')
    require(type(config.get('library')) is str and Path(config['library']).is_absolute(), 'Absolute pinned library required')
    tools = config.get('tools', {})
    require(type(tools) is dict and {'yosys', 'abc', 'lean', 'lake'} <= set(tools) and
        all(type(tools[name]) is str and Path(tools[name]).is_absolute() for name in tools),
        'Explicit absolute native tools required')
    require(type(config.get('timeout', 900)) is int and 1 <= config.get('timeout', 900) <= 43200,
        'Bounded command timeout required')
    for label, component in config['components'].items():
        require(type(component) is dict and all(type(component.get(name)) is str and
            Path(component[name]).is_absolute() for name in ('raw_json', 'sv')), 'Missing exact raw inputs: ' + label)
        for name in ('raw_module', 'raw_namespace'):
            if name in component: namespace_name(component[name])
        if 'raw_sources' in component:
            require({'raw_module','raw_namespace'} <= set(component) and component['raw_module'] in component['raw_sources'],
                'Raw proof root and namespace must bind the supplied source closure')
            require(type(component['raw_sources']) is dict and component['raw_sources'], 'Ordered raw proof source map required')
            for module, path in component['raw_sources'].items():
                namespace_name(module)
                require(type(path) is str and Path(path).is_absolute(), 'Absolute raw proof source required')
    return config


def runtime_files(tools):
    """Selected wrappers, payloads, technology data and native/Lean runtimes."""
    files = set()
    for value in tools.values():
        path = Path(value)
        require(path.is_file(), 'Missing selected native executable')
        files.add(path.resolve())
    oss = Path(tools['yosys']).parent.parent.resolve()
    require(Path(tools['abc']).parent.parent.resolve() == oss, 'ABC and Yosys must share the selected tool package')
    for name in ('yosys', 'yosys-abc', 'realpath'):
        path = oss / 'libexec' / name
        require(path.is_file(), 'Missing selected mapping tool payload: ' + str(path))
        files.add(path.resolve())
    data = oss / 'share/yosys'
    require(data.is_dir(), 'Missing selected mapping technology data')
    files.update(path.resolve() for path in data.rglob('*') if path.is_file())
    lean = Path(tools['lean']).parent.parent.resolve()
    require(Path(tools['lake']).parent.parent.resolve() == lean, 'Lake and Lean must share the selected toolchain')
    for package in (oss, lean):
        for path in (package / 'lib').rglob('*'):
            if path.is_file() and (path.name.endswith('.dylib') or '.so' in path.name or
                package == lean and ('.olean' in path.name or path.name.endswith(('.ir', '.ir.sig')))):
                files.add(path.resolve())
    return sorted(files)


def audit_source(modules):
    imports = '\n'.join('import ' + namespace_name(name) for name in modules)
    owners = ','.join(json.dumps(name) for name in modules)
    return '''import Lean
IMPORTS
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  for (name, info) in env.constants.toList do
    let owned := match env.getModuleIdxFor? name with
      | some idx =>
        let owner := env.header.modules[idx.toNat]!.module.toString
        owner == "Pinwheel" || owner.startsWith "Pinwheel." || (#[OWNERS] : Array String).contains owner
      | none => info.isAxiom || info.isTheorem
    if owned then
      declarations := declarations + 1
      if info.isTheorem then theorems := theorems + 1
      let axioms ← collectAxioms name
      let unexpected := axioms.filter fun ax => ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound
      unless unexpected.isEmpty do throwError "Unapproved axioms in {name}: {unexpected}"
  if declarations == 0 || theorems == 0 then throwError "Empty mapped audit"
  logInfo m!"Mapped audit: {declarations} declarations, {theorems} theorems; standard axioms only."
'''.replace('IMPORTS', imports).replace('OWNERS', owners)


def required_source(rb, module, namespace):
    namespace_name(module); namespace_name(namespace)
    return ('import ' + module + '\n' + rb.HEADER +
        'example (i : Values ' + rb.INPUT_TYPE + ') (s : Values ' + rb.REGISTER_TYPE + ') (r : ' + rb.REGISTER_TYPE + ' w) :\n' +
        '  ' + namespace + '.step i s r = ' + rb.CIRCUIT + '.step i s r := ' + namespace + '.step_correct i s r\n' +
        'example (i : Values ' + rb.INPUT_TYPE + ') (s : Values ' + rb.REGISTER_TYPE + ') (o : ' + rb.OUTPUT_TYPE + ' w) :\n' +
        '  ' + namespace + '.observe i s o = ' + rb.CIRCUIT + '.observe i s o := ' + namespace + '.observe_correct i s o\n' +
        'end ' + rb.NAMESPACE + '\n')


def acceptance(report):
    components = report.get('components', {})
    return (not report.get('error') and set(components) == set(LABELS) and all(
        component.get('local_proofs_checked') is True and component.get('full_component_checked') is True and
        component.get('all_state_bijection') is True and component.get('mutations_checked') is True and
        component.get('whole_component_controls_checked') is True and
        component.get('axiom_audit_checked') is True and component.get('private_axiom_rejected') is True for component in components.values()) and
        report.get('wrapper_checked') is True and report.get('wrapper_axiom_audit_checked') is True and
        report.get('wrapper_private_axiom_rejected') is True and report.get('required_qnames_checked') is True and
        report.get('extra_qnames_checked') is True and
        report.get('frozen_inputs_unchanged') is True)


def verify_qnames(output,qnames):
    require(type(output) is str and type(qnames) is list and len(qnames) == 44 and len(set(qnames)) == 44,
        'Both depths require all44 unique physical/session proof targets')
    for name in qnames:
        namespace_name(name)
        require(len(re.findall(r'(?m)^'+re.escape(name)+r'(?=[\s(:{])',output)) == 1,
            'Missing, duplicate or truncated checked QName: '+name)
    return True


def verify_extra_qnames(output, qnames, required):
    require(type(qnames) is list and len(qnames) == 6 and len(set(qnames)) == 6 and
        not (set(qnames) & set(required)), 'Both depths require six separate first-terminal proof targets')
    for name in qnames:
        namespace_name(name)
        require(len(re.findall(r'(?m)^'+re.escape(name)+r'(?=[\s(:{])',output)) == 1,
            'Missing, duplicate or truncated extra checked QName: '+name)
    return True


class Worker:
    def __init__(self, out, config, run=None):
        self.config = validate_config(deepcopy(config))
        self.root, self.out = Path(config['root']).resolve(), Path(out).resolve()
        self.out.mkdir(parents=True, exist_ok=False)
        self.frozen, self.modules = Frozen(), []
        self.report = dict(schema=SCHEMA, boundary=BOUNDARY, passed=False, full_qualification=False,
            source_commit_hint=config.get('source_commit'), committed_archive_membership_asserted=False,
            started_utc=datetime.now(timezone.utc).isoformat(), components={}, wrapper_checked=False,
            wrapper_axiom_audit_checked=False, commands=[])
        if run is None:
            self.run = Commands(self.root, self.out, self.report['commands'], config.get('timeout', 900))
        else:
            def journal(command, label, timeout=None, reject=None):
                record = dict(label=label, argv=list(map(str,command)), expected_failure=bool(reject), external_runner=True)
                self.report['commands'].append(record)
                started = time.monotonic()
                try:
                    output = run(command,label,timeout=timeout,reject=reject)
                    require(type(output) is str and (reject is None or reject in output), 'External runner omitted required output/rejection')
                    record.update(expected_outcome_completed=True, seconds=round(time.monotonic()-started,3))
                    return output
                except BaseException as error:
                    record.update(error=type(error).__name__, seconds=round(time.monotonic()-started,3))
                    raise
            self.run = journal
        self.tools = self.config['tools']
        self.started = time.monotonic()

    def write(self, path, value):
        path = Path(path)
        require(not path.exists(), 'Preserve earlier generated artifact: ' + str(path))
        path.write_text(value)
        self.frozen.add(path)
        return path

    def compile(self, directory, name, text, *, paths=(), reject=None, label=None, fixture=False):
        namespace_name(name)
        source = self.write(Path(directory) / (name + '.lean'), text)
        self.frozen.add(source)
        search = os.pathsep.join(map(str, [directory, *paths, self.root / '.lake/build/lib/lean']))
        result = self.run(['env', 'LEAN_PATH=' + search, self.tools['lean'], '--root=' + str(directory),
            '-DwarningAsError=true', '-DmaxErrors=1', '-o', Path(directory) / (name + '.olean'), source],
            label or name, timeout=self.config.get('timeout', 900), reject=reject)
        if reject is None:
            self.frozen.add(Path(directory) / (name + '.olean'))
            if not fixture: self.modules.append(dict(directory=str(directory), module=name))
        return result

    def intake(self):
        self.write(self.out/'config.json', json.dumps(self.config,indent=2)+'\n')
        for component in self.config['components'].values():
            self.frozen.add(component['raw_json'], component['sv'], *component.get('raw_sources', {}).values())
        self.frozen.add(self.config['library'])
        require(digest(self.config['library']) == LIBRARY_SHA256, 'Unpinned mapping library')
        producer = {Path(__file__).resolve(), Path(sys.executable).resolve()}
        producer.update(Path(module.__file__).resolve() for module in sys.modules.values()
            if getattr(module, '__file__', None) and Path(module.__file__).resolve().parent == self.root / 'scripts')
        producer.update(path.resolve() for path in (self.root / 'scripts').glob('*.py'))
        producer.update(Path(path).resolve() for path in self.config.get('source_files', []))
        self.frozen.add(*sorted(producer))
        tools = runtime_files(self.tools)
        self.frozen.add(*tools)
        self.report.update(producer_sha256={str(path): self.frozen.files[str(path)] for path in sorted(producer)},
            native_runtime_sha256={str(path): self.frozen.files[str(path)] for path in tools},
            python=dict(path=sys.executable, version=sys.version, dont_write_bytecode=sys.dont_write_bytecode,
                sha256=digest(Path(sys.executable).resolve())))
        if self.config.get('build', True):
            sources = list((self.root / 'Pinwheel').rglob('*.lean'))
            lakefiles = [path for path in (self.root/'lakefile.lean',self.root/'lakefile.toml') if path.is_file()]
            require(len(lakefiles) == 1, 'Select one unambiguous Lake project file')
            self.frozen.add(*sources, self.root/'Pinwheel.lean', self.root/'lean-toolchain', self.root/'lake-manifest.json', *lakefiles)
            self.run([self.tools['lake'], 'build', *BUILD_ROOTS], 'mapped-library-build', timeout=self.config.get('timeout', 900))
        products = [path for path in (self.root / '.lake/build/lib/lean/Pinwheel').rglob('*') if path.is_file() and '.olean' in path.name]
        self.frozen.add(*products)
        self.library = load_library(self.config['library'])

    def component(self, label, component_generator=None):
        cfg = self.config['components'][label]
        suffix = dict(frontend='Frontend', **{'core-d2': 'CoreD2', 'core-d4': 'CoreD4'})[label]
        prefix, namespace = 'Mapped' + suffix, 'Pinwheel.Artifact.StreamingMapped' + suffix
        directory = self.out / label; directory.mkdir()
        proof = directory / 'proof'; proof.mkdir()
        raw = read_json(cfg['raw_json'])
        require(type(raw.get('modules')) is dict and len(raw['modules']) == 1, 'One source component top required')
        top = next(iter(raw['modules']))
        source_state(raw, top)
        hierarchical, words = hierarchical_source(raw, top)
        source = self.write(directory / 'source.json', json.dumps(hierarchical, sort_keys=True) + '\n')
        self.write(directory / 'words.json', json.dumps(words, sort_keys=True, indent=2) + '\n')
        script = self.write(directory / 'map.ys', mapping_script(source, top, directory, self.config['library'], self.tools['abc']))
        self.frozen.add(source, script, self.config['library'], cfg['raw_json'])
        self.run([self.tools['yosys'], '-Q', '-T', '-s', script], label + '-map', timeout=self.config.get('timeout', 900))
        mapped = directory / 'mapped.json'; self.frozen.add(mapped, directory / 'mapped.v', directory / 'pre-map.json')
        data = read_json(mapped)
        inventory = state_inventory(raw, data, top, self.library)
        self.write(directory / 'state-inventory.json', json.dumps(inventory, sort_keys=True, indent=2) + '\n')
        entry = dict(all_state_bijection=True, register_fields=inventory['register_fields'],
            state_bits=inventory['register_bits'], mapped_ff_cells=inventory['mapped_ff_cells'],
            mapped_comb_cells=inventory['mapped_comb_cells'], local_proofs_checked=False,
            full_component_checked=False, mutations_checked=False, whole_component_controls_checked=False,
            axiom_audit_checked=False,
            proof_directory=str(proof), namespace=namespace, compiled_modules=[])
        self.report['components'][label] = entry
        fa_module, fa_namespace = prefix + 'FA', namespace + '.FA'
        text = generate_full_adder(mapped, self.library, namespace=fa_namespace)
        self.compile(proof, fa_module, text); entry['compiled_modules'].append(fa_module)
        word_modules = {}
        for module, description in words.items():
            self.frozen.add(mapped)
            name, ns, kind = prefix + 'Word' + module.rsplit('_', 1)[-1], namespace + '.Word' + module.rsplit('_', 1)[-1], description['kind']
            if kind in ARITHMETIC:
                text, metadata = generate_arithmetic(mapped, self.library, module, kind, namespace=ns,
                    fa_module=fa_module, fa_namespace=fa_namespace)
            elif kind in REDUCTIONS:
                text, metadata = generate_reduction(mapped, self.library, module, kind, namespace=ns)
            else:
                require(kind in BITWISE, 'No native certificate producer for ' + kind)
                text = bitwise_source(load_mapped(mapped, module, self.library, combinational=True), kind,
                    namespace=ns, netlist_sha256=digest(mapped)); metadata = dict(module=module, kind=kind)
            self.compile(proof, name, text); entry['compiled_modules'].append(name)
            word_modules[module] = dict(module=name, namespace=ns, metadata=metadata, netlist_sha256=digest(mapped),
                module_sha256=sha256(json.dumps(data['modules'][module],sort_keys=True,separators=(',',':')).encode()).hexdigest(),
                source_sha256=digest(proof/(name+'.lean')))
        entry.update(local_proofs_checked=True, word_modules=word_modules)
        self.controls(label, directory, proof, mapped, words, prefix, namespace, fa_module, fa_namespace, entry)
        raw_sources = cfg.get('raw_sources', {})
        if component_generator is not None and raw_sources:
            for name, path in raw_sources.items():
                self.frozen.add(path)
                self.compile(proof, name, Path(path).read_text(), label=label + '-raw-' + name)
                entry['compiled_modules'].append(name)
            kind, bits = ('frontend', 1) if label == 'frontend' else ('core', 1 if label == 'core-d2' else 2)
            rb = streaming_ready_readback.backend(kind, bits)
            self.frozen.add(mapped, cfg['raw_json'])
            texts, metadata = component_generator(rb, Path(cfg['raw_json']), mapped, self.library, word_modules,
                namespace=namespace, raw_module=cfg['raw_module'], raw_namespace=cfg['raw_namespace'], module_prefix=prefix)
            require(type(texts) is dict and texts, 'Component generator omitted native modules')
            for name, text in texts.items():
                self.compile(proof, name, text); entry['compiled_modules'].append(name)
            required = prefix + 'Required'
            self.compile(proof, required, required_source(rb, next(reversed(texts)), namespace))
            entry['compiled_modules'].append(required)
            self.structural_controls(label, directory, mapped, word_modules, rb, component_generator, entry)
            entry.update(full_component_checked=True, component_metadata=metadata)
        else:
            entry['missing_component_join'] = 'Whole-component generator or fresh raw proof source closure not supplied'
        audit = prefix + 'Audit'
        output = self.compile(proof, audit, audit_source(entry['compiled_modules']))
        match = re.findall(r'Mapped audit: (\d+) declarations, (\d+) theorems; standard axioms only\.', output)
        require(len(match) == 1 and min(map(int, match[0])) > 0, 'Missing unambiguous native closure audit')
        entry.update(axiom_audit_checked=True, audited_declarations=int(match[0][0]), audited_theorems=int(match[0][1]))
        private = prefix + 'PrivateControl'
        self.compile(proof, private, 'namespace Pinwheel.MappedNegativeControl\nprivate axiom hidden : False\nend Pinwheel.MappedNegativeControl\n', fixture=True)
        self.compile(proof, prefix + 'PrivateAuditControl', audit_source([*entry['compiled_modules'],private]),
            reject='Unapproved axioms', fixture=True)
        entry['private_axiom_rejected'] = True
        return dict(label=label, directory=directory, proof=proof, mapped=mapped, raw=raw,
            word_modules=word_modules, namespace=namespace, prefix=prefix, report=entry)

    def controls(self, label, directory, proof, mapped, words, prefix, namespace, fa_module, fa_namespace, entry):
        candidates = [(name, info) for name, info in words.items() if info['kind'] == '$add' and info['ports']['Y'] >= 2]
        require(candidates, 'Need a positive wide add before carry/output/operator mutations')
        module, description = candidates[0]
        original = read_json(mapped); controls = []
        target = directory / 'controls'; target.mkdir()
        for mode, rejection in [('unchanged', None), ('broken-carry', 'Tactic `rfl` failed'),
                ('changed-output', 'Type mismatch'), ('wrong-operator', 'Tactic `rfl` failed')]:
            data = deepcopy(original); word = data['modules'][module]; kind = '$add'
            if mode == 'broken-carry': word['cells']['bit_1']['connections']['CI'] = ['0']
            elif mode == 'changed-output': word['ports']['Y']['bits'][0] = word['ports']['Y']['bits'][1]
            elif mode == 'wrong-operator': kind = '$sub'
            path = self.write(target / (mode + '.json'), json.dumps(data, sort_keys=True) + '\n')
            text, metadata = generate_arithmetic(path, self.library, module, kind,
                namespace=namespace + '.Control' + mode.replace('-', ''), fa_module=fa_module, fa_namespace=fa_namespace)
            self.compile(target, prefix + mode.replace('-', '') + 'Control', text, paths=(proof,), reject=rejection,
                label=label + '-' + mode)
            controls.append(dict(name=mode, passed=True, expected_rejection=rejection is not None,
                reason=rejection, artifact=str(path)))
        data = deepcopy(original)
        top = next(name for name in data['modules'] if name == next(iter(read_json(self.config['components'][label]['raw_json'])['modules'])))
        ff = next(name for name, cell in data['modules'][top]['cells'].items() if cell['type'].endswith('dfrbpq_1'))
        del data['modules'][top]['cells'][ff]
        path = self.write(target / 'dropped-ff.json', json.dumps(data, sort_keys=True) + '\n')
        try: state_inventory(read_json(self.config['components'][label]['raw_json']), data, top, self.library)
        except ValueError: controls.append(dict(name='dropped-ff', passed=True, expected_rejection=True,
            reason='Strict complete FF Q inventory/driver refusal', artifact=str(path)))
        else: raise RuntimeError('A dropped physical FF was accepted')
        entry.update(mutations=controls, mutations_checked=True)

    def structural_controls(self, label, directory, mapped, word_modules, rb, component_generator, entry):
        """Corrupt actual top wiring, keeping every certified word body intact."""
        cfg = self.config['components'][label]
        self.frozen.add(mapped, cfg['raw_json'])
        original = read_json(mapped)
        top = rb.TOP
        data = deepcopy(original)
        choices = [(name,pin,index) for name,cell in data['modules'][top]['cells'].items()
            if cell['type'] in word_modules for pin,bits in cell['connections'].items()
            if pin != 'Y' for index,bit in enumerate(bits) if bit in ('0','1')]
        require(choices, 'No actual word-input constant available for the structural control')
        name,pin,index = choices[0]
        bits = data['modules'][top]['cells'][name]['connections'][pin]
        bits[index] = '1' if bits[index] == '0' else '0'
        path = self.write(directory/'controls'/'top-word-input.json',json.dumps(data,sort_keys=True)+'\n')
        expected = 'Actual mapped word wiring differs from source topology'
        try:
            component_generator(rb,Path(cfg['raw_json']),path,self.library,word_modules,
                namespace=entry['namespace'],raw_module=cfg['raw_module'],raw_namespace=cfg['raw_namespace'])
        except ValueError as error:
            require(expected in str(error), 'Word-input control refused for an unrelated reason: '+str(error))
        else: raise RuntimeError('Actual mapped top word-input mutation was accepted')
        entry['mutations'].append(dict(name='top-word-input',passed=True,expected_rejection=True,
            rejection_layer='strict-component-topology',reason=expected,artifact=str(path),cell=name,pin=pin,bit=index))
        data = deepcopy(original)
        name = next(name for name,cell in data['modules'][top]['cells'].items() if cell['type'].endswith('dfrbpq_1'))
        data['modules'][top]['cells'][name]['connections']['CLK'] = ['0']
        path = self.write(directory/'controls'/'ff-clock-zero.json',json.dumps(data,sort_keys=True)+'\n')
        expected = 'Unsupported FF clock, asynchronous reset or clock-as-data'
        try: state_inventory(read_json(cfg['raw_json']),data,top,self.library)
        except ValueError as error:
            require(expected in str(error), 'FF-clock control refused for an unrelated reason: '+str(error))
        else: raise RuntimeError('Actual physical FF nonclock mutation was accepted')
        entry['mutations'].append(dict(name='ff-clock-zero',passed=True,expected_rejection=True,
            rejection_layer='strict-physical-clock',reason=expected,artifact=str(path),cell=name))
        entry['whole_component_controls_checked'] = True

    def finish(self):
        self.report['frozen_inputs_unchanged'] = self.frozen.verify()
        self.report['frozen_sha256'] = self.frozen.files
        self.report['passed'] = acceptance(self.report)
        self.report['elapsed_seconds'] = round(time.monotonic() - self.started, 3)
        (self.out / 'report.json').write_text(json.dumps(self.report, indent=2) + '\n')
        return self.report


def run_campaign(out, config, run=None, *, component_generator=None, wrapper_hook=None):
    """All outputs are fresh; missing joins are explicit incomplete reports.

    component_generator is the new generate_component API. wrapper_hook(worker,
    contexts) must return ordered native module texts plus required exact-typed
    proof targets; the master wrapper producer owns actual wrapper generation.
    """
    worker = Worker(out, config, run)
    try:
        worker.intake()
        contexts = [worker.component(label, component_generator) for label in LABELS]
        if wrapper_hook is not None:
            result = wrapper_hook(worker, contexts)
            require(type(result) is dict and type(result.get('modules')) is dict and result['modules'] and
                type(result.get('required')) is dict and result['required'], 'Wrapper omitted native modules or exact typed required targets')
            directory = worker.out / 'wrapper'; directory.mkdir(exist_ok=True)
            paths = tuple(dict.fromkeys([*(context['proof'] for context in contexts),
                *(Path(item['directory']) for item in worker.modules)]))
            require(not (set(result['modules']) & set(result['required'])), 'Wrapper source/required module names collide')
            names, required_output = [], ''
            for name, text in result['modules'].items():
                worker.compile(directory,name,text,paths=paths);names.append(name)
            for name,text in result['required'].items():
                required_output += worker.compile(directory,name,text,paths=paths) + '\n';names.append(name)
            metadata = result.get('metadata', {})
            qnames = metadata.get('required_qnames', [])
            verify_qnames(required_output,qnames)
            verify_extra_qnames(required_output, metadata.get('extra_qnames'), qnames)
            closure = list(dict.fromkeys(item['module'] for item in worker.modules))
            output = worker.compile(directory, 'MappedWrapperAudit', audit_source(closure), paths=paths)
            require(re.search(r'Mapped audit: [1-9]\d* declarations, [1-9]\d* theorems; standard axioms only\.', output), 'Wrapper audit absent')
            private = 'MappedWrapperPrivateControl'
            worker.compile(directory,private,'namespace Pinwheel.MappedWrapperNegative\nprivate axiom hidden : False\nend Pinwheel.MappedWrapperNegative\n',paths=paths,fixture=True)
            worker.compile(directory,'MappedWrapperPrivateAuditControl',audit_source([*closure,private]),
                paths=paths,reject='Unapproved axioms',fixture=True)
            worker.report.update(wrapper_checked=True, wrapper_axiom_audit_checked=True,
                wrapper_private_axiom_rejected=True, required_qnames_checked=True, extra_qnames_checked=True,
                wrapper_metadata=metadata)
        return worker.finish()
    except BaseException as error:
        worker.report.update(error=type(error).__name__ + ': ' + str(error), passed=False)
        try: worker.finish()
        except BaseException as closeout:
            worker.report.update(passed=False, frozen_inputs_unchanged=False, closeout_error=str(closeout), frozen_sha256=worker.frozen.files)
            (worker.out / 'report.json').write_text(json.dumps(worker.report, indent=2) + '\n')
        raise
