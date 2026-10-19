"""Full-session certificate assembly for the fresh buffered RTL gate.

Component facts are imported from their actual artifact certificates. This
module never substitutes the typed circuit for an imported component model.
The generic memory law remains explicit; the concrete digital specialization
is a closed model, not an electrical or SRAM-macro implementation claim.
"""
from contextlib import contextmanager
from pathlib import Path
import re
import pickle
import subprocess


class SectionRun:
    def __init__(self, run, section):
        self.run, self.section = run, section

    def __call__(self, command, label, **options):
        return self.run(command, self.section + '.' + label, **options)


@contextmanager
def recorded_solver(rb, solver, run, directory, *, freeze=None):
    """Retain every solver proposal, including old unsat-core selection calls.

    The temporarily redirected subprocess entry accepts only the one selected
    solver and exact stdin/text options. Commands uses Popen independently, so
    the actual execution is bounded and logged through its process group.
    """
    directory = Path(directory)
    directory.mkdir()
    count = 0
    original_run, original_oracle = subprocess.run, rb.cut_oracle
    def invoke(argv, *, input=None, capture_output=False, text=False, timeout=None, **options):
        nonlocal count
        if (str(argv[0]) != str(solver) or '-in' not in argv or not isinstance(input, str) or
                not capture_output or not text or options):
            raise RuntimeError('Unrecorded or unexpected subprocess in solver proposal context')
        count += 1
        label = f'smt-{count:05d}'
        path = directory / (label + '.smt2')
        path.write_text(input)
        if freeze:
            freeze([path])
        command = [arg for arg in argv if arg != '-in'] + ['-smt2', path]
        output = run(command, label, timeout=timeout or 20)
        return subprocess.CompletedProcess(argv, 0, output, '')
    def oracle(selected):
        if str(selected) != str(solver):
            raise RuntimeError('Proposal changed the selected solver')
        def query(pair):
            result = invoke([str(solver), '-in', '-T:3'], input=rb.smt_suggestion(pair),
                            capture_output=True, text=True, timeout=5)
            return result.stdout.strip() == 'unsat'
        return query
    subprocess.run, rb.cut_oracle = invoke, oracle
    try:
        yield lambda: count
    finally:
        subprocess.run, rb.cut_oracle = original_run, original_oracle


def register_inputs(report, gate, root, paths):
    return gate.freeze_inputs(report, root, paths)


def controller_worker(config, run, report, gate):
    """Build both controller descriptions and their actual RTL certificate.

    The independently checked complete-DAG to emitted-MLIR generator returns an
    ordered module dictionary ending SramArtifactProof.
    """
    import buffered_sram_readback as b
    import buffered_sram_reference as env
    import buffered_reactive_reference as reactive
    snapshot, root = Path(config['snapshot']), Path(config['worker_out'])
    out = root / 'controller'
    out.mkdir()
    emitted, proof, proposals = out / 'emitted', out / 'proof', out / 'smt-proposals'
    emitted.mkdir()
    proof.mkdir()
    tools = config['tool_paths']
    run = SectionRun(run, 'controller')
    freeze = lambda paths: register_inputs(report, gate, root, paths)
    run([tools['lake'], 'build', 'Pinwheel.Hardware.Buffered.SramArtifactReference'],
        'fresh-reference-build', timeout=1800)
    run([tools['python'], '-B', 'test/test_buffered_sram_readback.py'], 'adapter-boundaries', timeout=120)
    for name in ('reference', 'selection', 'mutations'):
        run([tools['python'], '-B', 'test/test_buffered_sram_' + name + '.py'],
            name + '-boundaries', timeout=120)
    emitters = {'EnvironmentEmit': env.environment_emitter(), 'ReactiveEmit': reactive.emitter_source()}
    for name, text in emitters.items():
        source = emitted / (name + '.lean')
        source.write_text(text)
        register_inputs(report, gate, root, [source])
        run([tools['lake'], 'env', 'lean', '--root=' + str(emitted), '-DwarningAsError=true',
             '--run', source, emitted / (name + '.mlir')], name, timeout=600)
        freeze([emitted / (name + '.mlir')])
    run([tools['lake'], 'env', 'lean', '-DwarningAsError=true', '--run',
         'test/SramArtifactEmit.lean', emitted], 'emit-core', timeout=600)
    freeze(emitted.rglob('*'))
    sv = emitted / 'core.sv'
    text = run([tools['circt'], emitted / 'core.mlir', '--canonicalize', '--lower-seq-to-sv',
        '--lower-hw-to-sv', '--hw-legalize-modules', '--export-verilog', '-o', '/dev/null'],
        'circt-export', timeout=180)
    sv.write_text(text)
    freeze([sv])
    rb = b.backend()
    b.check_interface(rb, b.read_json(emitted / 'assembly.json'))
    source = b.read_hints(rb, emitted / 'core.mlir')
    b.validate_graph(rb, source)
    rtl, imported = gate.import_rtl(run, rb, tools, proof, sv, 'import-core', freeze=freeze)
    b.validate_graph(rb, rtl)
    environment_rb, reactive_rb = env.environment_backend(), reactive.backend()
    environment = environment_rb.read_hints(emitted / 'EnvironmentEmit.mlir')
    reactive_graph = reactive_rb.read_hints(emitted / 'ReactiveEmit.mlir')
    b.validate_graph(environment_rb, environment)
    b.validate_graph(reactive_rb, reactive_graph)
    reference, mapping, post = env.complete_reference(environment, reactive_graph)
    b.validate_graph(rb, reference)
    with recorded_solver(rb, tools['solver'], run, proposals, freeze=freeze) as query_count:
        pairs = b.partitions(rb, source, rtl, tools['solver'])
        pairs = b.comparison_abstractions(rb, pairs, tools['solver'])
        reference_pairs = b.reference_partitions(rb, reference, source, tools['solver'])
        typed = b.reference_certificate_sources(rb, reference, source, environment, reference_pairs)
        report['controller_smt_proposal_commands'] = query_count()
    if not typed or list(typed)[-1] != 'SramArtifactProof':
        raise RuntimeError('Complete typed controller bridge must end with SramArtifactProof')
    gate.write_json(out / 'partitions.json', pairs)
    # Preserve object sharing in the large dictionary-selection description.
    # This is retained proposal data, never deserialized as proof evidence.
    (out / 'reference-partitions.pickle').write_bytes(pickle.dumps(reference_pairs, protocol=5))
    texts = {
        'EnvironmentHints': env.environment_hints(environment_rb, environment),
        'EnvironmentSources': env.environment_sources(environment_rb, environment),
        'ReactiveHints': reactive.hints_source(reactive_rb, reactive_graph),
        'ReactiveSources': reactive.sources_source(reactive_rb, reactive_graph),
        'ComposedHints': env.composition_hints(rb, reference, environment, reactive_graph, mapping),
        'ComposedSources': env.composition_sources(rb, reference, environment, reactive_graph, mapping),
        'CompleteSources': env.complete_sources(rb, reference, environment, reactive_graph, mapping, post),
        'SramArtifactHints': b.graph_source(rb, source, 'Source'),
        'SramArtifactGraphs': b.graph_source(rb, rtl, 'RTL'),
        'SramArtifactLocalProofsAbstract': b.local_proofs_source(rb, pairs),
        'SramArtifactLinks': b.links_source(rb, source, rtl, pairs,
            proofs_module='SramArtifactLocalProofsAbstract'),
        'SramArtifactModel': b.model_source(rb, rtl),
        **b.hint_certificate_sources(rb, source, rtl, pairs),
        **typed,
    }
    for name, text in texts.items():
        (proof / (name + '.lean')).write_text(text)
    register_inputs(report, gate, root, [*emitted.rglob('*'), imported,
        *(proof / (name + '.lean') for name in texts)])
    generated = {p.name: gate.digest(p) for p in proof.glob('*.lean')}
    report['controller_proof_closure'] = gate.proof_closure(snapshot, [proof, emitted],
        ['SramArtifactProof', *emitters], config['source_sha256'],
        {**generated, **{p.name: gate.digest(p) for p in emitted.glob('*.lean')}})
    order = ('EnvironmentHints', 'EnvironmentSources', 'ReactiveHints', 'ReactiveSources',
        'ComposedHints', 'ComposedSources', 'CompleteSources', 'SramArtifactHints',
        'SramArtifactGraphs', 'SramArtifactLocalProofsAbstract', 'SramArtifactLinks',
        'SramArtifactModel', 'SramArtifactHintModel', 'SramArtifactHintEndpoints',
        'SramArtifactHintProof', *typed)
    for name in order:
        gate.compile_lean(run, tools, proof, name)
    report['controller'] = dict(**b.census(rb, rtl), partitions=len(pairs),
        reference_partitions=len(reference_pairs),
        abstract_comparison_partitions=sum('abstract' in pair for pair in pairs),
        typed_source_bridge=True, complete_reference_graph_validated=True,
        compiled_modules=list(order))
    return dict(directory=proof, modules=texts, rb=rb, source=source, rtl=rtl, sv=sv)


def combined_source(controller_module, controller_step, controller_observe):
    header = f'''import SerialProof
import {controller_module}
import ArtifactWrapperCertificate
import Pinwheel.Hardware.Buffered.ArtifactTinyTapeoutI2cTimingSession
import Pinwheel.Hardware.Buffered.ArtifactMixedSession

namespace Pinwheel.Artifact.Buffered.Session
open Pinwheel.Hardware Pinwheel.Hardware.Buffered Pinwheel.Program
set_option linter.unusedVariables false

def components : ArtifactPackage.Components where
  frontend := Pinwheel.Artifact.Buffered.Serial.behavior
  controller := ⟨Pinwheel.Artifact.BufferedSram.rtlStep, Pinwheel.Artifact.BufferedSram.rtlObserve⟩

theorem components_correct : ArtifactPackage.Correct components where
  frontend_step := fun i r {{w}} port => Pinwheel.Artifact.Buffered.Serial.next_correct i r port
  frontend_observe := fun i r {{w}} port => Pinwheel.Artifact.Buffered.Serial.output_correct i r port
  controller_step := fun i r {{w}} port => {controller_step} i r port
  controller_observe := fun i r {{w}} port => {controller_observe} i r port

def package : ArtifactPackageWiringSession.Certified :=
  ⟨Pinwheel.Artifact.Buffered.Wrappers.packageWiring,
    Pinwheel.Artifact.Buffered.Wrappers.package_correct,
    Pinwheel.Artifact.Buffered.Wrappers.memoryInventory,
    Pinwheel.Artifact.Buffered.Wrappers.memory_correct⟩

def wrapper : ArtifactTinyTapeoutWiringSession.Certified :=
  ⟨package, Pinwheel.Artifact.Buffered.Wrappers.tinyWiring,
    Pinwheel.Artifact.Buffered.Wrappers.tiny_correct⟩

theorem all_pin_history {{M : Type}} (memory : Memory.SinglePort.Contract M 6 64)
    (before : ArtifactPackage.State M) (pins : List ArtifactTinyTapeout.Pins) :
    (wrapper.run components memory before pins).view memory =
      (before.view memory).run (pins.map ArtifactTinyTapeout.Pins.enginePins) := by
  exact wrapper.view_run components_correct memory before pins

def digitalMemory : Memory.SinglePort.Contract (Memory.Sram.State 6 64) 6 64 where
  view := id
  advance := fun command state => Memory.SinglePort.step state command
  correct := fun command state => rfl

theorem digital_all_pin_history (before : ArtifactPackage.State (Memory.Sram.State 6 64))
    (pins : List ArtifactTinyTapeout.Pins) :
    (wrapper.run components digitalMemory before pins).view digitalMemory =
      (before.view digitalMemory).run (pins.map ArtifactTinyTapeout.Pins.enginePins) := by
  exact all_pin_history digitalMemory before pins
'''
    generic_session = '''
theorem initialized_session {M : Type} (memory : Memory.SinglePort.Contract M 6 64)
    (before : ArtifactPackage.State M) (previous : Transfer.State)
    (coldPin : SerialPackage.Pins) (cold : coldPin.cold = true) (idle : coldPin.csn = true)
    (loading : SerialUpload.Loading ((before.view memory).step coldPin))
    (trace : LogicalWire.Interrupted.Trace loading.after
      (.free (LogicalSession.resetLogical previous) (loading.after.controller.core .transfer).toNat)
      .available pins after final finalFrontend) :
    (wrapper.run components memory before
      (((coldPin :: loading.pins) ++ pins).map ArtifactTinyTapeout.encode)).view memory = after ∧
      Transfer.step Refinement.capacity previous .reset = ⟨LogicalSession.resetLogical previous,.reset⟩ ∧
      LogicalWire.Valid after final finalFrontend ∧ trace.Observed := by
  exact wrapper.initialized_session components_correct memory before previous coldPin cold idle loading trace
'''
    generic_rounds = '''
theorem initialized_two_logical_rounds {M : Type} (memory : Memory.SinglePort.Contract M 6 64)
    (before : ArtifactPackage.State M) (previous : Transfer.State)
    (pin : SerialPackage.Pins) (cold : pin.cold = true) (idle : pin.csn = true) :
    ∃ loading : SerialUpload.Loading ((before.view memory).step pin),
      ∃ first : SerialSessionWitness.LogicalRound loading.after (LogicalSession.resetLogical previous) 0,
      ∃ second : SerialSessionWitness.LogicalRound first.after first.finalLogical 0,
      ∃ trace : LogicalWire.Trace loading.after (.free (LogicalSession.resetLogical previous) 0) .available
        (first.pins ++ second.pins) second.after (.free second.finalLogical 0) .available,
      (wrapper.run components memory before
        (((pin :: loading.pins) ++ (first.pins ++ second.pins)).map ArtifactTinyTapeout.encode)).view memory =
          second.after ∧
      LogicalWire.Valid second.after (.free second.finalLogical 0) .available ∧
      second.finalLogical.epoch = previous.epoch + 1 ∧ second.finalLogical.nextSequence = 3 ∧
      second.after.controller.core .generation = 1 ∧ second.after.controller.core .transfer = 2 ∧
      trace.Observed := by
  exact wrapper.initialized_two_logical_rounds components_correct memory before previous pin cold idle
'''
    # Specialize the complete propositions as well as the proof application.
    # The closed versions have no caller-supplied memory-contract premise.
    digital_session = generic_session.replace('theorem initialized_session {M : Type} (memory : Memory.SinglePort.Contract M 6 64)\n'
        '    (before : ArtifactPackage.State M)',
        'theorem digital_initialized_session\n    (before : ArtifactPackage.State (Memory.Sram.State 6 64))')
    digital_session = digital_session.replace('memory', 'digitalMemory').replace(
        'exact wrapper.initialized_session components_correct digitalMemory',
        'exact initialized_session digitalMemory')
    digital_rounds = generic_rounds.replace('theorem initialized_two_logical_rounds {M : Type} (memory : Memory.SinglePort.Contract M 6 64)\n'
        '    (before : ArtifactPackage.State M)',
        'theorem digital_initialized_two_logical_rounds\n    (before : ArtifactPackage.State (Memory.Sram.State 6 64))')
    digital_rounds = digital_rounds.replace('memory', 'digitalMemory').replace(
        'exact wrapper.initialized_two_logical_rounds components_correct digitalMemory',
        'exact initialized_two_logical_rounds digitalMemory')
    timing_module = Path(__file__).resolve().parents[1] / 'Pinwheel/Hardware/Buffered/ArtifactTinyTapeoutI2cTimingSession.lean'
    timing = timing_module.read_text()
    timing = timing[timing.index('theorem Certified.timing_initialized_session'):timing.index('\nend Pinwheel.Hardware.Buffered.ArtifactTinyTapeoutWiringSession')]
    # Copy the exact public propositions, specializing the implementation
    # argument to the independently certified imported components.
    for theorem in ('timing_initialized_session', 'timing_two_fused_rounds'):
        start = timing.index('theorem Certified.' + theorem)
        stop = timing.find('\ntheorem ', start + 1)
        statement = timing[start:stop if stop >= 0 else len(timing)].split(' := by', 1)[0]
        statement = statement.replace('theorem Certified.' + theorem + ' {M : Type} (wrapper : Certified)\n'
            '    {components : ArtifactPackage.Components} (correct : ArtifactPackage.Correct components)',
            'theorem ' + theorem + ' {M : Type}')
        call = ('wrapper.' + theorem + ' components_correct memory duration budget before previous ' +
                ('coldPin cold idle loading trace' if theorem == 'timing_initialized_session' else 'pin cold idle'))
        generic = statement + ' := by\n  exact ' + call + '\n'
        digital = generic.replace('theorem ' + theorem + ' {M : Type}\n'
            '    (memory : Memory.SinglePort.Contract M 6 64)', 'theorem digital_' + theorem)
        digital = digital.replace('(before : ArtifactPackage.State M)',
            '(before : ArtifactPackage.State (Memory.Sram.State 6 64))')
        digital = digital.replace('memory', 'digitalMemory').replace(
            'wrapper.' + theorem + ' components_correct digitalMemory', theorem + ' digitalMemory')
        header += generic + digital
    programmable_module = Path(__file__).resolve().parents[1] / 'Pinwheel/Hardware/Buffered/ArtifactProgrammableSession.lean'
    programmable = programmable_module.read_text()
    programmable = programmable[programmable.rindex('theorem Certified.programmable_initialized_session'):]
    statement = programmable.split(' := by', 1)[0].replace(
        'theorem Certified.programmable_initialized_session {M : Type} (wrapper : Certified)\n'
        '    {components : ArtifactPackage.Components} (correct : ArtifactPackage.Correct components)',
        'theorem programmable_initialized_session {M : Type}')
    generic = statement + (' := by\n  exact wrapper.programmable_initialized_session components_correct '
        'memory image before previous coldPin cold idle loading trace\n')
    digital = generic.replace('theorem programmable_initialized_session {M : Type}\n'
        '    (memory : Memory.SinglePort.Contract M 6 64)', 'theorem digital_programmable_initialized_session')
    digital = digital.replace('(before : ArtifactPackage.State M)',
        '(before : ArtifactPackage.State (Memory.Sram.State 6 64))')
    digital = digital.replace('memory', 'digitalMemory').replace(
        'wrapper.programmable_initialized_session components_correct digitalMemory',
        'programmable_initialized_session digitalMemory')
    header += generic + digital
    mixed_module = Path(__file__).resolve().parents[1] / 'Pinwheel/Hardware/Buffered/ArtifactMixedSession.lean'
    mixed = mixed_module.read_text()
    mixed = mixed[mixed.rindex('theorem Certified.mixed_i2c_spi_switch'):]
    statement = mixed.split(' := by', 1)[0].replace(
        'theorem Certified.mixed_i2c_spi_switch {M : Type} (wrapper : Certified)\n'
        '    {components : ArtifactPackage.Components} (correct : ArtifactPackage.Correct components)',
        'theorem mixed_i2c_spi_switch {M : Type}')
    generic = statement + (' := by\n  exact wrapper.mixed_i2c_spi_switch components_correct '
        'memory duration budget c before previous pin cold idle\n')
    digital = generic.replace('theorem mixed_i2c_spi_switch {M : Type}\n'
        '    (memory : Memory.SinglePort.Contract M 6 64)', 'theorem digital_mixed_i2c_spi_switch')
    digital = digital.replace('(before : ArtifactPackage.State M)',
        '(before : ArtifactPackage.State (Memory.Sram.State 6 64))')
    digital = digital.replace('memory', 'digitalMemory').replace(
        'wrapper.mixed_i2c_spi_switch components_correct digitalMemory', 'mixed_i2c_spi_switch digitalMemory')
    header += generic + digital
    return header + generic_session + generic_rounds + digital_session + digital_rounds + '\nend Pinwheel.Artifact.Buffered.Session\n'


FULL_TARGETS = (
    'frontend all 13 register fields / 19 output fields',
    'controller all 117 register fields / 31 output fields',
    'actual package, memory and Tiny Tapeout wiring certificates',
    'Session.components_correct derived from actual imported components',
    'Session.all_pin_history for every finite Tiny Tapeout pin history under the exact memory law',
    'Session.initialized_session with carried source state and repeated/interrupted raw transactions',
    'Session.initialized_two_logical_rounds nonempty witness',
    'Session.digital_all_pin_history with a closed synchronous digital memory model',
    'Session.digital_initialized_session',
    'Session.digital_initialized_two_logical_rounds',
    'Session.timing_initialized_session for every duration/budget : Fin 256',
    'Session.timing_two_fused_rounds nonempty witness for every duration/budget : Fin 256',
    'Session.digital_timing_initialized_session and digital_timing_two_fused_rounds',
    'Session.programmable_initialized_session for arbitrary certified images and heterogeneous reloads',
    'Session.digital_programmable_initialized_session with carried allocator and closed digital memory',
    'Session.mixed_i2c_spi_switch: concrete initialized I2C to warm reload to SPI witness',
    'Session.digital_mixed_i2c_spi_switch for every timing pair and BufferedSPI.Config',
    'all owned constants including private generated helpers; one private axiom rejection',
    'unchanged full-field reimports and actual RTL/wrapper mutation refusals',
)



def controller_unchanged_source(rb, graph):
    """Reconnect identical reimports linearly, preserving every field theorem.

    Definitional equality of entire renamed DAGs can expand exponentially. Each
    alias below unfolds exactly one operator and reuses its earlier argument
    aliases. The final statements still quantify over arbitrary inputs/state.
    """
    lines = ['import SramArtifactProof\nimport SramMutantModel\n' + rb.HEADER,
             'set_option linter.unusedSimpArgs false']
    for name, node in graph.nodes.items():
        if node.op in ('input', 'reg'):
            continue
        rules = ['Mutant.' + name, 'RTL.' + name]
        rules += ['unchanged_' + arg for arg in dict.fromkeys(node.args)
                  if graph.nodes[arg].op not in ('input', 'reg')]
        lines += [f'theorem unchanged_{name} (i : Values Sram.Input) (s : Values Sram.Register) :',
                  f'    Mutant.{name} i s = RTL.{name} i s := by',
                  '  simp only [' + ', '.join(rules) + ']', '  all_goals rfl']
    def rules(roots):
        return ', '.join(dict.fromkeys('unchanged_' + root for root in roots
            if graph.nodes[root].op not in ('input', 'reg')))
    step = '[mutantStep, rtlStep, ' + rules(graph.next.values()) + ']'
    observe = '[mutantObserve, rtlObserve, ' + rules(graph.outputs.values()) + ']'
    lines += [
        'theorem unchanged_next (i : Values Sram.Input) (s : Values Sram.Register) (r : Sram.Register w) :',
        '    mutantStep i s r = Sram.circuit.step i s r := by',
        '  apply Eq.trans (b := rtlStep i s r) _ (step_correct i s r)',
        '  cases r with',
        '  | metadata k => simp only ' + step,
        '  | branch k => simp only ' + step,
        '  | branchWritten => simp only ' + step,
        '  | startWord => simp only ' + step,
        '  | core r => cases r <;> simp only ' + step,
        'theorem unchanged_output (i : Values Sram.Input) (s : Values Sram.Register) (o : Sram.Output w) :',
        '    mutantObserve i s o = Sram.circuit.observe i s o := by',
        '  apply Eq.trans (b := rtlObserve i s o) _ (observe_correct i s o)',
        '  cases o with',
        '  | base o => cases o <;> simp only ' + observe,
        '  | port p =>', '    cases p with',
        '    | address b => cases b <;> simp only ' + observe,
        '    | data => simp only ' + observe,
        '    | write => simp only ' + observe,
        '    | read => simp only ' + observe,
        'end Pinwheel.Artifact.BufferedSram']
    return '\n'.join(lines) + '\n'


def controller_mutations(config, run, report, gate, controller):
    import buffered_sram_readback as b
    import buffered_sram_mutations as mutations
    root, tools = Path(config['worker_out']), config['tool_paths']
    proof, rb, original = controller['directory'], controller['rb'], controller['rtl']
    run = SectionRun(run, 'controller-control')
    records = []
    base_frozen = {p.name: gate.digest(p) for p in proof.glob('*.lean')}
    for label, pattern, replacement, operation, port in mutations.mutation_specs():
        directory = root / 'controller-controls' / label
        directory.mkdir(parents=True)
        sv = controller['sv'].read_text()
        if pattern:
            sv, count = re.subn(pattern, replacement, sv)
            if count != 1: raise RuntimeError('Controller mutation must change one use: ' + label)
        candidate = directory / 'candidate.sv'
        candidate.write_text(sv)
        freeze = lambda paths: register_inputs(report, gate, root, paths)
        freeze([candidate])
        actual, _ = gate.import_rtl(run, rb, tools, directory, candidate, label, freeze=freeze)
        if pattern is None and (actual.nodes != original.nodes or actual.next != original.next or
                                actual.outputs != original.outputs):
            raise RuntimeError('Unchanged controller reimport altered complete graph')
        texts = mutations.mutation_sources(rb, actual, operation, port, baseline=original)
        if pattern is None:
            texts['ControllerUnchanged'] = controller_unchanged_source(rb, original)
        for name, text in texts.items(): (directory / (name + '.lean')).write_text(text)
        frozen = {**base_frozen, **{p.name: gate.digest(p) for p in directory.glob('*.lean')}}
        report.setdefault('controller_control_closures', {})[label] = gate.proof_closure(
            config['snapshot'], [directory, proof], list(texts), config['source_sha256'], frozen)
        register_inputs(report, gate, root, directory.rglob('*'))
        selected_run = SectionRun(run, label)
        for name in ('SramMutantGraphs', 'SramMutantModel'):
            gate.compile_lean(selected_run, tools, directory, name, paths=[proof])
        if pattern is None:
            gate.compile_lean(selected_run, tools, directory, 'ControllerUnchanged', paths=[proof])
        gate.compile_lean(selected_run, tools, directory, 'SramReject', paths=[proof],
            reject='error: Type mismatch' if pattern else None)
        records.append(dict(name=label, passed=True, expected_rejection=bool(pattern),
                            universal_all_field_reimport=pattern is None))
    report['controller_controls'] = records


def wrapper_worker(config, run, report, gate):
    import artifact_wrapper_readback as a
    root, snapshot, tools = Path(config['worker_out']), Path(config['snapshot']), config['tool_paths']
    out = root / 'wrappers'
    out.mkdir()
    run = SectionRun(run, 'wrapper')
    run([tools['python'], '-B', 'test/test_artifact_wrapper_readback.py'], 'adapter-boundaries', timeout=120)
    paths = [snapshot / relative for relative in (
        'physical/buffered_sram_serial_wrapper.sv', 'physical/buffered_sram_memory.sv',
        'physical/tt_um_pinwheel_buffered.sv')]
    texts = [path.read_text() for path in paths]
    baseline = a.read_wrappers(*paths)
    (out / 'ArtifactWrapperCertificate.lean').write_text(a.lean_source(baseline))
    register_inputs(report, gate, root, [out / 'ArtifactWrapperCertificate.lean'])
    gate.compile_lean(run, tools, out, 'ArtifactWrapperCertificate')
    controls = []
    for name, index, changes in a.corruption_cases():
        directory = out / name
        directory.mkdir()
        candidates = list(texts)
        for old, new in changes:
            if candidates[index].count(old) != 1:
                raise RuntimeError('Wrapper control must change one actual use: ' + name)
            candidates[index] = candidates[index].replace(old, new)
        files = [directory / path.name for path in paths]
        for file, text in zip(files, candidates): file.write_text(text)
        register_inputs(report, gate, root, files)
        mutant = a.read_wrappers(*files)
        (directory / 'WrapperReject.lean').write_text(a.lean_source(mutant))
        report.setdefault('wrapper_control_closures', {})[name] = gate.proof_closure(
            snapshot, directory, ['WrapperReject'], config['source_sha256'],
            {'WrapperReject.lean': gate.digest(directory / 'WrapperReject.lean')})
        register_inputs(report, gate, root, directory.iterdir())
        rejected = gate.compile_lean(SectionRun(run, name), tools, directory, 'WrapperReject', reject='error:')
        if not re.search(r'error: (Tactic `rfl` failed|(?:Type mismatch|Application type mismatch: The argument)\n\s+rfl\n)', rejected):
            raise RuntimeError('Wrapper control rejected for an unrelated reason: ' + name)
        controls.append(dict(name=name, parsed=True, kernel_rejected=True,
                             reason='unchanged canonical wiring certificate fails rfl'))
    report['wrapper_controls'] = controls
    report['actual_wrapper_sources'] = [str(path.relative_to(snapshot)) for path in paths]
    return out


def full_worker(config, run, report, gate):
    root, snapshot, tools = Path(config['worker_out']), Path(config['snapshot']), config['tool_paths']
    run([tools['lake'], 'build', 'Pinwheel.Hardware.Buffered.ArtifactTinyTapeoutI2cTimingSession',
        'Pinwheel.Hardware.Buffered.ArtifactProgrammableSession',
        'Pinwheel.Hardware.Buffered.ArtifactMixedSession',
        'Pinwheel.Hardware.Buffered.SramArtifactReference', 'Pinwheel.Hardware.Buffered.ArtifactSelection'],
        'fresh-session-library-build', timeout=3600)
    frontend_out = root / 'frontend'
    frontend_out.mkdir()
    front = {}
    gate.frontend_worker(dict(config, worker_out=str(frontend_out)), SectionRun(run, 'frontend'),
                         front, inject_axiom=False)
    report['frontend'] = front
    report['proof_input_sha256_before'] = {'frontend/' + path: value
        for path, value in front['proof_input_sha256_before'].items()}
    controller = controller_worker(config, run, report, gate)
    controller_mutations(config, run, report, gate, controller)
    wrappers = wrapper_worker(config, run, report, gate)
    combined = root / 'combined'
    combined.mkdir()
    frontproof = frontend_out / 'proof'
    controllerproof = controller['directory']
    all_dirs = [combined, frontproof, controllerproof, wrappers]
    texts = {'CombinedArtifactSessionCertificate': combined_source('SramArtifactProof',
        'Pinwheel.Artifact.BufferedSram.step_correct', 'Pinwheel.Artifact.BufferedSram.observe_correct')}
    all_modules = {path.stem for directory in all_dirs for path in directory.glob('*.lean')}
    all_modules |= set(texts)
    template = (snapshot / 'test/ProofAudit.lean').read_text()
    texts['CombinedAudit'] = gate.audit_source(template, all_modules, 'CombinedArtifactSessionCertificate')
    texts['SessionPrivateAxiomControl'] = 'import Init\nprivate axiom untrustedBufferedRtlSession : False\n'
    texts['CombinedRejectAxiom'] = gate.audit_source(template,
        all_modules | {'SessionPrivateAxiomControl'}, 'CombinedArtifactSessionCertificate').replace(
            'import CombinedArtifactSessionCertificate\n',
            'import CombinedArtifactSessionCertificate\nimport SessionPrivateAxiomControl\n')
    for name, text in texts.items(): (combined / (name + '.lean')).write_text(text)
    register_inputs(report, gate, root, [combined / (name + '.lean') for name in texts])
    frozen = {path.name: gate.digest(path) for directory in all_dirs for path in directory.glob('*.lean')}
    roots = ['CombinedArtifactSessionCertificate', 'CombinedAudit', 'CombinedRejectAxiom']
    closure = gate.proof_closure(snapshot, all_dirs, roots, config['source_sha256'], frozen)
    report['full_proof_dependency_closure'] = closure
    for name in ('CombinedArtifactSessionCertificate', 'CombinedAudit', 'SessionPrivateAxiomControl'):
        output = gate.compile_lean(run, tools, combined, name, paths=all_dirs[1:])
        if name == 'CombinedAudit':
            matches = re.findall(r'Pinwheel audit: (\d+) declarations, (\d+) theorems; standard axioms only\.', output)
            if len(matches) != 1: raise RuntimeError('Missing complete full-certificate ownership audit')
            report['audited_declarations'], report['audited_theorems'] = map(int, matches[0])
    rejected = gate.compile_lean(run, tools, combined, 'CombinedRejectAxiom', paths=all_dirs[1:],
                               reject='Unapproved axioms in _private.')
    if 'untrustedBufferedRtlSession' not in rejected:
        raise RuntimeError('Injected private axiom rejected for an unrelated reason')
    report['injected_axiom_rejections'] = 1
    gate.assert_hashes(root, report['proof_input_sha256_before'])
    if gate.proof_closure(snapshot, all_dirs, roots, config['source_sha256'], frozen) != closure:
        raise RuntimeError('Full generated proof closure changed')
    report['proof_inputs_unchanged'] = True
    report['full_session_proved'] = True
