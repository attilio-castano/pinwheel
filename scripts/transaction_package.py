"""Source-bound transaction sessions on the existing emitted paired package.

The shared context owns byte custody and package construction. Callers own
their independent wire peers and acceptance criteria; successful closeout does
not establish board frequency, electrical timing or physical qualification.
"""
from contextlib import contextmanager
from dataclasses import asdict, dataclass, field
import json
from pathlib import Path
import re
import sys
import time

from capability_receipt import CapabilityEvidence
from pad_io import PAD_MAP, PadDrive
from pinwheel_host import Host, PAIRED_FORMAT
from pinwheel_sim import Simulation
from pinwheel_transactions import Transaction, TransactionSpec, compile_transaction
from protocol_tool_closure import ProtocolToolClosure
from validation_run import Commands, fresh_directory, sha


ROOT = Path(__file__).resolve().parents[1]


def _require(condition, message):
    if not condition:
        raise RuntimeError(message)


def _integer(value, low, high, name):
    if type(value) is not int or not low <= value <= high:
        raise ValueError(f'{name} must be an integer in {low}..{high}')


class TransactionCommands(Commands):
    """Keep command identities available even when the session fails."""
    def __call__(self, *args, **kwargs):
        try:
            return super().__call__(*args, **kwargs)
        finally:
            (self.out / 'commands.json').write_text(json.dumps(self.records, indent=2) + '\n')


@dataclass
class PackageRuntime:
    simulation: Simulation
    host: Host
    evidence: CapabilityEvidence
    run: TransactionCommands
    out: Path
    receipt: dict | None = None
    compiled: list = field(default_factory=list)
    _active: bool = True

    def compile(self, spec: TransactionSpec, name: str) -> Transaction:
        """Compile request data in the frozen session and certify its upload."""
        if not self._active:
            raise RuntimeError('The package session has already closed')
        if not isinstance(spec, TransactionSpec):
            raise TypeError('Compile requires a TransactionSpec')
        if not isinstance(name, str) or not re.fullmatch(r'[A-Za-z][A-Za-z0-9_-]*', name):
            raise ValueError('Use a letter followed by letters, numbers, hyphens or underscores in transaction names')
        request_path = self.out / (name + '-request.json')
        if request_path.exists():
            raise FileExistsError('Preserve existing transaction request: ' + str(request_path))
        request_path.write_text(spec.request_json + '\n')
        request_digest = self.evidence.freeze_generated(request_path)

        def exporter(request):
            _require(request == spec.request, 'Frontend callback request differs from its captured request')
            text = self.run([sys.executable, ROOT / 'scripts/export-program.py', request_path],
                            name + '-frontend')
            response = json.loads(text)
            path = self.out / (name + '-frontend.json')
            _require(not path.exists(), 'Preserve existing frontend response')
            path.write_text(text)
            self.evidence.freeze_generated(path)
            return response

        transaction = compile_transaction(spec, exporter=exporter)
        artifact_path = self.out / (name + '-transaction.json')
        _require(not artifact_path.exists(), 'Preserve existing transaction artifact')
        transaction.write(artifact_path)
        artifact_digest = self.evidence.freeze_generated(artifact_path)
        self.evidence.certify(name, transaction.program, self.run)
        self.compiled.append(dict(name=name, request=request_path.name,
            request_sha256=request_digest, artifact=artifact_path.name,
            artifact_sha256=artifact_digest, description=transaction.inspect()))
        return transaction


def _sources():
    return [ROOT / 'Pinwheel.lean', *sorted((ROOT / 'Pinwheel').rglob('*.lean')),
        *sorted((ROOT / 'scripts').rglob('*.py')),
        *sorted((ROOT / 'scripts').rglob('*.lean')),
        *[ROOT / name for name in ('lakefile.toml', 'lake-manifest.json', 'lean-toolchain',
            'test/PairedStreamEmit.lean', 'test/host_bridge.sv', 'test/paired_chip.sv',
            'tools/hardware-toolchain.json', 'tools/storage-macros.json')]]


@contextmanager
def paired_package(tag):
    """Yield one package runtime; populate its receipt after successful closeout.

    This context never publishes report.json. A gate may publish its acceptance
    report only after context exit. Failed attempts and commands are retained.
    """
    out = fresh_directory(ROOT / 'build/host', tag)
    run = TransactionCommands(ROOT, out, default_timeout=600)
    (out / 'commands.json').write_text('[]\n')
    started = time.monotonic()
    runtime = None
    try:
        cad = ROOT / 'build/tools/oss-cad-suite/bin'
        circt = ROOT / 'build/tools/firtool-1.159.0/bin/circt-opt'
        closure = ProtocolToolClosure(ROOT, circt, cad / 'iverilog', cad / 'vvp')
        models = [ROOT / 'build/storage/macros' / name for name in
            ('RM_IHPSG13_1P_512x64_c2_bm_bist.v', 'RM_IHPSG13_1P_core_behavioral_bm_bist.v')]
        lock = json.loads((ROOT / 'tools/storage-macros.json').read_text())['files_sha256']
        _require(all(sha(path) == lock['verilog/' + path.name] for path in models),
                 'Transaction package has unpinned SRAM models')
        evidence = CapabilityEvidence(ROOT, out, _sources(), closure.files, models)
        (out / 'attempt-inputs.json').write_text(json.dumps(dict(status='initial-input-inventory',
            accepted=False, **evidence.identity()), indent=2) + '\n')
        lean_version = run(['lake', 'env', 'lean', '--version'], 'lean-version').strip()
        version = (ROOT / 'lean-toolchain').read_text().strip().split(':v')[-1]
        _require(re.search(r'Lean \(version ' + re.escape(version) + r'(?:,|\s)', lean_version),
                 'Transaction Lean toolchain differs from the pinned version')
        run(['lake', 'build', 'Pinwheel', 'Pinwheel.Program.Requests'], 'build')
        run(['lake', 'env', 'lean', '-DwarningAsError=true', '--run',
             'test/PairedStreamEmit.lean', out], 'emit')
        for path in sorted(out.glob('*.mlir')):
            evidence.freeze_generated(path)
        if (out / 'assembly.json').exists():
            evidence.freeze_generated(out / 'assembly.json')
        rtl = run([circt, out / 'chip.mlir', '--canonicalize', '--lower-seq-to-sv',
            '--lower-hw-to-sv', '--hw-legalize-modules', '--export-verilog', '-o', '/dev/null'], 'export')
        design = out / 'design.sv'
        design.write_text(rtl)
        evidence.freeze_generated(design)
        executable = out / 'host.vvp'
        run([cad / 'iverilog', '-B', closure.backend, '-g2012', '-DFUNCTIONAL', '-s', 'host_bridge',
            '-o', executable, design, ROOT / 'test/host_bridge.sv', ROOT / 'test/paired_chip.sv', *models],
            'compile-simulation')
        evidence.freeze_generated(executable)
        closure.check_executable(executable)
        with Simulation(cad / 'vvp', executable) as simulation:
            runtime = PackageRuntime(simulation, Host(simulation, image_format=PAIRED_FORMAT), evidence, run, out)
            yield runtime
        _require(run(['lake', 'env', 'lean', '--version'], 'lean-version-closeout').strip() == lean_version,
                 'Transaction Lean version changed during the session')
        closure.closeout()
        evidence.closeout()
        runtime.receipt = dict(backend='paired-stream', **evidence.identity(),
            rtl_sha256=sha(design), mlir_sha256=sha(out / 'chip.mlir'), executable_sha256=sha(executable),
            commands=run.records, compiled_transactions=runtime.compiled,
            bundled_tool_closure=closure.identity(), lean_version=lean_version,
            lean_version_unchanged=True, elapsed_seconds=round(time.monotonic() - started, 3),
            pad_map=PAD_MAP,
            boundary='One source/tool/model-bound emitted paired package. Protocol peers and case verdicts '
                'belong to the caller. No board frequency, analog sampling or physical qualification claim.')
    except BaseException as error:
        (out / 'failed-attempt.json').write_text(json.dumps(dict(status='failed', accepted=False,
            backend='paired-stream', error_type=type(error).__name__, error=str(error),
            commands=run.records,
            boundary='Incomplete transaction package attempt; retained commands and artifacts are diagnostic. '
                'Complete source/tool custody and acceptance are unverified.'), indent=2) + '\n')
        raise
    finally:
        if runtime is not None:
            runtime._active = False


@dataclass(frozen=True)
class ConstantInputFixture:
    incoming: int
    open_drain: bool = False

    def __post_init__(self):
        _integer(self.incoming, 0, 3, 'Incoming fixture')
        if type(self.open_drain) is not bool:
            raise ValueError('Open-drain fixture selection must be Boolean')

    def drive(self, cycle, pads, ui):
        if self.open_drain:
            # A high external I2C value releases its linked line; the controller
            # may still pull that resolved line low. This is not a target peer.
            return PadDrive(0, self.incoming ^ 3, links=3)
        return PadDrive(self.incoming, 3)


def run_transaction(tag, transaction, payload=0, incoming=3, timeout_cycles=100_000):
    """Run one bound artifact with constant external inputs, without a target peer."""
    if not isinstance(transaction, Transaction):
        raise TypeError('Run requires a bound Transaction')
    transaction.validate_payload(payload)
    _integer(incoming, 0, 3, 'Incoming fixture')
    _integer(timeout_cycles, 0, sys.maxsize, 'Timeout cycles')
    incoming_artifact = transaction.artifact()
    with paired_package(tag) as package:
        captured = package.out / 'incoming-transaction.json'
        captured.write_text(json.dumps(incoming_artifact, indent=2) + '\n')
        incoming_digest = package.evidence.freeze_generated(captured)
        compiled = package.compile(transaction.spec, 'transaction')
        _require(compiled.artifact() == incoming_artifact,
                 'Transaction artifact differs from compilation inside the frozen package session')
        package.host.reset()
        loaded = compiled.load(package.host)
        package.simulation.device = ConstantInputFixture(incoming, compiled.pins.open_drain)
        before = package.host.edges
        result = loaded.run(payload=payload, timeout_cycles=timeout_cycles)
        package.simulation.device = None
        observation = asdict(package.simulation.observation)
        host_run_edges = package.host.edges - before
    report = dict(action='transaction-run', **package.receipt,
        transaction=compiled.artifact(), incoming_artifact_sha256=incoming_digest,
        artifact_binding_recompiled=True, payload=payload,
        constant_external_input=incoming, result=asdict(result),
        host_run_edges=host_run_edges, edges=package.host.edges, frames=package.host.frames,
        edge_count_boundary='host_run_edges includes START preflight/framing, busy polling, readback and consume; '
            'it is not the protocol wire duration.',
        final_observation=observation,
        run_boundary='Constant external drivers only; I2C high means release through the declared links. '
            'No protocol target reply or independent waveform acceptance is supplied by this command.')
    path = package.out / 'report.json'
    _require(not path.exists(), 'Preserve existing transaction report')
    path.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(dict(result=report['result'], host_run_edges=host_run_edges, report=str(path)), indent=2))
    return report
