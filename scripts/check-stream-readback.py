#!/usr/bin/env python3
"""Fresh universal RTL interpretation for the opt-in UART stream candidate."""
import argparse
from datetime import datetime, timezone
import importlib.util
import json
from pathlib import Path
import re
import sys
import time

import stream_readback as sr
from protocol_tool_closure import ProtocolToolClosure
from validation_run import fresh_directory, sha

ROOT = Path(__file__).resolve().parents[1]
# Reuse command/import/mutation mechanics in a private module instance. Its
# original retained runner remains unchanged, including its narrower interface.
spec = importlib.util.spec_from_file_location('_stream_readback_commands', ROOT / 'scripts/check-paired-readback.py')
commands = importlib.util.module_from_spec(spec)
spec.loader.exec_module(commands)
commands.pr = sr
CIRCT, YOSYS, SOLVER = commands.CIRCT, commands.YOSYS, commands.SOLVER
IVERILOG = ROOT / 'build/tools/oss-cad-suite/bin/iverilog'
VVP = ROOT / 'build/tools/oss-cad-suite/bin/vvp'


def current_sources():
    return [ROOT / 'Pinwheel.lean', *sorted((ROOT / 'Pinwheel').rglob('*.lean')),
        *sorted((ROOT / 'scripts').glob('*.py')), *sorted((ROOT / 'test').glob('*.lean')),
        *sorted((ROOT / 'test').glob('*.py')),
        *[ROOT / n for n in ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json', 'tools/hardware-toolchain.json']]]


def generate(rb, source, rtl, cuts, pairs, kind):
    texts = sr.generate(rb, source, rtl, cuts, pairs, kind)
    texts['Audit'] = (ROOT / 'test/ProofAudit.lean').read_text().replace('import Pinwheel\n', 'import Pinwheel\nimport Proof\n')
    return {n: commands.qualified(t, kind) for n, t in texts.items()}


def import_rtl_frozen(rb, run, directory, rtl, freeze):
    """Bind the exact SV, import script and JSON before their respective uses."""
    rtl = Path(rtl)
    freeze(rtl)
    script, imported = directory / 'import.ys', directory / 'import.json'
    script.write_text('\n'.join([f'read_verilog -sv "{rtl}"',
        f'hierarchy -check -top {rb.TOP}', 'proc', 'pmuxtree', 'opt_clean',
        'check -assert', f'write_json "{imported}"', '']))
    freeze(script)
    run([YOSYS, '-Q', '-T', '-s', script], 'import')
    freeze(rtl)
    freeze(script)
    freeze(imported)
    sr.read_json(imported)  # Duplicate-key rejection applies to the frozen bytes.
    graph = rb.read_rtl(imported)
    freeze(imported)
    return graph


def mutation_control(rb, directory, rtl_text, kind, records, name, operation, port,
                     pattern=None, replacement=None, *, freeze, compile_lean):
    mutated = rtl_text
    if pattern is not None:
        mutated, count = re.subn(pattern, replacement, rtl_text)
        if count != 1:
            raise ValueError('Mutation must change exactly one statement: ' + name)
    out = directory / 'mutations' / name
    out.mkdir(parents=True)
    run = commands.ScopedCommands(ROOT, out, records, default_timeout=180, scope=kind + '.mutations.' + name + '.')
    path = out / 'candidate.sv'
    path.write_text(mutated)
    graph = import_rtl_frozen(rb, run, out, path, freeze)
    (out / 'MutantGraphs.lean').write_text(commands.qualified(sr.adapt(
        rb.HEADER + graph.definitions('Mutant') + 'end Pinwheel.Artifact.Paired\n', kind), kind))
    model = sr.model_source(rb, graph, kind).replace('import Graphs', 'import MutantGraphs').replace(
        'RTL.', 'Mutant.').replace('rtlStep', 'mutantStep').replace('rtlObserve', 'mutantObserve').replace('rtlComponent', 'mutantComponent')
    (out / 'MutantModel.lean').write_text(commands.qualified(model, kind))
    itype, rtype = ('Input', 'Register') if kind == 'core' else ('(SramController.Reads Chip.Pin)', 'FullRegister')
    ctor = (rb.REGISTERS if operation == 'next' else rb.OUTPUTS)[port][1]
    method, action = ('mutantStep', 'step') if operation == 'next' else ('mutantObserve', 'observe')
    proof = f'''import Proof
import MutantModel
{rb.HEADER}
theorem candidate_correct (i : Values {itype}) (s : Values {rtype}) :
    {method} i s ({ctor}) = reference.{action} i s ({ctor}) := by
  exact model_{operation} i s ({ctor})
end Pinwheel.Artifact.Paired
'''
    (out / 'Reject.lean').write_text(commands.qualified(proof, kind))
    for module in ('MutantGraphs', 'MutantModel'):
        compile_lean(run, out, module, [directory])
    compile_lean(run, out, 'Reject', [directory], reject='error: Type mismatch' if pattern else None)
    return name


def mutation_controls(rb, directory, rtl_text, kind, records, *, freeze, compile_lean):
    tests = [('unchanged', 'next', 'r_active', None, None)]
    if kind == 'core':
        tests += [
            ('upload-cursor', 'next', 'r_cursor', r'r_cursor\s*<=\s*[^;]+;', "r_cursor <= 9'h0;"),
            ('parameter-bank', 'next', 'r_parameter_b1_w31', r'r_parameter_b1_w31\s*<=\s*[^;]+;', "r_parameter_b1_w31 <= 20'h0;"),
            ('sram-write', 'output', 'mem_write', r'assign mem_write\s*=\s*[^;]+;', "assign mem_write = 1'b0;")]
    else:
        tests += [
            ('sampler', 'next', 'r_pin_second_init', r'r_pin_second_init\s*<=\s*[^;]+;', 'r_pin_second_init <= ~r_pin_first_init;'),
            ('mailbox-valid', 'next', 'r_result_valid', r'r_result_valid\s*<=\s*[^;]+;', "r_result_valid <= 1'b0;"),
            ('package-output', 'output', 'uo_out', r'assign uo_out\s*=\s*([^;]+);', lambda m: 'assign uo_out = ~(' + m.group(1) + ');')]
    tests += [('stream-enabled', 'next', 'r_stream_enabled', r'r_stream_enabled\s*<=\s*[^;]+;', "r_stream_enabled <= 1'b0;")]
    return [mutation_control(rb, directory, rtl_text, kind, records, name, operation, port, pattern, replacement,
                             freeze=freeze, compile_lean=compile_lean)
            for name, operation, port, pattern, replacement in tests]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--tag', required=True)
    parser.add_argument('--proof-timeout-seconds', type=int, default=600,
                        help='Per Lean module compilation bound, 1..3600 (default: 600)')
    args = parser.parse_args()
    if not 1 <= args.proof_timeout_seconds <= 3600:
        parser.error('proof-timeout-seconds must be 1..3600')
    out = fresh_directory(ROOT / 'build/validation', args.tag)
    run = commands.ScopedCommands(ROOT, out, default_timeout=600)
    started = time.monotonic()
    source_hashes = {str(p.relative_to(ROOT)): sha(p) for p in current_sources()}
    consumed = {}
    def freeze(path):
        path = Path(path)
        key, digest = str(path.relative_to(ROOT)), sha(path)
        if key in consumed and consumed[key] != digest:
            raise ValueError('Consumed generated input changed: ' + key)
        consumed[key] = digest
        return digest
    original_compile = commands.compile_lean
    compiled_modules = []
    def compile_frozen(run, directory, name, paths=(), reject=None):
        imported_directories = {Path(directory), *(Path(path) for path in paths)}
        dependencies = [path for path in compiled_modules if path.parent in imported_directories]
        for path in dependencies:
            freeze(path)
        freeze(directory / (name + '.lean'))
        def bounded(command, label, *positional, **options):
            options['timeout'] = args.proof_timeout_seconds
            index = len(run.records)
            try:
                return run(command, label, *positional, **options)
            finally:
                if len(run.records) > index:
                    run.records[index]['timeout_seconds'] = args.proof_timeout_seconds
        result = original_compile(bounded, directory, name, paths, reject)
        freeze(directory / (name + '.lean'))
        for path in dependencies:
            freeze(path)
        if reject is None:
            output = directory / (name + '.olean')
            freeze(output)
            compiled_modules.append(output)
        return result
    closure = ProtocolToolClosure(ROOT, CIRCT, IVERILOG, VVP)
    tool_files = [*closure.files, YOSYS, SOLVER, YOSYS.parent.parent / 'libexec/yosys', SOLVER.parent.parent / 'libexec/z3']
    tool_hashes = {str(p.relative_to(ROOT)): sha(p.resolve()) for p in tool_files}
    report = dict(schema=1, implementation='PairedStream', status='running',
        proof_timeout_seconds=args.proof_timeout_seconds,
        date=datetime.now(timezone.utc).isoformat(), source_sha256=source_hashes,
        tools_sha256=tool_hashes, commands=run.records, modules={},
        placement_or_routing=False, cad_seconds=0,
        scope='Fresh core and package RTL equals the exact typed stream supervisor and reused paired graph for all '
            'represented state and inputs under two-state positive-edge semantics. SRAM response remains an '
            'independent input. No initialized continuous package execution or analog/physical theorem is inferred.')
    try:
        run(['lake', 'build'], 'build')
        report['lean'] = run(['lake', 'env', 'lean', '--version'], 'lean-version').strip()
        expected = (ROOT / 'lean-toolchain').read_text().strip().split(':v')[-1]
        if not re.search(r'Lean \(version ' + re.escape(expected) + r'(?:,|\s)', report['lean']):
            raise ValueError('Wrong Lean toolchain')
        for tool, flag, name in [(CIRCT, '--version', 'circt'), (YOSYS, '-V', 'yosys'), (SOLVER, '-version', 'z3')]:
            run([tool, flag], name + '-version')
        for optimized in (False, True):
            run([sys.executable, *(['-O'] if optimized else []), '-B', '-m', 'unittest', 'discover',
                '-s', 'test', '-p', 'test_stream_readback.py', '-v'], 'guards' + ('-optimized' if optimized else ''))
        emitted = out / 'emitted'
        run(['lake', 'env', 'lean', '-DwarningAsError=true', '--run', 'test/PairedStreamEmit.lean', emitted], 'emit')
        for name in ('core.mlir', 'chip.mlir', 'assembly.json'):
            freeze(emitted / name)
        def retain(path):
            return Path(path)
        report['emitted_artifacts'] = commands.fresh_rtl(run, emitted, retain)
        for name in ('core.sv', 'chip.sv'):
            freeze(emitted / name)
        run(['lake', 'env', 'lean', '-DwarningAsError=true', '--run', 'test/PairedStreamReadback.lean', out / 'hints'], 'hint-labels')
        interface = sr.read_json(emitted / 'assembly.json')
        for kind in ('core', 'chip'):
            directory = out / kind
            directory.mkdir()
            check = commands.ScopedCommands(ROOT, directory, run.records, default_timeout=600, scope=kind + '.')
            rb = sr.backend(kind)
            sr.check_interface(rb, interface[kind])
            source = rb.read_hints(emitted / (kind + '.mlir'))
            rtl = import_rtl_frozen(rb, check, directory, emitted / (kind + '.sv'), freeze)
            cuts_path = out / 'hints' / (kind + '-cuts.json')
            freeze(cuts_path)
            cuts = sr.read_json(cuts_path)
            freeze(cuts_path)
            sr.check_cuts(cuts, source)
            rb.add_storage_views(rtl, source)
            pairs = sr.partitions(rb, source, rtl, SOLVER)
            (directory / 'partitions.json').write_text(json.dumps([
                {k: v for k, v in p.items() if k not in ('left', 'right')} for p in pairs], indent=2) + '\n')
            for name, text in generate(rb, source, rtl, cuts, pairs, kind).items():
                (directory / (name + '.lean')).write_text(text)
                output = compile_frozen(check, directory, name)
                if name == 'Audit':
                    match = re.search(r'Pinwheel audit: (\d+) declarations, (\d+) theorems;', output)
                    if not match:
                        raise ValueError('Missing generated-circuit axiom audit')
                    audit = dict(declarations=int(match[1]), theorems=int(match[2]), standard_axioms_only=True)
            negative = (directory / 'Audit.lean').read_text().removesuffix('#audit_pinwheel\n')
            negative += 'axiom Pinwheel.CI.untrustedReadback : False\n#audit_pinwheel\n'
            (directory / 'RejectAxiom.lean').write_text(negative)
            compile_frozen(check, directory, 'RejectAxiom', reject='Unapproved axioms in Pinwheel.CI.untrustedReadback')
            controls = mutation_controls(rb, directory, (emitted / (kind + '.sv')).read_text(), kind, run.records,
                                        freeze=freeze, compile_lean=compile_frozen)
            report['modules'][kind] = dict(top=rb.TOP, registers=len(rb.REGISTERS),
                register_bits=sum(w for w, _ in rb.REGISTERS.values()), outputs=len(rb.OUTPUTS),
                shared_equations=len(cuts), local_equalities=len(pairs), audit=audit,
                mutation_controls=controls,
                component_theorem='Pinwheel.Artifact.Paired.' + ('Core' if kind == 'core' else 'Package') + '.component_correct')
        closure.closeout()
        for table in (source_hashes, tool_hashes, consumed):
            if any(sha((ROOT / path).resolve()) != digest for path, digest in table.items()):
                raise ValueError('An input changed during validation')
        report.update(status='passed', inputs_unchanged=True, tool_closure=closure.identity(),
            consumed_generated_sha256=consumed)
    except BaseException as error:
        report.update(status='failed', error=str(error))
        raise
    finally:
        report['seconds'] = round(time.monotonic() - started, 3)
        report['artifact_sha256'] = {str(p.relative_to(ROOT)): sha(p) for p in sorted(out.rglob('*'))
            if p.is_file() and p.name != 'report.json' and p.suffix != '.olean'}
        (out / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({'report': str(out / 'report.json'), 'status': report['status'], 'seconds': report['seconds'],
        'modules': report['modules']}, indent=2))


if __name__ == '__main__':
    main()
