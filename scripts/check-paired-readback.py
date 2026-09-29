#!/usr/bin/env python3
"""Interpret retained paired RTL and kernel-check its typed/session meaning."""
import argparse
from datetime import datetime, timezone
import json
from pathlib import Path
import re
import sys
import time

import paired_readback as pr
from validation_run import Commands, fresh_directory, sha

ROOT = Path(__file__).resolve().parents[1]
YOSYS = ROOT / 'build/tools/oss-cad-suite/bin/yosys'
SOLVER = ROOT / 'build/tools/oss-cad-suite/bin/z3'


class ScopedCommands(Commands):
    """Keep receipt labels unique across modules and independent fault fixtures."""
    def __init__(self, *args, scope='', **kwargs):
        super().__init__(*args, **kwargs)
        self.scope = scope

    def __call__(self, command, label, *args, **kwargs):
        index = len(self.records)
        try:
            return super().__call__(command, label, *args, **kwargs)
        finally:
            if len(self.records) > index:
                self.records[index]['label'] = self.scope + label
                self.records[index]['log'] = str((self.out / (label + '.log')).relative_to(ROOT))


def qualified(text, kind):
    suffix = 'Core' if kind == 'core' else 'Package'
    return pr.adapt(text).replace('Pinwheel.Artifact.Paired', 'Pinwheel.Artifact.Paired.' + suffix)


def compile_lean(run, directory, name, paths=(), reject=None):
    return run(['env', 'LEAN_PATH=' + ':'.join(map(str, [directory, *paths])),
                'lake', 'env', 'lean', '-DwarningAsError=true', '-DmaxErrors=1',
                '-o', directory / (name + '.olean'), directory / (name + '.lean')],
               name, timeout=600, reject=reject)


def import_rtl(rb, run, directory, rtl):
    script = directory / 'import.ys'
    script.write_text('\n'.join([f'read_verilog -sv "{rtl}"',
        f'hierarchy -check -top {rb.TOP}', 'proc', 'pmuxtree', 'opt_clean',
        'check -assert', f'write_json "{directory / "import.json"}"', '']))
    run([YOSYS, '-Q', '-T', '-s', script], 'import')
    pr.read_json(directory / 'import.json')  # Reject duplicate keys before interpreting it.
    return rb.read_rtl(directory / 'import.json')


def generate(rb, source, rtl, cuts, pairs, kind):
    texts = {
        'Design': pr.design_source(rb, kind),
        'Hints': rb.HEADER + source.definitions('Source') + 'end Pinwheel.Artifact.Paired\n',
        'Graphs': 'import Hints\n' + rb.HEADER + rtl.definitions('RTL') + 'end Pinwheel.Artifact.Paired\n',
        'HintEquations': pr.hint_equations_source(rb, source, cuts, kind),
        'Equations': pr.equations_source(rb, cuts, kind),
        'Sources': pr.sources_source(rb, source, kind),
        'LocalProofs': pr.helper_source(rb, pairs),
        'Links': pr.links_source(rb, source, rtl, pairs),
        'Model': pr.model_source(rb, rtl, kind),
        'Endpoints': pr.endpoints_source(rb, source, rtl, pairs, kind),
        'Proof': pr.proof_source(rb, kind),
    }
    if kind == 'chip':
        texts['Session'] = pr.session_source(rb)
    texts['Audit'] = (ROOT / 'test/ProofAudit.lean').read_text().replace(
        'import Pinwheel\n', 'import Pinwheel\nimport ' + ('Session' if kind == 'chip' else 'Proof') + '\n')
    # Only the reused backend graph/link generator assumes the core interface.
    # Design's package-to-core projections must retain their core return types.
    return {name: qualified(pr.adapt(text, kind) if name in ('Hints', 'Graphs', 'Links') else text, kind)
            for name, text in texts.items()}


def mutations(rb, directory, rtl_text, kind, commands):
    tests = [('unchanged', None, None, 'next', 'r_active')]
    if kind == 'core':
        tests += [
            ('upload-cursor', r'r_cursor\s*<=\s*[^;]+;', "r_cursor <= 9'h0;", 'next', 'r_cursor'),
            ('parameter-bank', r'r_parameter_b1_w31\s*<=\s*[^;]+;',
             "r_parameter_b1_w31 <= 20'h0;", 'next', 'r_parameter_b1_w31'),
            ('sram-write', r'assign mem_write\s*=\s*[^;]+;',
             "assign mem_write = 1'b0;", 'output', 'mem_write')]
    else:
        tests += [
            ('sampler', r'r_pin_second_init\s*<=\s*[^;]+;',
             'r_pin_second_init <= ~r_pin_first_init;', 'next', 'r_pin_second_init'),
            ('mailbox-valid', r'r_result_valid\s*<=\s*[^;]+;',
             "r_result_valid <= 1'b0;", 'next', 'r_result_valid'),
            ('package-output', r'assign uo_out\s*=\s*[^;]+;',
             'assign uo_out = ~casez_tmp_1;', 'output', 'uo_out')]
    for name, pattern, replacement, operation, port in tests:
        out = directory / 'mutations' / name
        out.mkdir(parents=True)
        run = ScopedCommands(ROOT, out, commands, default_timeout=180,
                             scope=kind + '.mutations.' + name + '.')
        text = rtl_text
        if pattern:
            text, count = re.subn(pattern, replacement, text)
            if count != 1:
                raise ValueError('Mutation must change exactly one statement: ' + name)
        rtl_path = out / 'candidate.sv'
        rtl_path.write_text(text)
        graph = import_rtl(rb, run, out, rtl_path)
        (out / 'MutantGraphs.lean').write_text(qualified(pr.adapt(
            rb.HEADER + graph.definitions('Mutant') + 'end Pinwheel.Artifact.Paired\n', kind), kind))
        model = pr.model_source(rb, graph, kind).replace('import Graphs', 'import MutantGraphs').replace(
            'RTL.', 'Mutant.').replace('rtlStep', 'mutantStep').replace('rtlObserve', 'mutantObserve').replace(
            'rtlComponent', 'mutantComponent')
        (out / 'MutantModel.lean').write_text(qualified(model, kind))
        itype = 'Input' if kind == 'core' else '(SramController.Reads Chip.Pin)'
        rtype = 'Register' if kind == 'core' else 'FullRegister'
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
        (out / 'Reject.lean').write_text(qualified(proof, kind))
        for module in ['MutantGraphs', 'MutantModel']:
            compile_lean(run, out, module, [directory])
        compile_lean(run, out, 'Reject', [directory], reject='error: Type mismatch' if pattern else None)
    return [test[0] for test in tests]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--tag', required=True)
    args = parser.parse_args()
    out = fresh_directory(ROOT / 'build/validation', args.tag)
    run = ScopedCommands(ROOT, out, default_timeout=600)
    started = time.monotonic()
    report = dict(schema=1, status='running', date=datetime.now(timezone.utc).isoformat(),
        commands=run.records, modules={}, placement_or_routing=False,
        scope='Exact retained raw controller and package RTL; all represented state and inputs; '
              'two-state positive-edge semantics. SRAM response is an independent input. '
              'Certified serial upload and E64 execution remain conditional on the explicit SRAM '
              'law, reset/release, digital delivery and execution-segment premises.')
    inputs = {}
    def retain(path, expected=None):
        path = ROOT / path
        digest = sha(path)
        if expected is not None and digest != expected:
            raise ValueError('Changed retained input: ' + str(path))
        inputs[str(path.relative_to(ROOT))] = digest
        return path
    try:
        mapping_path = retain('physical/experiments/paired-validation-mapping.json')
        mapping = pr.read_json(mapping_path)
        mapping_report_path = retain(mapping['report'], mapping['report_sha256'])
        mapping_report = pr.read_json(mapping_report_path)
        formal_path = retain('physical/experiments/paired-admission-results.json')
        formal = pr.read_json(formal_path)
        formal_report_path = retain(formal['report']['path'], formal['report']['sha256'])
        formal_report = pr.read_json(formal_report_path)
        if mapping['implementation'] != 'PairedValidation' or any(
                x['status'] != 'passed' for x in [mapping, mapping_report, formal_report]):
            raise ValueError('Expected passing retained mapping and formal reports')
        for path, digest in formal_report['source_sha256'].items():
            retain(path, digest)
        for name in ['scripts/check-paired-readback.py', 'scripts/paired_readback.py',
                     'scripts/backend_readback.py', 'test/PairedReadback.lean',
                     'test/test_paired_readback.py']:
            retain(name)
        artifacts = {}
        retained = out / 'retained'
        retained.mkdir()
        for name in ['core.mlir', 'chip.mlir', 'core.sv', 'chip.sv', 'assembly.json']:
            path = mapping_report_path.parent / name
            key = str(path.relative_to(ROOT))
            retain(key, mapping_report['artifact_sha256'][key])
            (retained / name).write_bytes(path.read_bytes())
            artifacts[name] = {'path': key, 'sha256': inputs[key]}
        report.update(source_sha256=inputs, retained_artifacts=artifacts,
            previous_gate={'path': str(formal_path.relative_to(ROOT)), 'sha256': sha(formal_path)},
            tools_sha256={str(p.relative_to(ROOT)): sha(p) for p in [YOSYS, SOLVER]})
        for path in [YOSYS, SOLVER]:
            retain(path)
        run(['lake', 'build'], 'build')
        report['lean'] = run(['lake', 'env', 'lean', '--version'], 'lean-version').strip()
        run([YOSYS, '-V'], 'yosys-version')
        run([SOLVER, '-version'], 'z3-version')
        for optimized in [False, True]:
            run([sys.executable, *(['-O'] if optimized else []), '-m', 'unittest', 'discover',
                 '-s', 'test', '-p', 'test_paired_readback.py', '-v'], 'guards' + ('-optimized' if optimized else ''))
        emitted = out / 'emitted'
        run(['lake', 'env', 'lean', '--run', 'test/PairedValidationEmit.lean', emitted], 'emit')
        for name in ['core.mlir', 'chip.mlir', 'assembly.json']:
            if sha(emitted / name) != artifacts[name]['sha256']:
                raise ValueError('Current typed emission differs from retained artifact: ' + name)
        run(['lake', 'env', 'lean', '--run', 'test/PairedReadback.lean', out / 'hints'], 'hint-labels')
        interface = pr.read_json(retained / 'assembly.json')
        for kind in ['core', 'chip']:
            directory = out / kind
            directory.mkdir()
            check = ScopedCommands(ROOT, directory, run.records, default_timeout=600, scope=kind + '.')
            rb = pr.backend(kind)
            pr.check_interface(rb, interface[kind])
            source = rb.read_hints(retained / (kind + '.mlir'))
            rtl = import_rtl(rb, check, directory, retained / (kind + '.sv'))
            cuts = pr.read_json(out / 'hints' / (kind + '-cuts.json'))
            pr.check_cuts(cuts, source)
            rb.add_storage_views(rtl, source)
            pairs = pr.partitions(rb, source, rtl, SOLVER)
            (directory / 'partitions.json').write_text(json.dumps([
                {k: v for k, v in p.items() if k not in ('left', 'right')} for p in pairs], indent=2) + '\n')
            for name, text in generate(rb, source, rtl, cuts, pairs, kind).items():
                (directory / (name + '.lean')).write_text(text)
                output = compile_lean(check, directory, name)
                if name == 'Audit':
                    match = re.search(r'Pinwheel audit: (\d+) declarations, (\d+) theorems;', output)
                    if not match:
                        raise ValueError('Missing generated-circuit axiom audit')
                    audit = dict(declarations=int(match[1]), theorems=int(match[2]), standard_axioms_only=True)
            negative = (directory / 'Audit.lean').read_text().removesuffix('#audit_pinwheel\n')
            negative += 'axiom Pinwheel.CI.untrustedReadback : False\n#audit_pinwheel\n'
            (directory / 'RejectAxiom.lean').write_text(negative)
            compile_lean(check, directory, 'RejectAxiom', reject='Unapproved axioms in Pinwheel.CI.untrustedReadback')
            controls = mutations(rb, directory, (retained / (kind + '.sv')).read_text(), kind, run.records)
            report['modules'][kind] = dict(top=rb.TOP, registers=len(rb.REGISTERS),
                register_bits=sum(w for w, _ in rb.REGISTERS.values()), outputs=len(rb.OUTPUTS),
                output_bits=sum(w for w, _ in rb.OUTPUTS.values()), shared_equations=len(cuts),
                local_equalities=len(pairs), audit=audit, mutation_controls=controls,
                component_theorem='Pinwheel.Artifact.Paired.' + ('Core' if kind == 'core' else 'Package') + '.component_correct')
        report['session_theorem'] = 'Pinwheel.Artifact.Paired.Package.rtl_initialized_session'
        if any(sha(ROOT / path) != digest for path, digest in inputs.items()):
            raise ValueError('An input changed during validation')
        report.update(status='passed', inputs_unchanged=True)
    except BaseException as error:
        report.update(status='failed', error=str(error))
        raise
    finally:
        report['seconds'] = round(time.monotonic() - started, 3)
        report['artifact_sha256'] = {str(p.relative_to(ROOT)): sha(p) for p in sorted(out.rglob('*'))
            if p.is_file() and p.name != 'report.json' and p.suffix != '.olean'}
        (out / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({'report': str(out / 'report.json'), 'status': report['status'],
                      'seconds': report['seconds'], 'modules': report['modules']}, indent=2))


if __name__ == '__main__':
    main()
