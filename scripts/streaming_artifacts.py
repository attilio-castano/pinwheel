"""Streaming raw-artifact certificate worker; acceptance is always kernel checked.

The callable worker is reused inside a fresh committed-source coordinator.
The direct CLI is exploratory and labels its report unqualified.
"""
import argparse
from contextlib import redirect_stdout
import hashlib
import importlib.util
import json
import io
import re
from pathlib import Path
import sys
import time

import streaming_readback as adapter
from buffered_rtl_session_full import recorded_solver
from validation_run import Commands

ROOT = Path(__file__).resolve().parents[1]
MODULES = ('Hints','Sources','Graphs','LocalProofs','Links','Model','Endpoints','Proof')


def controls(rb, rtl, sv, prefix, proof, out, tools, run, report, gate, freeze):
    """Actual RTL mutation controls and a module-owned private-axiom control."""
    records = []
    roots = []
    for label,pattern,replacement,operation in adapter.mutation_specs(rb.KIND):
        directory = out/'controls'/label
        directory.mkdir(parents=True)
        value = sv.read_text()
        if pattern is not None:
            value,changes = re.subn(pattern,replacement,value)
            if changes != 1:
                raise RuntimeError('Streaming mutation did not change exactly one driver: '+label)
        candidate = directory/'candidate.sv'
        candidate.write_text(value)
        freeze([candidate])
        graph,_ = gate.import_rtl(run,rb,tools,directory,candidate,'control-'+label,freeze=freeze)
        adapter.shared.validate_graph(rb,graph)
        equal = graph.nodes == rtl.nodes and graph.next == rtl.next and graph.outputs == rtl.outputs
        if equal != (pattern is None):
            raise RuntimeError('Mutation has unexpected graph equality: '+label)
        texts = adapter.mutation_sources(rb,graph,operation)
        for name,text in texts.items():
            (directory/(prefix+name+'.lean')).write_text(adapter.prefix_imports(text,prefix))
        freeze(directory.glob('*.lean'))
        def control_run(command,name,**options):
            return run(command,label+'-'+name,**options)
        for name in ('MutantGraphs','MutantModel'):
            gate.compile_lean(control_run,tools,directory,prefix+name,paths=[proof])
        gate.compile_lean(control_run,tools,directory,prefix+'Reject',paths=[proof],
            reject=None if pattern is None else 'error: Type mismatch')
        records.append(dict(name=label,passed=True,all_state_reimport=pattern is None,
            expected_rejection=pattern is not None,operation=operation,
            proof_directory=str(directory),modules=[prefix+n for n in texts]))
        roots += [dict(directory=str(directory),module=prefix+n) for n in texts]
    template = (ROOT/'test/ProofAudit.lean').read_text()
    private = prefix+'PrivateAxiom'
    reject = prefix+'RejectAxiom'
    (proof/(private+'.lean')).write_text('import Init\nprivate axiom untrustedStreamingArtifact : False\n')
    audit = gate.audit_source(template,[prefix+n for n in MODULES]+[private],root_module=prefix+'Proof')
    (proof/(reject+'.lean')).write_text(audit.replace('import '+prefix+'Proof\n',
        'import '+prefix+'Proof\nimport '+private+'\n'))
    freeze([proof/(private+'.lean'),proof/(reject+'.lean')])
    gate.compile_lean(run,tools,proof,private)
    output = gate.compile_lean(run,tools,proof,reject,reject='Unapproved axioms in _private.')
    if 'untrustedStreamingArtifact' not in output:
        raise RuntimeError('Private axiom rejected for an unrelated declaration')
    report.update(mutations=records,private_axiom_rejected=True,control_proof_roots=roots,
        private_control_modules=[private,reject])


class QuietSolver:
    def __init__(self,run):
        self.run = run

    def __call__(self,command,label,**options):
        with redirect_stdout(io.StringIO()):
            return self.run(command,label,**options)


def load_gate():
    name = '_streaming_shared_artifact_gate'
    spec = importlib.util.spec_from_file_location(name, ROOT/'scripts/check-buffered-rtl-session.py')
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def component(kind, addr_bits, emitted, out, tools, run, *, gate=None):
    gate = load_gate() if gate is None else gate
    emitted, out = Path(emitted), Path(out)
    out.mkdir(parents=True, exist_ok=False)
    proof = out/'proof'
    proof.mkdir()
    report = dict(passed=False, kind=kind, addr_bits=addr_bits,
        boundary='All raw two-state register and output equations; no standalone initialized source-session claim.')
    started = time.monotonic()
    freeze = lambda paths: gate.freeze_inputs(report,out,paths)
    # Inputs outside this component's directory are inventoried before use too.
    input_hashes = {str(p.resolve()):gate.digest(p) for p in emitted.iterdir() if p.is_file()}
    report['emitted_input_sha256_before'] = input_hashes
    try:
        rb = adapter.backend(kind,addr_bits)
        prefix = ('CoreD'+str(2**addr_bits)) if kind=='core' else 'QuadFrontend'
        stem = 'core' if kind=='core' else 'frontend'
        mlir = emitted/(stem+'.mlir')
        assembly = emitted/('assembly.json' if kind=='core' else 'frontend-assembly.json')
        adapter.check_interface(rb,assembly)
        source = adapter.shared.validate_graph(rb,rb.read_hints(mlir))
        sv = out/(stem+'.sv')
        sv.write_text(run([tools['circt'],mlir,'--canonicalize','--lower-seq-to-sv',
            '--lower-hw-to-sv','--hw-legalize-modules','--export-verilog','-o','/dev/null'],
            'circt-export',timeout=180))
        freeze([sv])
        rtl, imported = gate.import_rtl(run,rb,tools,out,sv,'import-rtl',freeze=freeze)
        adapter.shared.validate_graph(rb,rtl)
        with recorded_solver(rb,tools['solver'],QuietSolver(run),out/'smt-proposals',freeze=freeze) as query_count:
            pairs = adapter.shared.partitions(rb,source,rtl,tools['solver'])
            pairs = adapter.shared.comparison_abstractions(rb,pairs,tools['solver'])
            pairs = adapter.boolean_abstractions(rb,pairs,tools['solver'])
            report['smt_proposals'] = query_count()
        gate.write_json(out/'partitions.json',pairs)
        freeze([out/'partitions.json'])
        texts = dict(Hints=adapter.hints_source(rb,source), Sources=adapter.sources_source(rb,source),
            Graphs=adapter.graphs_source(rb,rtl),LocalProofs=adapter.helper_source(rb,pairs),
            Links=adapter.links_source(rb,source,rtl,pairs),Model=adapter.model_source(rb,rtl),
            Endpoints=adapter.endpoints_source(rb,source,rtl,pairs),Proof=adapter.proof_source(rb))
        for name,text in texts.items():
            (proof/(prefix+name+'.lean')).write_text(adapter.prefix_imports(text,prefix))
        freeze(proof.glob('*.lean'))
        for name in MODULES:
            gate.compile_lean(run,tools,proof,prefix+name)
        selected_modules = [prefix+name for name in MODULES]
        audit = gate.audit_source((ROOT/'test/ProofAudit.lean').read_text(),selected_modules,root_module=prefix+'Proof')
        (proof/(prefix+'Audit.lean')).write_text(audit)
        freeze([proof/(prefix+'Audit.lean')])
        report['axiom_audit'] = gate.compile_lean(run,tools,proof,prefix+'Audit').strip()
        controls(rb,rtl,sv,prefix,proof,out,tools,run,report,gate,freeze)
        report.update(passed=True,registers=len(rb.REGISTERS),
            state_bits=sum(w for w,_ in rb.REGISTERS.values()),outputs=len(rb.OUTPUTS),
            source_nodes=len(source.nodes),rtl_nodes=len(rtl.nodes),partitions=len(pairs),
            compiled_modules=selected_modules,all_state=True,all_outputs=True)
    except BaseException as error:
        report['error'] = type(error).__name__+': '+str(error)
        raise
    finally:
        report['elapsed_seconds'] = round(time.monotonic()-started,3)
        try:
            if {path:gate.digest(path) for path in input_hashes} != input_hashes:
                raise RuntimeError('Emitted input changed during component proof')
            gate.assert_hashes(out,report.get('proof_input_sha256_before',{}))
            report['frozen_inputs_unchanged'] = True
            report['emitted_input_sha256_after'] = {path:gate.digest(path) for path in input_hashes}
        except Exception as error:
            report.update(passed=False,closeout_error=str(error))
        gate.write_json(out/'component-report.json',report)
    if not report['passed']:
        raise RuntimeError('Component closeout failed')
    return report


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--kind',choices=('core','frontend'),required=True)
    p.add_argument('--addr-bits',type=int,choices=(1,2),default=1)
    p.add_argument('--emitted',type=Path,required=True)
    p.add_argument('--out',type=Path,required=True)
    p.add_argument('--circt',default=str(ROOT/'build/tools/firtool-1.159.0/bin/circt-opt'))
    p.add_argument('--yosys',default=str(ROOT/'build/tools/oss-cad-suite/bin/yosys'))
    p.add_argument('--solver',default=str(ROOT/'build/tools/oss-cad-suite/bin/z3'))
    a = p.parse_args()
    a.out.mkdir(parents=True,exist_ok=False)
    logs = a.out/'logs'
    logs.mkdir()
    run = Commands(ROOT,logs)
    prefix = Path(run(['lake','env','lean','--print-prefix'],'toolchain').strip())
    tools = dict(circt=a.circt,yosys=a.yosys,solver=a.solver,lake=str(prefix/'bin/lake'))
    report = dict(standalone_qualification=False,commands=run.records)
    try:
        report['component'] = component(a.kind,a.addr_bits,a.emitted,a.out/'component',tools,run)
        report['passed'] = True
    finally:
        load_gate().write_json(a.out/'report.json',report)


if __name__=='__main__':
    main()
