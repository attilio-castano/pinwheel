"""Generate explicit all-state joins for constant-specialized mapped words.

This development adapter preserves the historical component interpreter and
its topology checks. It adds only explicit proof arguments for static input
literals, which Lean must check at every physical word instance.
"""
from hashlib import sha256
import json
import os
from pathlib import Path
import subprocess
import time

from streaming_mapped_arithmetic import generate_arithmetic
from streaming_mapped_campaign import audit_source, required_source
from streaming_mapped_certificate import bitwise_source, generate_full_adder
from streaming_mapped_component import generate_component
from streaming_mapped_hierarchy import ARITHMETIC
from streaming_mapped_liberty import load_library, require
from streaming_mapped_netlist import load_mapped
from streaming_mapped_reductions import REDUCTIONS, generate_reduction
from streaming_tt_opt_certificate import generate_specialized, add_static_premises
import streaming_ready_readback


def generate_words(mapped, descriptor, library, *, prefix, namespace):
    data = json.loads(Path(mapped).read_bytes())
    top = descriptor['top']
    used = sorted({cell['type'] for cell in data['modules'][top]['cells'].values()
        if cell['type'] in descriptor['words']})
    texts = {}
    fa_module, fa_namespace = prefix+'FA', namespace+'.FA'
    texts[fa_module] = generate_full_adder(mapped, library, namespace=fa_namespace)
    specs = {}
    for index, module in enumerate(used):
        desc = descriptor['words'][module]
        name, ns = prefix+'Word'+str(index), namespace+'.Word'+str(index)
        kind = desc['kind']
        if 'fixed_operands' in desc:
            source = generate_specialized(mapped, library, module, desc, namespace=ns)
        elif kind in ARITHMETIC:
            source, _ = generate_arithmetic(mapped, library, module, kind, namespace=ns,
                fa_module=fa_module, fa_namespace=fa_namespace)
        elif kind in REDUCTIONS:
            source, _ = generate_reduction(mapped, library, module, kind, namespace=ns)
        else:
            source = bitwise_source(load_mapped(mapped, module, library, combinational=True), kind,
                namespace=ns, netlist_sha256=sha256(Path(mapped).read_bytes()).hexdigest())
        texts[name] = source
        specs[module] = dict(module=name, namespace=ns,
            module_sha256=sha256(json.dumps(data['modules'][module],sort_keys=True,separators=(',',':')).encode()).hexdigest(),
            netlist_sha256=sha256(Path(mapped).read_bytes()).hexdigest(),
            fixed_operands=desc.get('fixed_operands', {}))
    return texts, specs


def generate_joins(rb, raw, mapped, library, specs, *, namespace, raw_module, raw_namespace, prefix):
    texts, metadata = generate_component(rb, Path(raw), Path(mapped), library, specs,
        namespace=namespace, raw_module=raw_module, raw_namespace=raw_namespace, module_prefix=prefix)
    return add_static_premises(texts, specs), metadata


def certify(label, candidate, config, out, *, lean=None, timeout=600, native_executor=None):
    """Compile fresh interpreted leaves and complete FF/output kernel links.

    The report is a development proof result, not a committed-source gate or
    upstream emitter certificate. The caller must provide that final binding.
    """
    candidate, out = Path(candidate).resolve(), Path(out).resolve()
    require(not out.exists() and label in ('frontend','core-d2') and type(timeout) is int and
        1 <= timeout <= 900, 'Fresh explicit bounded proof target required')
    out.mkdir(parents=True)
    library_path = Path(config['library']).resolve()
    library = load_library(library_path)
    descriptor = json.loads((candidate/'words.json').read_bytes())
    suffix = 'Frontend' if label == 'frontend' else 'CoreD2'
    prefix, namespace = 'Optimized'+suffix, 'Pinwheel.Artifact.StreamingOptimized'+suffix
    lean = lean or config['tools']['lean']
    cfg = config['components'][label]
    rb = streaming_ready_readback.backend('frontend' if label == 'frontend' else 'core', 1)
    inputs = {str(Path(path).resolve()): sha256(Path(path).read_bytes()).hexdigest() for path in
        [candidate/'mapped.json', candidate/'words.json', library_path, cfg['raw_json'], *cfg['raw_sources'].values()]}
    texts, specs = generate_words(candidate/'mapped.json', descriptor, library, prefix=prefix, namespace=namespace)
    texts.update({name: Path(path).read_text() for name,path in cfg['raw_sources'].items()})
    joins, metadata = generate_joins(rb, cfg['raw_json'], candidate/'mapped.json', library, specs,
        namespace=namespace, raw_module=cfg['raw_module'], raw_namespace=cfg['raw_namespace'], prefix=prefix)
    texts.update(joins)
    texts[prefix+'Required'] = required_source(rb, next(reversed(joins)), namespace)
    texts[prefix+'Audit'] = audit_source(list(texts))
    env = dict(os.environ, LEAN_PATH=str(out)+':'+str(Path('.lake/build/lib/lean').resolve()))
    results=[];start=time.monotonic()
    report=dict(schema='pinwheel.streaming-tt-optimization-proof.v1',passed=False,qualified=False,
        namespace=namespace, component_metadata=metadata, input_sha256=inputs, modules=[], word_modules=specs)
    for name, source in texts.items():
        path=out/(name+'.lean');path.write_text(source)
        argv=[lean,'--root='+str(out),'-DwarningAsError=true','-o',str(out/(name+'.olean')),str(path)]
        try:
            if native_executor is None:
                run=subprocess.run(argv,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=timeout)
            else:
                run=native_executor.run(['env','LEAN_PATH='+str(out),*argv],out/(name+'.log'),timeout=timeout)
                argv=run.native_argv
        except subprocess.TimeoutExpired as error:
            output=error.stdout or b''
            if type(output) is bytes:output=output.decode(errors='replace')
            (out/(name+'.log')).write_text(output+'\nNative Lean timed out.\n')
            report.update(error='Native Lean timeout',timed_out_module=name,
                elapsed_seconds=time.monotonic()-start)
            (out/'report.json').write_text(json.dumps(report,sort_keys=True,indent=2)+'\n')
            raise
        (out/(name+'.log')).write_text(run.stdout)
        entry=dict(module=name,argv=argv,exit_code=run.returncode,
            source_sha256=sha256(path.read_bytes()).hexdigest(),log_sha256=sha256(run.stdout.encode()).hexdigest())
        if native_executor is not None:entry['native_journal_index']=run.native_journal_index
        results.append(entry)
        report.update(modules=results,elapsed_seconds=time.monotonic()-start)
        (out/'report.json').write_text(json.dumps(report,sort_keys=True,indent=2)+'\n')
        require(run.returncode==0,'Kernel check failed for '+name+': '+run.stdout[:3000])
        if len(results)%20==0: print(label,len(results),'modules checked',round(time.monotonic()-start,2),flush=True)
    require(inputs == {path:sha256(Path(path).read_bytes()).hexdigest() for path in inputs},'Proof inputs changed')
    report.update(passed=True, all_state_kernel_join=True, strict_private_axiom_audit=True,inputs_unchanged=True)
    (out/'report.json').write_text(json.dumps(report,sort_keys=True,indent=2)+'\n')
    return report
