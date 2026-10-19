"""Actual mapped package/pad joins, complete costs and native pin diagnostics.

This hook consumes fresh component contexts. It returns ordinary Lean proof
sources; the campaign must compile/audit every source and exact API target
before it can accept the complete-device result.
"""
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path

from streaming_mapped_liberty import require
from streaming_mapped_flow import quoted
from streaming_mapped_wrapper import (prepare_wrapper,prepare_package,complete_hierarchy,
    wrapper_source,package_source,cut_engine)
from streaming_mapped_netlist import load_mapped,parse_mapped
from streaming_mapped_cost import measure
from streaming_mapped_simulation import cell_models,sampler_mutation,run_uart_cases
from streaming_mapped_composition import generate
from streaming_mapped_uart_timing import generate as generate_timing,required_qnames as timing_qnames

JOIN_THEOREMS=('components_correct','physical_step_correct','physical_observe_correct','physical_run_correct',
    'source_runtime_step_correct','source_runtime_run_correct','source_runtime_observe_correct',
    'initialized_upload_correct','initialized_runtime_correct','physical_warm_reset_correct',
    'concrete_i2c_initialized','concrete_i2c_runtime','concrete_i2c_custody','concrete_i2c_progress',
    'concrete_uart_initialized','concrete_uart_runtime','concrete_uart_custody','uart_frame_correct',
    'uart_false_start_correct','uart_bad_stop_correct','uart_host_quiet_correct','uart_arming_correct')


def digest(path):return sha256(Path(path).read_bytes()).hexdigest()


def read(path):
    from streaming_mapped_campaign import read_json
    return read_json(path)


class NativeAudit:
    """Retain intents before Popen and actual closed native results afterward.

    Only the three selected module-local client aliases are scoped; the old
    source files and their native process/pipe behavior are preserved.
    """
    def __init__(self,path,vvp,executables):
        self.path=Path(path);self.vvp=str(vvp);self.executables={str(path):digest(path) for path in executables}
        self.records=[];self.scope=None;self.saved=[]
        require(not self.path.exists(),'Preserve earlier native journal')
    def event(self,record):
        import os
        with self.path.open('a') as stream:
            stream.write(json.dumps(record,sort_keys=True)+'\n');stream.flush();os.fsync(stream.fileno())
    def __enter__(self):
        import streaming_rtl,streaming_ready_wire_cases,streaming_wire_cases
        audit=self;original=streaming_rtl.QuadRTL
        class Recorded(original):
            def __init__(self,vvp,executable,**options):
                argv=[str(vvp),str(executable)]
                require(str(vvp)==audit.vvp and str(executable) in audit.executables and
                    digest(executable)==audit.executables[str(executable)] and audit.scope in ('uart','i2c','legacy'),
                    'Unexpected native executable, scope or changed input')
                self.mapped_intent=dict(index=len(audit.records),scope=audit.scope,argv=argv,
                    executable_sha256_before=digest(executable))
                audit.event(dict(event='intent',**self.mapped_intent))
                super().__init__(vvp,executable,**options)
            def __exit__(self,kind,error,traceback):
                try:return super().__exit__(kind,error,traceback)
                finally:
                    record=dict(self.mapped_intent,actual_argv=list(self.process.args),
                        native_exit_code=self.process.returncode,physical_edges=self.cycle,
                        executable_sha256_after=digest(self.process.args[1]),client_succeeded=error is None)
                    audit.records.append(record);audit.event(dict(event='result',**record))
        for module in (streaming_rtl,streaming_ready_wire_cases,streaming_wire_cases):
            self.saved.append((module,module.QuadRTL));module.QuadRTL=Recorded
        return self
    def __exit__(self,kind,error,traceback):
        for module,original in self.saved:module.QuadRTL=original
        if error is None:
            require(len(self.records)==14 and [row['scope'] for row in self.records]==
                ['uart']*2+['legacy']*2+['i2c']*10,'Complete14 native processes/depth not recorded')
            for row in self.records:
                require(row['argv']==row['actual_argv'] and type(row['native_exit_code']) is int and
                    row['native_exit_code']==0 and row['client_succeeded'] is True and
                    row['executable_sha256_before']==row['executable_sha256_after'] and
                    type(row['physical_edges']) is int and row['physical_edges']>0,
                    'Missing actual successful closed native process evidence')


def wrapper_hook(worker,contexts):
    import streaming_ready_wire_cases as i2c
    import streaming_uart_legacy_cases as legacy
    w=worker
    require({context['label'] for context in contexts}=={'frontend','core-d2','core-d4'},'Missing complete fresh component contexts')
    by={context['label']:context for context in contexts}
    target=w.out/'device';target.mkdir()
    modules={};depths={};paths=tuple(context['proof'] for context in contexts)
    library=w.library
    def freeze_tree(directory):w.frozen.add(*(path for path in Path(directory).rglob('*') if path.is_file()))
    def native(argv,log):
        freeze_tree(log.parent)
        output=w.run(argv,'device-'+str(log.relative_to(target)).replace('/','--'),timeout=w.config.get('timeout',900))
        w.write(log,output)
        freeze_tree(log.parent)
        return output
    device=w.config.get('device',{})
    require(set(device)=={'2','4'},'Both actual external wrapper source sets required')
    for a in (1,2):
        depth=2**a;key=str(depth);cfg=device[key]
        require(set(cfg)=={'tiny','package','bridge'} and all(Path(path).is_absolute() for path in cfg.values()),
            'Expected three exact actual wrapper/bridge paths')
        w.frozen.add(*cfg.values())
        out=target/('d'+key);out.mkdir()
        outer=prepare_wrapper(out/'outer',addr_bits=a,tiny=cfg['tiny'],package=cfg['package'],
            liberty=w.config['library'],yosys=w.tools['yosys'],abc=w.tools['abc'],run=native)
        package=prepare_package(out/'package',addr_bits=a,package=cfg['package'],
            frontend=w.config['components']['frontend']['sv'],core=w.config['components']['core-d'+key]['sv'],
            yosys=w.tools['yosys'],run=native)
        freeze_tree(out)
        for report in (outer,package):
            modules[report['proof_module']]=Path(report['proof_source']).read_text()
        complete=complete_hierarchy(read(outer['restored_json']),read(package['package_json']),
            read(by['core-d'+key]['mapped']),read(by['frontend']['mapped']),addr_bits=a,library=library)
        full=w.write(out/'complete.json',json.dumps(complete,indent=2)+'\n')
        bits=6039 if depth==2 else 6195
        # Expanding this exact assembled hierarchy is mandatory. It refuses
        # shorts/aliases, missing branches, undriven pins and clock-as-data.
        graph=load_mapped(full,outer['top'],library)
        cost=measure(full,outer['top'],w.config['library'],bits,complete=True)
        w.write(out/'cost.json',json.dumps(cost,indent=2)+'\n')
        native_sources={}
        for label,data in [('complete',complete),('sampler-ff-pin',sampler_mutation(complete,
                'pinwheel_streaming_ready_core_d'+key,library)[0])]:
            if label!='complete':
                mapped=w.write(out/(label+'.json'),json.dumps(data,indent=2)+'\n')
                load_mapped(mapped,outer['top'],library)
            else:mapped=full
            source=out/(label+'.sv')
            script=w.write(out/(label+'-emit.ys'),'\n'.join(('read_json '+quoted(mapped),
                'read_liberty -lib '+quoted(w.config['library']),'hierarchy -check -top '+outer['top'],
                'check -assert','write_verilog -noattr -noexpr '+quoted(source)))+'\n')
            native([w.tools['yosys'],'-Q','-s',str(script)],out/(label+'-emit.log'))
            w.frozen.add(source);native_sources[label]=source
        models=w.write(out/'cells.sv',cell_models(library,set(graph.cell_counts)))
        executables={}
        for label,source in native_sources.items():
            executable=out/(label+'.vvp')
            native([w.tools['iverilog'],'-g2012','-s','streaming_quad_host_bridge','-o',str(executable),
                str(source),str(models),cfg['bridge']],out/(label+'-compile.log'))
            w.frozen.add(executable);executables[label]=executable
        _,mutation=sampler_mutation(complete,'pinwheel_streaming_ready_core_d'+key,library)
        w.write(out/'sampler-mutation.json',json.dumps(mutation,indent=2)+'\n')
        # Independent actual-function controls. A wrong mapped pad reaches a
        # false scalar theorem; a same-width status wire reaches a wrong typed
        # wiring equation; a clock change is a separate strict-reader refusal.
        controls=out/'controls';controls.mkdir()
        changed=read(outer['mapped_json']);changed['modules'][outer['top']]['ports']['uo_out']['bits'][0]='0'
        wrong=w.write(controls/'changed-pad.json',json.dumps(changed,indent=2)+'\n')
        text=wrapper_source(parse_mapped(changed,outer['top'],library,combinational=True),a,
            namespace='Pinwheel.Artifact.StreamingMappedChangedPadD'+key,netlist_sha256=digest(wrong))
        w.compile(controls,'MappedChangedPadD'+key,text,paths=paths,reject='Tactic `decide` proved that the proposition',fixture=True)
        changed=read(package['package_json']);main=changed['modules'][package['top']]
        main['cells']['frontend']['connections']['status_generation']=deepcopy(main['cells']['frontend']['connections']['status_transfer'])
        wrong=w.write(controls/'status-wire.json',json.dumps(changed,indent=2)+'\n')
        text=package_source(changed,package['top'],a,namespace='Pinwheel.Artifact.StreamingMappedStatusWireD'+key,netlist_sha256=digest(wrong))
        w.compile(controls,'MappedStatusWireD'+key,text,paths=paths,reject='Tactic `rfl` failed',fixture=True)
        original=read(out/'outer/actual-outer.json')
        changed={'modules':{outer['top']:deepcopy(original['modules'][outer['top']])}}
        changed['modules'][outer['top']]['cells']['engine']['connections']['clk']=changed['modules'][outer['top']]['ports']['ena']['bits']
        w.write(controls/'changed-clock.json',json.dumps(changed,indent=2)+'\n')
        try:cut_engine(changed,outer['top'],outer['package'])
        except ValueError as error:require('clock is not direct' in str(error),'Wrong clock control failure')
        else:raise RuntimeError('Changed actual engine clock was accepted')
        control_records=[dict(name=name,passed=True,expected_rejection=True,
            boundary='strict actual clock interpretation' if name=='changed-clock' else 'native kernel proof rejection')
            for name in ('changed-pad','status-wire','changed-clock')]
        intent=dict(schema='pinwheel.streaming-mapped-native-intent.v1',depth=depth,
            executable_sha256={name:digest(path) for name,path in executables.items()},
            model_sha256=digest(models),source_sha256={name:digest(path) for name,path in native_sources.items()},
            vvp=str(w.tools['vvp']),scopes=['UART24','I2C10','SPI32768','JTAG4097'])
        w.write(out/'native-intent.json',json.dumps(intent,indent=2)+'\n')
        with NativeAudit(out/'native.jsonl',w.tools['vvp'],executables.values()) as audit:
            audit.scope='uart'
            uart=run_uart_cases(w.tools['vvp'],executables['complete'],out/'uart',depth=depth,
                mutant=executables['sampler-ff-pin'],mutation=mutation)
            audit.scope='legacy'
            legacy_result=legacy.run_legacy_cases(w.tools['vvp'],executables['complete'],out/'legacy',depth=depth)
            w.write(out/'legacy/report.json',json.dumps(legacy_result,indent=2)+'\n')
            audit.scope='i2c'
            i2c_result=i2c.run_i2c_cases(w.tools['vvp'],executables['complete'],out/'i2c',depth=depth)
        require(intent['executable_sha256']=={name:digest(path) for name,path in executables.items()},
            'Mapped native executable changed during pin diagnostics')
        from streaming_mapped_simulation import check_uart_cases
        check_uart_cases(uart);legacy.check_legacy_cases(legacy_result);i2c.check_i2c_cases(i2c_result)
        freeze_tree(out)
        depths[key]=dict(cost=cost,uart=uart,i2c=i2c_result,legacy=legacy_result,controls=control_records,
            native_intent=intent,native_runs=audit.records,native_journal=str(audit.path),
            native_journal_sha256=digest(audit.path),outer=outer,package=package,complete_json=str(full),
            complete_sha256=digest(full),physical_edges=uart['physical_edges']+i2c_result['physical_edges']+legacy_result['physical_edges'])
        modules.update(generate(a))
        modules.update(generate_timing(a))
    qnames=['Pinwheel.Artifact.StreamingMappedSessionD'+str(depth)+'.'+name
        for depth in (2,4) for name in JOIN_THEOREMS]
    extra_qnames=timing_qnames()
    required='\n'.join(['import StreamingMappedSessionD2','import StreamingMappedSessionD4',
        'import StreamingMappedUARTTimingD2','import StreamingMappedUARTTimingD4']+
        ['#check '+name for name in qnames+extra_qnames])+'\n'
    return dict(modules=modules,required={'StreamingMappedRequiredTargets':required},metadata=dict(
        complete_device_checked=True,full_state_bits={'2':6039,'4':6195},depths=depths,required_qnames=qnames,
        extra_qnames=extra_qnames,
        all_native_cases_checked=True,all_device_mutations_checked=True,all_complete_costs_checked=True,
        physical_edges=sum(row['physical_edges'] for row in depths.values()),
        boundary='Actual interpreted mapped component+package+pad functions, all declared FFs. '
            'Proof sources returned here still require native compilation, all44qualified API checks, six additional first-BUSY timing checks and a complete private-declaration audit. '
            'Native diagnostics and complete cell cost remain separate from universal kernel equivalence and physical timing.'))
