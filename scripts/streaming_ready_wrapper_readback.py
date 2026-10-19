"""Restricted actual-SV wrapper interpretation for the streaming target.

The shared stateless parser rejects unsupported syntax. This adapter resolves
the complete actual driver graph, then prints typed descriptions whose every
port, instance, clock and expression must be checked by the Lean kernel.
"""
import artifact_wrapper_readback as syntax
import streaming_ready_readback as interface
from pathlib import Path


def read_bundle(package_path,tiny_path,addr_bits):
    core,front = interface.backend('core',addr_bits),interface.backend('frontend',addr_bits)
    package,tiny = map(syntax.read_module,(package_path,tiny_path))
    syntax.require(len(package.instances)==2,'Streaming package must have exactly two instances')
    syntax.require(set(package.assignments)=={'busy','levels','enabled'},'Unexpected package logic')
    f,c = syntax.instance(package,'frontend'),syntax.instance(package,'core')
    fp = syntax.connections(package,f,{'clk':1,**{n:w for n,(w,_) in front.INPUTS.items()},
        **{n:w for n,(w,_) in front.OUTPUTS.items()}})
    cp = syntax.connections(package,c,{'clk':1,**{n:w for n,(w,_) in core.INPUTS.items()},
        **{n:w for n,(w,_) in core.OUTPUTS.items()}})
    drivers = {'clk':('clock','clk')}
    for name,_,ctor in interface.FRONTEND_INPUTS:
        syntax.claim(drivers,name,('physical',ctor))
    for name,(_,ctor) in front.OUTPUTS.items():
        syntax.claim(drivers,syntax.wire(fp[name]),('frontend',ctor))
    for name,(_,ctor) in core.OUTPUTS.items():
        syntax.claim(drivers,syntax.wire(cp[name]),('status',ctor[1:]))
    syntax.require(set(package.widths)==set(drivers)|set(package.assignments),
        'Unaccounted, undriven or extra streaming package signal')
    frontend,controller,outputs = {},{},{}
    for name in front.INPUTS:
        value = syntax.resolve(package,drivers,fp[name])
        syntax.require(value[0] in ('physical','status'),'Unsupported frontend source')
        frontend[name] = value
    for name in core.INPUTS:
        value = syntax.resolve(package,drivers,cp[name])
        syntax.require(value[0]=='frontend','Unsupported streaming core source')
        controller[name] = value[1]
    for name in ('miso','ready','busy','levels','enabled'):
        value = syntax.resolve(package,drivers,('wire',name))
        syntax.require(value[0] in ('frontend','status'),'Unsupported public streaming output')
        outputs[name] = value
    clocks = [syntax.wire(ports['clk']) for ports in (fp,cp)]
    syntax.require(all(name in drivers and package.widths[name] == 1 for name in clocks),
        'Undriven or incorrectly sized streaming clock')
    syntax.require(len(tiny.instances)==1,'Tiny wrapper must have exactly one engine')
    engine = syntax.instance(tiny,'engine')
    tp = syntax.connections(tiny,engine,{'clk':1,'initialize':1,'csn':1,'sck':1,'mosi':4,
        'raw_inputs':2,'miso':4,'ready':1,'busy':1,'levels':3,'enabled':3})
    syntax.require(set(tiny.assignments)=={'active','uo_out','uio_out','uio_oe','_unused'},
        'Unexpected Tiny wrapper logic')
    sources = dict(ui_in='.ui',uio_in='.uio',ena='.ena',rst_n='.rstN')
    for name in ('miso','ready','busy','levels','enabled'):
        wire = syntax.wire(tp[name])
        syntax.require(wire not in sources and wire not in tiny.assignments,'Multiple Tiny output driver')
        sources[wire] = '(.engine .'+name+')'
    syntax.require(set(tiny.widths)==set(sources)|set(tiny.assignments)|{'clk'},
        'Unaccounted or undriven Tiny signal')
    return dict(package=package,tiny=tiny,core=core,front=front,frontend=frontend,
        controller=controller,outputs=outputs,clocks=clocks,tiny_engine=engine,
        tiny_connections=tp,tiny_sources=sources,addr_bits=addr_bits)


def selection(value):
    kind,tag = value
    if kind=='physical': return '.physical .'+tag
    if kind=='status': return '.status .'+tag
    if kind=='frontend': return '.frontend ('+tag+')'
    raise ValueError('Unsupported streaming source kind')


def lean_source(bundle):
    a = bundle['addr_bits']
    namespace = 'Pinwheel.Artifact.StreamingReadyWrappersD'+str(2**a)
    p,t = bundle['package'],bundle['tiny']
    lines = ['import Pinwheel.Hardware.StreamingReady.TinyWiring',
        'namespace '+namespace,'open Pinwheel.Hardware Pinwheel.Hardware.StreamingReady',
        'open Wiring',
        'def sourceHashes : List (String × String) := '+syntax.lean_list(
            '⟨'+syntax.quoted(m.source)+','+syntax.quoted(m.sha256)+'⟩' for m in (p,t)),
        'def actualFrontend : {w : Nat} → Pinwheel.Hardware.Streaming.Frontend.Input w → FrontSource w']
    for name,(_,ctor) in bundle['front'].INPUTS.items():
        lines.append('  | _, '+ctor+' => '+selection(bundle['frontend'][name]))
    lines += ['def actualCore : {w : Nat} → Pinwheel.Hardware.StreamingReady.Core.Input w → Pinwheel.Hardware.Streaming.Frontend.Output w']
    for name,(_,ctor) in bundle['core'].INPUTS.items():
        lines.append('  | _, '+ctor+' => '+bundle['controller'][name])
    lines += ['def actualOutput : {w : Nat} → Package.Output w → PublicSource w']
    for name in ('miso','ready','busy','levels','enabled'):
        lines.append('  | _, .'+name+' => '+selection(bundle['outputs'][name]))
    instances = syntax.lean_list('⟨'+syntax.quoted(i['name'])+','+syntax.quoted(i['kind'])+'⟩' for i in p.instances)
    lines += ['def actualPackage : Wiring.Description :=',
        '  ⟨'+','.join([syntax.quoted(p.name),syntax.port_list(p),instances,
            syntax.quoted(bundle['clocks'][0]),syntax.quoted(bundle['clocks'][1]),
            'actualFrontend','actualCore','actualOutput'])+'⟩',
        'theorem package_correct : Wiring.Certificate '+str(a)+' actualPackage where',
        '  name := rfl','  interface := rfl','  instances := rfl',
        '  frontendClock := rfl','  coreClock := rfl',
        '  frontend := by\n    intro w port\n    cases port <;> try rfl\n    case status o => cases o <;> rfl',
        '  core := by intro w port; cases port <;> rfl',
        '  outputs := by intro w port; cases port <;> rfl',
        'open TinyWiring',
        'def actualEngine : {w : Nat} → Wiring.Physical w → TinyWiring.E w']
    for name,_,ctor in interface.FRONTEND_INPUTS:
        lines.append('  | _, .'+ctor+' => '+syntax.expand_expression(t,bundle['tiny_connections'][name],bundle['tiny_sources']))
    lines += ['def actualPads : TinyWiring.Pad → TinyWiring.E 8']
    for name,tag in [('uo_out','uo'),('uio_out','uio'),('uio_oe','oe')]:
        lines.append('  | .'+tag+' => '+syntax.expand_expression(t,t.assignments[name],bundle['tiny_sources']))
    engine = bundle['tiny_engine']
    lines += ['def actualTiny : TinyWiring.Description :=',
        '  ⟨'+','.join([syntax.quoted(t.name),syntax.port_list(t),syntax.quoted(engine['name']),
            syntax.quoted(engine['kind']),syntax.quoted(syntax.wire(bundle['tiny_connections']['clk'])),
            'actualEngine','actualPads',syntax.expand_expression(t,t.assignments['_unused'],bundle['tiny_sources'])])+'⟩',
        'theorem tiny_correct : TinyWiring.Certificate '+str(a)+' actualTiny where',
        '  name := rfl','  interface := rfl','  engineName := rfl','  engineKind := rfl',
        '  engineClock := rfl','  engine := by intro w port; cases port <;> rfl',
        '  outputs := by intro port; cases port <;> rfl','  unused := rfl',
        'end '+namespace]
    return ('\n'.join(lines)+'\n').replace('(.input (.engine ',
        '(.input (TinyWiring.Input.engine ')


def mutation_specs():
    return [('unchanged',None,None,None),
        ('package-wire','package','.status_generation(status_generation)',
            '.status_generation(status_transfer)'),
        ('package-clock','package','.clk(clk)', '.clk(sck)'),
        ('tiny-output','tiny',"assign uio_oe = active ? {5'b0, enabled}",
            "assign uio_oe = active ? {5'b0, levels}")]


def certify(addr_bits, package, tiny, out, tools, run, *, gate=None):
    if gate is None:
        from streaming_ready_artifacts import load_gate
        gate = load_gate()
    out = Path(out)
    out.mkdir(parents=True,exist_ok=False)
    inputs = {'package':Path(package),'tiny':Path(tiny)}
    before = {name:gate.digest(path) for name,path in inputs.items()}
    report = dict(passed=False,addr_bits=addr_bits,input_sha256_before=before,mutations=[])
    module = 'StreamingReadyWrappersD'+str(2**addr_bits)
    try:
        for label,selected,old,new in mutation_specs():
            directory = out/label
            directory.mkdir()
            copies = {}
            for name,path in inputs.items():
                text = path.read_text()
                if selected == name:
                    if text.count(old) < 1:
                        raise ValueError('Missing exact wrapper mutation target: '+label)
                    text = text.replace(old,new,1)
                copies[name] = directory/(name+'.sv')
                copies[name].write_text(text)
            gate.freeze_inputs(report,out,copies.values())
            bundle = read_bundle(copies['package'],copies['tiny'],addr_bits)
            source = directory/(module+'.lean')
            source.write_text(lean_source(bundle))
            gate.freeze_inputs(report,out,[source])
            def scoped(command,name,**options):
                return run(command,'wrapper-'+label+'-'+name,**options)
            gate.compile_lean(scoped,tools,directory,module,
                reject=None if selected is None else
                    'error: Type mismatch' if label=='package-clock' else 'error: Tactic `rfl` failed')
            report['mutations'].append(dict(name=label,passed=True,expected_rejection=selected is not None,
                proof_directory=str(directory),module=module))
        if before != {name:gate.digest(path) for name,path in inputs.items()}:
            raise RuntimeError('Wrapper source changed during certification')
        gate.assert_hashes(out,report['proof_input_sha256_before'])
        report.update(passed=True,inputs_unchanged=True,
            module=module,proof_directory=str(out/'unchanged'))
    except BaseException as error:
        report['error'] = type(error).__name__+': '+str(error)
        raise
    finally:
        gate.write_json(out/'wrapper-report.json',report)
    return report
