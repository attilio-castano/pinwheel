"""Native simulation models for explicitly interpreted pinned Liberty cells.

These are a separate two-state digital diagnostic, never an equivalence or
timing authority. Every mapped module and connected pin remains in the DUT.
"""
from copy import deepcopy

from streaming_mapped_liberty import FF, require


def verilog_boolean(node):
    kind=node[0]
    if kind=='constant': return "1'b1" if node[1] else "1'b0"
    if kind=='variable': return node[1]
    if kind=='not': return '(~'+verilog_boolean(node[1])+')'
    require(kind in ('*','+','^'),'Unsupported native Boolean cell function')
    return '('+verilog_boolean(node[1])+{'*':' & ','+':' | ','^':' ^ '}[kind]+verilog_boolean(node[2])+')'


def cell_models(library,used):
    require(library.pinned and used and set(used)<=library.cells.keys(),'Expected used pinned Liberty cells')
    lines=['`timescale 1ns/1ps','// Interpreted digital functions only; no delay/electrical model.']
    for name in sorted(used):
        model=library.cells[name]
        lines.append('module '+name+'('+','.join(model.directions)+');')
        for pin,direction in model.directions.items():
            lines.append(direction+(' reg ' if model.sequential and direction=='output' else ' wire ')+pin+';')
        if model.sequential:
            require(name==FF,'Unsupported native sequential leaf')
            lines.append('always @(posedge CLK or negedge RESET_B) if (!RESET_B) Q <= 1\'b0; else Q <= D;')
        else: lines.append('assign '+model.output+' = '+verilog_boolean(model.function)+';')
        lines.append('endmodule')
    return '\n'.join(lines)+'\n'


def sampler_mutation(data,top,library):
    """Change one actual FF D pin to the first-stage sampler's actual D root.

    Named register bits propose the target; actual FF Q and D pins determine
    the mutation. The resulting witness must be observed through public pins.
    """
    result=deepcopy(data)
    require(library.pinned and top in result.get('modules',{}),'Missing actual mapped core')
    module=result['modules'][top]
    def register(name):
        bits=module.get('netnames',{}).get(name,{}).get('bits')
        require(type(bits) is list and len(bits)==2 and all(type(bit) is int for bit in bits),'Missing complete sampler register')
        return bits
    first,second=register('r_stage1')[0],register('r_stage2')[0]
    def flop(q):
        matches=[(name,cell) for name,cell in module['cells'].items() if cell['type']==FF and cell['connections'].get('Q')==[q]]
        require(len(matches)==1,'Sampler register does not resolve to exactly one actual FF Q')
        name,cell=matches[0]
        require(cell.get('parameters')=={} and cell.get('port_directions')==library.cells[FF].directions and
            set(cell['connections'])==set(library.cells[FF].directions) and
            cell['connections']['RESET_B']==['1'] and cell['connections']['CLK']==module['ports']['clk']['bits'],
            'Changed sampler FF boundary')
        return name,cell
    first_name,source=flop(first);second_name,target=flop(second)
    before=deepcopy(target['connections']['D']);after=deepcopy(source['connections']['D'])
    require(before!=after and len(before)==len(after)==1,'Sampler mutation is vacuous')
    target['connections']['D']=after
    return result,dict(operation='Replace second sampler bit0 actual physical FF D pin with first sampler bit0 actual FF D root',
        module=top,changed_cell=second_name,source_cell=first_name,pin='D',before=before,after=after,changed_ff_pins=1,
        boundary='Actual one-bit mapped FF pin mutation; public native witness required, no assumed payload mismatch.')


def check_uart_cases(result):
    require(result.get('schema')=='pinwheel.streaming-mapped-uart-wire.v1' and result.get('passed') is True and not result.get('error') and
        type(result.get('depth')) is int and result['depth'] in (2,4),'Incomplete mapped UART diagnostic')
    expected=[]
    for q in (4,12,128):
        expected += [('valid',q,byte) for byte in (0,255,0x96,0x69)]
        expected += [('false-start',q,0x96),('bad-stop',q,0x69)]
        if q==4:expected += [('sampling-center',q,0),('sampling-off-center',q,0)]
        expected += [('held-high',q,0)]
    expected += [('sampler-ff-pin',4,0)]
    cases=result.get('cases')
    require(type(cases) is list and len(cases)==len(expected),'Mapped UART cases omitted or duplicated')
    for case,key in zip(cases,expected):
        require(case.get('passed') is True and (case.get('kind'),case.get('quarter_cycles'),case.get('payload'))==key and
            case.get('starts')==1 and case.get('tx_accepted')==0 and
            case.get('expected_terminal_delta')==(-1 if key[0]=='sampler-ff-pin' else 0),
            'Mapped UART case identity, exact owner/start or terminal evidence differs')
        if key[0]=='sampler-ff-pin':
            mutation=case.get('mutation',{})
            require(case.get('oracle_rejected') is True and mutation.get('changed_ff_pins')==1 and
                mutation.get('before')!=mutation.get('after') and mutation.get('pin')=='D' and
                case.get('observation',{}).get('terminal_delta')==-1,'Missing actual mapped FF pin witness')
    runs=result.get('native_runs')
    require(type(runs) is list and len(runs)==2 and [run.get('name') for run in runs]==['unchanged','sampler-ff-pin'],
        'Mapped native run inventory differs')
    for run in runs:
        trace=run.get('trace',{});edges=run.get('physical_edges')
        require(type(run.get('native_exit_code')) is int and run['native_exit_code']==0 and
            type(edges) is int and edges>0 and trace.get('edges')==edges and trace.get('bytes')==edges*20 and
            type(trace.get('sha256')) is str and len(trace['sha256'])==64,'Mapped native exit or complete trace evidence missing')
    require(result.get('physical_edges')==sum(run['physical_edges'] for run in runs),'Mapped native edge aggregate differs')


def run_uart_cases(vvp,executable,out,*,depth,mutant,mutation):
    """Twenty-three selected frame cases plus one actual FF-pin witness/depth.

    The prior qualified raw corpus exhausts all256 values at three rates. This
    separate mapped diagnostic deliberately reports its smaller finite scope.
    """
    from hashlib import sha256
    import json
    from pathlib import Path
    from streaming_ready_transport import ReadyHost
    from streaming_rtl import QuadRTL
    from streaming_transport import QuadTransport
    from streaming_uart_compile import uart_image
    from streaming_uart_wire_cases import Recording,receive_frame,opcode_counts
    require(type(depth) is int and depth in (2,4) and mutation.get('changed_ff_pins')==1 and
        mutation.get('pin')=='D' and mutation.get('before')!=mutation.get('after'),
        'Missing actual one-bit physical sampler mutation')
    out=Path(out);require(not out.exists(),'Mapped UART diagnostic requires fresh output')
    out.mkdir(parents=True)
    hashes={str(Path(path)):sha256(Path(path).read_bytes()).hexdigest() for path in (executable,mutant)}
    result=dict(schema='pinwheel.streaming-mapped-uart-wire.v1',passed=False,depth=depth,cases=[],native_runs=[],
        boundary='Finite selected mapped public-pin diagnostics; universal state transition requires separate kernel composition. '
            'Twelve valid frames, nine framing/park controls, two sampling-window diagnostics and one actual FF D-pin mutation. '
            'The mutation is distinguished by a one-edge-early terminal event, with no assumed payload change.')
    try:
        for label,image_path in [('unchanged',executable),('sampler-ff-pin',mutant)]:
            recording=Recording(out/(label+'.bin'));rtl=None
            try:
                with QuadRTL(vvp,image_path,record_sink=recording) as rtl:
                    transport=QuadTransport(rtl);host=ReadyHost(transport,depth=depth);host.initialize()
                    for q in ((4,12,128) if label=='unchanged' else (4,)):
                        loaded=host.load(uart_image(q))
                        profiles=([('valid',byte) for byte in (0,255,0x96,0x69)]+
                            [('false-start',0x96),('bad-stop',0x69)] if label=='unchanged' else [('sampling-center',0)])
                        if label=='unchanged' and q==4:profiles += [('sampling-center',0),('sampling-off-center',0)]
                        if label=='unchanged':profiles += [('held-high',0)]
                        for profile,payload in profiles:
                            case=receive_frame(rtl,transport,host,loaded,recording,q=q,profile=profile,payload=payload,
                                timing_delta=-1 if label!='unchanged' else 0)
                            if label!='unchanged':case.update(kind='sampler-ff-pin',mutation=mutation,oracle_rejected=True)
                            result['cases'].append(case)
                run=dict(name=label,argv=[str(vvp),str(image_path)],native_exit_code=rtl.process.returncode,
                    physical_edges=rtl.cycle,executable_sha256=hashes[str(Path(image_path))],
                    opcode_counts=opcode_counts(transport),trace=recording.trace.close())
                require(run['native_exit_code']==0,'Mapped native process did not exit successfully')
                result['native_runs'].append(run)
            finally:recording.trace.close()
        require(len(result['cases'])==24 and len(result['native_runs'])==2,'Mapped selected UART corpus incomplete')
        require(hashes=={str(Path(path)):sha256(Path(path).read_bytes()).hexdigest() for path in (executable,mutant)},
            'Mapped executable changed during native diagnostics')
        result.update(passed=True,physical_edges=sum(run['physical_edges'] for run in result['native_runs']))
        check_uart_cases(result)
    except BaseException as error:
        result.update(passed=False,error=type(error).__name__+': '+str(error));raise
    finally:(out/'report.json').write_text(json.dumps(result,indent=2)+'\n')
    return result
