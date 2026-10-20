"""Keep the complete actual CTS/reset cone in a kernel-checked scalar graph."""
from streaming_mapped_liberty import require
from streaming_mapped_certificate import substitute
from streaming_tt_certificate import clock_cones,canonical_model
from streaming_tt_graph import network_sources,contraction_sources,lookup_source,atom_source,header
from streaming_tt_finite import finite_forall


def model(graph,*,state_order):
    roots=clock_cones(graph)
    require(type(state_order) is tuple and len(state_order)==len(set(state_order)) and set(state_order)==set(roots),
        'Actual clock/reset roots must cover every physical FF once')
    by_output={gate.output:gate for gate in graph.gates};indices={graph.clock:0};nodes=[];active=set()
    def visit(wire):
        if type(wire) is str:
            require(wire in ('0','1'),'Functional X/Z in actual clock cone');return ('constant',wire=='1')
        if wire in indices:return ('wire',indices[wire],False)
        require(wire in by_output and wire not in active,'Data-driven or cyclic actual clock/reset cone')
        active.add(wire);gate=by_output[wire];cell=graph.library.cells[gate.cell]
        pins=sorted(pin for pin,direction in cell.directions.items() if direction=='input');sources=[];mapping={}
        for pin in pins:
            root=visit(gate.connections[pin])
            if root[0]=='constant':mapping[pin]=root
            else:
                require(not root[2],'Actual clock wire acquired an implicit inversion')
                if root[1] not in sources:sources.append(root[1])
                mapping[pin]=('variable','p'+str(sources.index(root[1])))
        active.remove(wire);index=1+len(nodes);indices[wire]=index
        nodes.append(dict(name=gate.name,cell=gate.cell,sources=tuple(sources),expression=substitute(cell.function,mapping)))
        return ('wire',index,False)
    ff={item.name:item for item in graph.flipflops};clocks=tuple(visit(ff[name].clock) for name in state_order);resets=tuple(visit(ff[name].reset_b) for name in state_order)
    # CTS may deliberately leave load branches whose outputs feed no FF. They
    # are still actual clock cells and must retain their interpreted equations.
    dependent={graph.clock};clock_cells=[]
    for gate in graph.gates:
        cell=graph.library.cells[gate.cell]
        if any(wire in dependent for pin,wire in gate.connections.items() if cell.directions[pin]=='input'):
            dependent.add(gate.output);clock_cells.append(gate.name);visit(gate.output)
    return dict(labels=(('input','clk',0),),nodes=tuple(nodes),next={},outputs={'clock':clocks,'reset':resets}),dict(ff_order=state_order,
        clock_roots=clocks,reset_roots=resets,actual_clock_cells=tuple(clock_cells),actual_cone_cells=tuple(node['name'] for node in nodes))


def generate(graph,*,state_order,prefix,namespace,clock_certificate):
    actual,metadata=model(graph,state_order=state_order);modules,network=network_sources(actual,prefix=prefix,namespace=namespace)
    canonical=canonical_model(actual)
    require(not canonical['nodes'] and all(atom==('wire',0,False) for atom in canonical['outputs']['clock'])
        and all(atom==('constant',True) for atom in canonical['outputs']['reset']),
        'Actual CTS/reset cone is not a positive clock and inactive reset')
    new,reference=network_sources(canonical,prefix=prefix+'Reference',namespace=namespace+'.Reference');modules.update(new)
    new,transport=contraction_sources(actual,canonical,reference,network,prefix=prefix+'Transport',namespace=namespace+'.Transport')
    modules.update(new)
    count=len(state_order);name=prefix+'Proof'
    lines=[header([network['module'],transport['module'],clock_certificate['module'],'Pinwheel.Hardware.StreamingPhysical.Clock'],namespace),
        lookup_source('clockRootTable',[atom_source(atom) for atom in actual['outputs']['clock']],result_type='Atom',default='.constant false'),
        lookup_source('resetRootTable',[atom_source(atom) for atom in actual['outputs']['reset']],result_type='Atom',default='.constant false'),
        f'def clockRoot (index : Fin {count}) : Atom := clockRootTable index.val',f'def resetRoot (index : Fin {count}) : Atom := resetRootTable index.val',
        finite_forall('clockBound',count,lambda index:f'(clockRoot {index}).Bounded (network.inputs + network.nodes)'),
        finite_forall('resetBound',count,lambda index:f'(resetRoot {index}).Bounded (network.inputs + network.nodes)'),
        finite_forall('clock_image',count,lambda index:f'(clockRoot {index}).rename {transport["namespace"]}.image = .wire 0 false'),
        finite_forall('reset_image',count,lambda index:f'(resetRoot {index}).rename {transport["namespace"]}.image = .constant true'),
        f'theorem transport_image : {transport["namespace"]}.contraction.image = {transport["namespace"]}.image := rfl',
        f'theorem actual_positive (index : Fin {count}) (raw : Bool) : (clockRoot index).eval (network.value (fun _ => raw)) = raw := by',
        f'  rw [{transport["namespace"]}.contraction.atom _ _ (clockBound index), transport_image, clock_image index]',
        f'  exact Network.value_input {reference["namespace"]}.network (fun _ => raw) 0 (by decide)',
        f'theorem actual_inactive (index : Fin {count}) (raw : Bool) : (resetRoot index).eval (network.value (fun _ => raw)) = true := by',
        f'  rw [{transport["namespace"]}.contraction.atom _ _ (resetBound index), transport_image, reset_image index]',
        '  rfl',
        f'theorem clock_link (index : Fin {count}) (raw : Bool) :',
        f'    (clockRoot index).eval (network.value (fun _ => raw)) = ClockLevel ({clock_certificate["namespace"]}.clocking.clock index) raw :=',
        f'  (actual_positive index raw).trans (({clock_certificate["namespace"]}.clocking.positive index).level raw).symm',
        f'theorem reset_link (index : Fin {count}) (raw : Bool) :',
        f'    (resetRoot index).eval (network.value (fun _ => raw)) = ClockLevel ({clock_certificate["namespace"]}.clocking.reset index) raw :=',
        f'  (actual_inactive index raw).trans (({clock_certificate["namespace"]}.clocking.inactive index).level raw).symm',
        'end '+namespace,'']
    modules[name]='\n\n'.join(lines)
    return modules,dict(module=name,namespace=namespace,network=network,**metadata)
