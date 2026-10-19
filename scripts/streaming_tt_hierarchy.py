"""Actual hierarchy port bindings, checked against the strict flattened graph.

This supplemental interpreter exposes port aliases needed by scalar/word
proofs. It does not assert equivalence: all connected cells are compared to the
existing strict expansion, and the generated kernel proofs check their values.
"""
import json
from streaming_mapped_liberty import require
from streaming_mapped_netlist import bit,expand_hierarchy


def trace_hierarchy(document,top,library):
    expected=expand_hierarchy(document,top,library)['modules'][top]
    modules=document['modules'];parents={};next_bit=2;cells={};instances={}
    def find(value):
        if value not in parents:parents[value]=value
        path=[]
        while parents[value]!=value:path.append(value);value=parents[value]
        for item in path:parents[item]=value
        return value
    def union(left,right):
        left,right=find(left),find(right)
        if left==right:return
        require(not(type(left) is str and type(right) is str),'Hierarchy shorts constants')
        if type(right) is str or type(left) is int and type(right) is int and right<left:left,right=right,left
        parents[right]=left
    top_body=modules[top]
    top_bits=[wire for port in top_body['ports'].values() for wire in port['bits']]
    top_bits += [wire for cell in top_body.get('cells',{}).values()
        for wires in cell['connections'].values() for wire in wires]
    next_bit=max([1,*(wire for wire in top_bits if type(wire) is int)])+1
    def visit(module,path,bindings):
        nonlocal next_bit
        body=modules[module];local={}
        def wire(value):
            nonlocal next_bit
            value=bit(value)
            if type(value) is str:return value
            if value not in local:
                local[value]=value if not path else next_bit
                next_bit=max(next_bit+bool(path),value+1 if not path else next_bit)
                find(local[value])
            return local[value]
        ports={}
        for pin,port in body['ports'].items():
            values=[wire(value) for value in port['bits']];ports[pin]=values
            if bindings is not None:
                for internal,external in zip(values,bindings[pin]):union(internal,external)
        instances[path]=dict(module=module,ports=ports,local=local)
        for cell in body.get('cells',{}).values():
            for values in cell['connections'].values():
                for value in values:wire(value)
        for instance,cell in body.get('cells',{}).items():
            connections={pin:[wire(value) for value in values] for pin,values in cell['connections'].items()}
            key=json.dumps((*path,instance),separators=(',',':'))
            if cell['type'] in library.cells or cell['type']=='$scopeinfo':
                cells[key]={**cell,'connections':connections}
            else:visit(cell['type'],(*path,instance),connections)
    visit(top,(),None)
    def resolved(value):return find(value) if type(value) is int else value
    actual={name:{**cell,'connections':{pin:[resolved(wire) for wire in values]
        for pin,values in cell['connections'].items()}} for name,cell in cells.items()}
    require(actual==expected['cells'],'Hierarchy port tracer differs from actual strict cell/pin expansion')
    return {path:dict(module=value['module'],
        ports={pin:tuple(resolved(wire) for wire in values) for pin,values in value['ports'].items()},
        local={wire:resolved(value) for wire,value in value['local'].items()})
        for path,value in instances.items()}
