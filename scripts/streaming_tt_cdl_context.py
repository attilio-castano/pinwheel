#!/usr/bin/env python3
"""Bind an actual-ODB top CDL to the exact pinned transistor master context.

The top and library bytes are preserved. Every top instance's positional pins
are independently checked against actual ODB terminal/net readback.
"""
from collections import Counter
from pathlib import Path
import hashlib,json,re

def require(ok,message):
    if not ok:raise ValueError(message)

def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def statements(text):
    """Read only explicit CDL statements; retain bytes separately for output."""
    result=[]
    for raw in text.splitlines():
        line=raw.strip()
        if not line or line.startswith('*'):continue
        if line.startswith('+'):
            require(result,'Orphan CDL continuation');result[-1]+=' '+line[1:].strip()
        else:result.append(line)
    return result

def modules(text):
    result={};current=None
    for line in statements(text):
        fields=line.split();directive=fields[0].upper()
        if directive=='.SUBCKT':
            require(current is None and len(fields)>1,'Nested/incomplete CDL subcircuit')
            name=fields[1];key=name.upper()
            require(key not in result,'Duplicate CDL module '+name)
            pins=fields[2:];require(len(pins)==len(set(p.upper() for p in pins)),'Duplicate CDL pin '+name)
            result[key]=dict(name=name,pins=pins,body=[]);current=result[key]
        elif directive=='.ENDS':
            require(current is not None and len(fields)<=2 and
                (len(fields)==1 or fields[1].upper()==current['name'].upper()),'Misbound CDL .ENDS')
            current=None
        else:
            require(not directive.startswith('.') or directive=='.PARAM','Unresolved or unsupported CDL directive '+directive)
            if current is None and directive=='.PARAM':
                # The pinned I/O CDL contains a global .PARAM statement. Its
                # exact bytes stay in the combined deck and KLayout parses it.
                continue
            require(current is not None,'CDL statement outside module');current['body'].append(fields)
    require(current is None and result,'Unclosed/empty CDL modules')
    return result

def child_call(fields):
    """Resolve explicit CDL X-call syntax, including the PDK's / separator."""
    require(fields and fields[0].startswith(('X','x')),'Expected master X call')
    if '/' in fields:
        index=fields.index('/');require(fields.count('/')==1 and index>=1 and index+1<len(fields),'Malformed child X call')
        master=fields[index+1];nodes=fields[1:index];parameters=fields[index+2:]
    else:
        end=next((i for i,value in enumerate(fields[1:],1) if '=' in value),len(fields))
        require(end>=2,'Missing child master');master=fields[end-1];nodes=fields[1:end-1];parameters=fields[end:]
    require(all('=' in value for value in parameters),'Unsupported child X parameters')
    return master,nodes

def used_master_closure(masters,roots):
    visited=set();active=set();primitive_counts=Counter()
    def visit(key):
        require(key in masters,'Unresolved used child master '+key)
        require(key not in active,'Cycle in used master hierarchy '+key)
        if key in visited:return
        active.add(key)
        for fields in masters[key]['body']:
            if fields[0].startswith(('X','x')):
                name,nodes=child_call(fields);child=name.upper()
                require(child in masters,'Unresolved used child master '+name)
                require(len(nodes)==len(masters[child]['pins']),'Wrong used child positional arity '+name)
                visit(child)
            else:primitive_counts[fields[0][0].upper()]+=1
        active.remove(key);visited.add(key)
    for key in roots:visit(key)
    require(primitive_counts['M']>0,'Used reachable master context lacks MOS transistor definitions')
    return visited,primitive_counts

def compose(top_path,library_paths,inventory_path,*,top):
    """Return complete bytes only after exact actual ODB pin-order checks pass."""
    top_path=Path(top_path);library_paths=[Path(p) for p in library_paths]
    require(library_paths and len(library_paths)==len(set(p.resolve() for p in library_paths)),
        'Missing/duplicate master CDL path')
    top_modules=modules(top_path.read_text());require(set(top_modules)=={top.upper()},'Exported top module differs')
    master_modules={}
    for path in library_paths:
        for key,value in modules(path.read_text()).items():
            require(key not in master_modules and key!=top.upper(),'Duplicate master/top module '+key)
            master_modules[key]=value
    inventory=json.loads(Path(inventory_path).read_text())
    require(inventory['top']==top and type(inventory['instances']) is dict,'Wrong actual ODB inventory top')
    require(not set(inventory['public_bterms']) & set(inventory['power_bterms']),'Public/power BTerm key overlap')
    bterms={**inventory['public_bterms'],**inventory['power_bterms']}
    require(set(top_modules[top.upper()]['pins'])==set(bterms),'Top CDL/ODB boundary pin inventory differs')
    # OpenROAD emits public port names for aliased ODB nets (for example a
    # tie output net5003 exported as uio_oe[3]). Resolve only actual BTerm aliases.
    aliases={name:value['net'] for name,value in bterms.items()}
    instances=inventory['instances'];seen=set();counts=Counter();pin_count=0;floating=set()
    actual_nets={term['net'] for instance in instances.values() for term in instance['terminals'].values()
        if term['net'] is not None}
    folded={}
    for net in sorted(actual_nets):
        require(net.upper() not in folded,'Case-insensitive actual net collision '+net);folded[net.upper()]=net
    for alias,net in aliases.items():
        require(alias.upper() not in folded or folded[alias.upper()]==net,'Case-insensitive BTerm/net collision '+alias)
        folded[alias.upper()]=net
    require(len({name.upper() for name in instances})==len(instances),'Case-insensitive instance collision')
    for fields in top_modules[top.upper()]['body']:
        require(fields[0].startswith(('X','x')) and len(fields)>2,'Top contains non-instance statement')
        name=fields[0][1:];require(name in instances and name not in seen,'Missing/duplicate actual ODB instance '+name)
        seen.add(name);actual=instances[name];master=fields[-1];key=master.upper()
        require(master==actual['master'] and key in master_modules,'Missing or changed actual master '+master)
        pins=master_modules[key]['pins'];nodes=fields[1:-1]
        require(len(nodes)==len(pins),'Wrong positional CDL pin count '+name)
        require(set(pins)==set(actual['terminals']),'CDL/ODB master terminal inventory differs '+name)
        expected=[actual['terminals'][pin]['net'] for pin in pins]
        for node,net in zip(nodes,expected):
            if net is None:
                require(re.fullmatch(r'_unconnected_[0-9]+',node) and node not in floating and
                    node.upper() not in folded,'Unbound CDL pin was joined/reused '+name)
                floating.add(node);folded[node.upper()]=node
            else:require(aliases.get(node,node)==net,'CDL positional pin order/net binding differs '+name)
        counts[master]+=1;pin_count+=len(pins)
    require(seen==set(instances),'Exported CDL omitted actual ODB instances')
    used_modules,used_primitives=used_master_closure(master_modules,{name.upper() for name in counts})
    primitive_counts=Counter()
    for master in master_modules.values():
        for fields in master['body']:
            if not fields[0].startswith(('X','x')):primitive_counts[fields[0][0].upper()]+=1
    require(primitive_counts['M']>0,'Master context lacks MOS transistor definitions')
    # Concatenation preserves every input byte and adds only separating newlines.
    chunks=[p.read_bytes() for p in library_paths]+[top_path.read_bytes()]
    data=b'\n'.join(chunks)+b'\n'
    combined=modules(data.decode())
    require(set(combined)==set(master_modules)|set(top_modules),'Combined CDL module inventory differs')
    return data,dict(top=top,actual_instances=len(seen),actual_terminals=pin_count,
        instance_counts=dict(sorted(counts.items())),master_modules=len(master_modules),
        primitive_definitions_by_prefix=dict(primitive_counts),
        used_reachable_master_modules=sorted(used_modules),used_reachable_primitive_definitions_by_prefix=dict(used_primitives),
        exact_top_bytes_preserved=True,exact_master_bytes_preserved=True,
        actual_odb_pin_order_and_net_binding_verified=True,isolated_unconnected_terminals=len(floating),
        input_sha256={str(p.resolve()):sha(p) for p in [top_path,*library_paths,Path(inventory_path)]})
