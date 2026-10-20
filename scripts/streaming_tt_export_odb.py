"""Read final OpenDB signal connectivity; never inherit a stale flow state.nl.

Run in the pinned native physical container's Python environment with `odb`.
The ODB is read only.  Power-only masters and every power terminal are retained
in a separate inventory, not silently treated as Boolean logic or signed off.
"""
import argparse
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path


POWER = frozenset(('POWER', 'GROUND'))
PHYSICAL_ONLY = frozenset('sg13cmos5l_'+name for name in
    ('fill_1','fill_2','fill_4','fill_8','decap_4','decap_8'))


def require(value, message):
    if not value: raise ValueError(message)


def public_pins(reference, top):
    require(type(reference) is dict and top in reference.get('modules', {}), 'Missing selected reference top')
    ports = reference['modules'][top].get('ports')
    require(type(ports) is dict and ports, 'Missing selected reference public interface')
    pins = {}
    for name, port in ports.items():
        require(port.get('direction') in ('input', 'output') and type(port.get('bits')) is list and port['bits'] and
            port.get('upto', 0) == 0 and port.get('offset', 0) == 0, 'Unsupported reference public port')
        names = [name] if len(port['bits']) == 1 else [name + '[' + str(k) + ']' for k in range(len(port['bits']))]
        require(not (set(names) & pins.keys()), 'Ambiguous reference scalar port spelling')
        for index, pin in enumerate(names): pins[pin] = (name, index, port['direction'])
    return ports, pins


def export_block(block, reference, top):
    """Pure object traversal, testable without loading a native database."""
    require(block is not None and block.getName() == top, 'OpenDB block differs from selected top')
    expected_ports, expected_pins = public_pins(reference, top)
    nets = sorted(block.getNets(), key=lambda net: net.getName())
    names = [net.getName() for net in nets]
    require(all(type(name) is str and name for name in names) and len(names) == len(set(names)),
        'OpenDB has empty/duplicate net names')
    wires = {name: index + 2 for index, name in enumerate(names)}
    net_types = {net.getName(): str(net.getSigType()) for net in nets}
    require(all(kind in ('SIGNAL', 'CLOCK', *POWER) for kind in net_types.values()), 'Unclassified OpenDB signal type')
    next_wire = len(wires) + 2
    output_ports = {name: dict(direction=port['direction'], bits=[None] * len(port['bits']))
        for name, port in expected_ports.items()}
    seen, power_bterms, bterms = set(), {}, {}
    for term in sorted(block.getBTerms(), key=lambda term: term.getName()):
        name, net = term.getName(), term.getNet()
        require(name not in seen and net is not None, 'Duplicate/disconnected OpenDB block terminal')
        seen.add(name)
        kind, direction = str(term.getSigType()), str(term.getIoType())
        require(net.getName() in wires, 'OpenDB block terminal names an unknown net')
        if kind in POWER:
            require(net_types[net.getName()] == kind and name not in expected_pins,
                'Power terminal shorts a signal interface')
            power_bterms[name] = dict(direction=direction, signal_type=kind, net=net.getName())
            continue
        require(name in expected_pins and kind in ('SIGNAL', 'CLOCK') and net_types[net.getName()] not in POWER,
            'Unexpected/shorted physical public signal pin')
        port, index, expected = expected_pins[name]
        require(direction.lower() == expected, 'Physical public pin direction changed')
        output_ports[port]['bits'][index] = wires[net.getName()]
        bterms[name] = dict(port=port, index=index, direction=expected, net=net.getName())
    require(set(bterms) == set(expected_pins) and all(None not in port['bits'] for port in output_ports.values()),
        'OpenDB is missing a selected public pin')
    cells, masters, physical_only, unconnected_outputs, instances = {}, {}, {}, {}, {}
    instance_names = set()
    for inst in sorted(block.getInsts(), key=lambda inst: inst.getName()):
        name, master = inst.getName(), inst.getMaster()
        require(type(name) is str and name and name not in instance_names and master is not None,
            'Duplicate/unnamed physical instance or missing master')
        instance_names.add(name)
        terms = list(inst.getITerms())
        terminal_names = [term.getMTerm().getName() for term in terms]
        master_terms = list(master.getMTerms())
        require(len(terminal_names) == len(set(terminal_names)) and
            set(terminal_names) == {term.getName() for term in master_terms}, 'OpenDB master terminal inventory mismatch')
        signature = {term.getName(): dict(direction=str(term.getIoType()), signal_type=str(term.getSigType()))
            for term in master_terms}
        kind = master.getName()
        require(kind not in masters or masters[kind] == signature, 'Inconsistent OpenDB master definition')
        masters[kind] = signature
        directions, connections, inventory = {}, {}, {}
        for term in sorted(terms, key=lambda term: term.getMTerm().getName()):
            pin, net = term.getMTerm().getName(), term.getNet()
            pin_kind, direction = str(term.getMTerm().getSigType()), str(term.getIoType())
            inventory[pin] = dict(direction=direction, signal_type=pin_kind,
                net=None if net is None else net.getName())
            if pin_kind in POWER:
                require(net is None or net_types.get(net.getName()) == pin_kind, 'Misbound physical power terminal')
                continue
            require(pin_kind in ('SIGNAL', 'CLOCK') and direction in ('INPUT', 'OUTPUT'),
                'Unsupported functional OpenDB terminal')
            directions[pin] = direction.lower()
            if net is None:
                require(direction == 'OUTPUT', 'Disconnected functional physical input')
                wire = next_wire; next_wire += 1
                unconnected_outputs[name + '/' + pin] = wire
            else:
                require(net.getName() in wires and net_types[net.getName()] not in POWER,
                    'Physical signal pin shorts a power rail')
                wire = wires[net.getName()]
            connections[pin] = [wire]
        instances[name] = dict(master=kind, master_type=str(master.getType()), terminals=inventory)
        if not directions:
            require(kind in PHYSICAL_ONLY and signature and
                all(value['signal_type'] in POWER for value in signature.values()),
                'Physical-only master has an unclassified signal pin')
            physical_only[name] = kind
            continue
        cells[name] = dict(type=kind, parameters={}, port_directions=directions, connections=connections)
    document = dict(modules={top:dict(ports=output_ports,cells=cells,netnames={
        name:dict(hide_name=0,bits=[wire],attributes={}) for name,wire in wires.items()
        if net_types[name] not in POWER})})
    inventory = dict(schema='pinwheel.streaming-tt-odb-inventory.v1',top=top,
        nets={name:dict(wire=wires[name],signal_type=net_types[name]) for name in names},
        public_bterms=bterms,power_bterms=power_bterms,masters=masters,instances=instances,
        physical_only_instances=physical_only,unconnected_signal_outputs=unconnected_outputs,
        instance_counts=dict(sorted(Counter(value['master'] for value in instances.values()).items())),
        signal_model_instances=len(cells),power_connectivity_signed_off=False)
    return document,inventory


def main(argv=None):
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--database',required=True);parser.add_argument('--reference',required=True)
    parser.add_argument('--top',required=True);parser.add_argument('--out',required=True)
    args=parser.parse_args(argv)
    database,reference,out=Path(args.database),Path(args.reference),Path(args.out)
    require(database.is_file() and not database.is_symlink() and reference.is_file() and not reference.is_symlink(),
        'Actual ODB and selected reference must be regular files')
    original_db,original_reference=database.read_bytes(),reference.read_bytes()
    import odb
    db=odb.dbDatabase.create();odb.read_db(db,str(database))
    chip=db.getChip();require(chip is not None,'Missing OpenDB chip')
    document,inventory=export_block(chip.getBlock(),json.loads(original_reference),args.top)
    require(database.read_bytes()==original_db and reference.read_bytes()==original_reference,
        'ODB/reference changed during native export')
    out.mkdir(parents=True,exist_ok=False)
    artifacts={}
    for filename,value in [('connectivity.json',document),('inventory.json',inventory)]:
        data=(json.dumps(value,indent=2,sort_keys=True)+'\n').encode();(out/filename).write_bytes(data)
        artifacts[filename]=sha256(data).hexdigest()
    receipt=dict(schema='pinwheel.streaming-tt-odb-export.v1',database=str(database),
        database_sha256=sha256(original_db).hexdigest(),reference=str(reference),
        reference_sha256=sha256(original_reference).hexdigest(),source_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
        top=args.top,artifacts_sha256=artifacts,read_only_database=True,
        boundary='Actual final OpenDB signal connectivity. Boolean, timing and power checks are separate.')
    (out/'receipt.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
    print(json.dumps(receipt,sort_keys=True))


if __name__=='__main__':main()
