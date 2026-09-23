"""Resolve frozen state/path roles and macro geometry in an actual OpenDB.

Run inside pinned OpenROAD Python. Import checks require all endpoints; the
optional placed-macro gate additionally requires positions, power net binding,
reserved rows and signal pin geometry. It does not certify routed metal access.
"""
import hashlib
import json
from pathlib import Path


def inspect(block, target, ownership, roles, geometry, placed):
    units = block.getDbUnitsPerMicron()
    instances = {i.getName(): i for i in block.getInsts()}
    macros = {n: i for n, i in instances.items() if i.getMaster().isBlock()}
    if set(macros) != set(target['macro']['instances']):
        raise ValueError('Database macro inventory differs from target')
    state_cells = {r['cell'] for group in ownership['registers'].values() for r in group}
    actual_state = {n for n, i in instances.items() if i.getMaster().getName().startswith('sg13cmos5l_df')}
    if actual_state != state_cells:
        raise ValueError('Database state ownership changed')

    def endpoint(name, kind):
        if kind == 'port':
            term = block.findBTerm(name)
        else:
            term = block.findITerm(name)
        if term is None or term.getNet() is None:
            raise ValueError('Missing or unconnected target endpoint: ' + name)
        return term.getNet().getName()

    for group in ownership['registers'].values():
        for r in group:
            endpoint(r['d'], 'pin'); endpoint(r['q'], 'pin')
    resolved = {}
    for name, role in roles.items():
        resolved[name] = dict(delay=role['delay'],
            sources={p: endpoint(p, 'pin') for p in role['sources']},
            sinks={p: endpoint(p, role['sink_kind']) for p in role['sinks']})
    macro_report = {}
    power_ports = {}
    if placed:
        for name in target['macro']['power']:
            port = block.findBTerm(name)
            expected = 'POWER' if name == 'VPWR' else 'GROUND'
            if (port is None or port.getNet() is None or port.getNet().getName() != name or
                    str(port.getSigType()) != expected or str(port.getNet().getSigType()) != expected):
                raise ValueError('Missing or misclassified package power rail: ' + name)
            power_ports[name] = expected
    for name, inst in macros.items():
        master = inst.getMaster()
        if master.getName() != target['macro']['master']:
            raise ValueError('Wrong database macro master')
        if [master.getWidth(), master.getHeight()] != [round(x * units) for x in geometry['size_um']]:
            raise ValueError('Database macro dimensions differ from LEF preflight')
        pins = {t.getMTerm().getName(): t for t in inst.getITerms()}
        if set(pins) != set(geometry['pins']):
            raise ValueError('Database macro terminal inventory differs from LEF')
        power = {p: pins[p].getNet().getName() if pins[p].getNet() else None
                 for ps in target['macro']['power'].values() for p in ps}
        bbox = inst.getBBox(); rect = [bbox.xMin(), bbox.yMin(), bbox.xMax(), bbox.yMax()]
        if placed:
            if rect != [round(x * units) for x in geometry['macro_bboxes_um'][name]]:
                raise ValueError('Actual macro location differs from target')
            if str(inst.getOrient()) != {'N': 'R0', 'S': 'R180', 'E': 'R270', 'W': 'R90',
                                        'FN': 'MY', 'FS': 'MX', 'FE': 'MXR90', 'FW': 'MYR90'}[target['macro']['instances'][name]['orientation']]:
                raise ValueError('Actual macro orientation differs from target')
            if any(power[p] != rail for rail, ps in target['macro']['power'].items() for p in ps):
                raise ValueError('Unconnected or wrong macro power rail')
            if any(not list(t.getGeometries()) for t in pins.values()):
                raise ValueError('Macro terminal has no physical geometry')
        macro_report[name] = dict(master=master.getName(), bbox_dbu=rect, orientation=str(inst.getOrient()), power=power,
                                 signal_pins=sum(v['use'] not in ['POWER', 'GROUND'] for v in geometry['pins'].values()))
    corridors = []
    if placed:
        def intersects(a, b):
            return max(a[0], b[0]) < min(a[2], b[2]) and max(a[1], b[1]) < min(a[3], b[3])
        for rect in target['placement_exclusions']:
            rect = [round(x * units) for x in rect]
            rows = [row for row in block.getRows() if intersects(rect, [row.getBBox().xMin(), row.getBBox().yMin(),
                    row.getBBox().xMax(), row.getBBox().yMax()])]
            cells = [n for n, inst in instances.items() if inst.isPlaced() and intersects(rect,
                     [inst.getBBox().xMin(), inst.getBBox().yMin(), inst.getBBox().xMax(), inst.getBBox().yMax()])]
            if rows or cells:
                raise ValueError('Reserved corridor contains rows or placed cells')
            corridors.append(dict(bbox_dbu=rect, clear=True))
    disconnected = sorted(n + '/' + t.getMTerm().getName() for n, inst in instances.items()
                          for t in inst.getITerms() if str(t.getIoType()) == 'OUTPUT' and t.getNet() is None)
    return dict(state_flip_flops=len(state_cells), roles=resolved, macros=macro_report, power_ports=power_ports,
                disconnected_outputs=disconnected,
                dbu_per_micron=units, placed_macros_checked=placed, corridors=corridors,
                boundary='Exact physical endpoints, macro geometry and optional power net binding. No routed metal continuity, timing or pin-access certification.')


def main():
    import odb
    folder = Path('/probe')
    request = json.loads((folder / 'target-request.json').read_text())
    design = Path(request['design'])
    values = [json.loads((design / n).read_text()) for n in
              ['target.json', 'state-ownership.json', 'path-roles.json', 'macro-geometry.json']]
    db = odb.dbDatabase.create(); odb.read_db(db, request['database'])
    result = inspect(db.getChip().getBlock(), *values, request['placed_macros'])
    result['database_sha256'] = hashlib.sha256(Path(request['database']).read_bytes()).hexdigest()
    (folder / 'target-odb.json').write_text(json.dumps(result, indent=2) + '\n')


if __name__ == '__main__':
    main()
