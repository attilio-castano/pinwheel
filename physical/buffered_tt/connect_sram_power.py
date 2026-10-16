"""Connect exact SRAM columns to the tile-edge Metal4 supply grid.

Scope is two north-oriented 64x64 SRAMs sharing their x coordinate. The step
checks loaded geometry and via landings before changing its in-memory ODB;
power continuity, extracted timing, DRC and IR drop remain separate gates.
"""
import json
from pathlib import Path
import click
import odb
from reader import click_odb


SUPPLIES = {'VPWR': ['VDD!', 'VDDARRAY!'], 'VGND': ['VSS!']}


def rectangle(shape):
    return (shape.xMin(), shape.yMin(), shape.xMax(), shape.yMax())


def overlaps(a, b, clearance=0):
    return (a[2] + clearance > b[0] and a[0] - clearance < b[2]
            and a[3] + clearance > b[1] and a[1] - clearance < b[3])


def contains(outer, inner):
    return (outer[0] <= inner[0] <= inner[2] <= outer[2]
            and outer[1] <= inner[1] <= inner[3] <= outer[3])


def same_net(left, right):
    # OpenDB returns fresh Python proxies; Python equality is not DB identity.
    # Names are unique within the one already validated block.
    return left is not None and right is not None and left.getName() == right.getName()


def landing_rectangles(via, x, y):
    result = {}
    for shape in via.getBoxes():
        layer = shape.getTechLayer().getName()
        a, b, c, d = rectangle(shape)
        result.setdefault(layer, []).append((x+a, y+b, x+c, y+d))
    return result


def stack_fits(landings, column, rail):
    if not all(contains(rail, box) for box in landings[0].get('Metal1', [])):
        return False
    if not all(contains(column, box) for box in landings[-1].get('Metal4', [])):
        return False
    if not landings[0].get('Metal1') or not landings[-1].get('Metal4'):
        return False
    # Adjacent generated vias must actually share an intermediate metal area.
    for index, layer in enumerate(('Metal2', 'Metal3')):
        if not any(overlaps(a, b) for a in landings[index].get(layer, [])
                   for b in landings[index+1].get(layer, [])):
            return False
    return True


def is_corridor_metal4(shape, xlo, xhi):
    layer = shape.getTechLayer()
    return (layer is not None and layer.getName() == 'Metal4'
            and shape.xMax() > xlo and shape.xMin() < xhi)


@click.command()
@click_odb
def connect(reader):
    block, tech = reader.block, reader.tech
    plan = json.loads(Path(__file__).with_name('power-columns.json').read_text())
    expected = {'engine.memory.storage0', 'engine.memory.storage1'}
    instances = [i for i in block.getInsts() if i.getMaster().isBlock()]
    if {i.getName() for i in instances} != expected:
        raise click.ClickException('Unexpected physical macro instances')
    for inst in instances:
        if inst.getOrient() != 'R0' or inst.getMaster().getName() != 'RM_IHPSG13_1P_64x64_c2_bm_bist':
            raise click.ClickException('Unexpected macro master or orientation')
    if len({i.getBBox().xMin() for i in instances}) != 1:
        raise click.ClickException('SRAM power extension requires aligned x coordinates')
    dbu = block.getDefUnits()
    metal = tech.findLayer('Metal4')
    core, die = block.getCoreArea(), block.getDieArea()
    macro_boxes = [rectangle(i.getBBox()) for i in instances]
    xlo, xhi = macro_boxes[0][0], macro_boxes[0][2]
    clearance = round(plan['clearance_um'] * dbu)
    stacks = []
    for a, b in zip(('Metal1', 'Metal2', 'Metal3'), ('Metal2', 'Metal3', 'Metal4')):
        candidates = [v for v in block.getVias() if v.getBottomLayer() is not None and v.getTopLayer() is not None
                      and v.getBottomLayer().getName() == a and v.getTopLayer().getName() == b]
        if not candidates:
            raise click.ClickException('Missing generated standard-cell rail via: '+a+'/'+b)
        stacks.append(min(candidates, key=lambda v: v.getBBox().yMax()-v.getBBox().yMin()))

    net_data = {}
    # Freeze and validate BOTH nets before either one is mutated.
    for name, pin_names in SUPPLIES.items():
        net = block.findNet(name)
        if net is None:
            raise click.ClickException('Missing supply net '+name)
        contacts = {}
        supply_rectangles = []
        for inst in instances:
            for pin in pin_names:
                iterm = inst.findITerm(pin)
                if iterm is None or not same_net(iterm.getNet(), net):
                    raise click.ClickException('Incorrect supply binding: '+inst.getName()+'/'+pin)
                ox, oy = inst.getBBox().xMin(), inst.getBBox().yMin()
                term = inst.getMaster().findMTerm(pin)
                shapes = [rectangle(r) for p in term.getMPins() for r in p.getGeometry()
                          if r.getTechLayer() is not None and r.getTechLayer().getName() == 'Metal4']
                supply_rectangles.extend((ox+a, oy+b, ox+c, oy+d) for a, b, c, d in shapes)
                contacts[inst.getName()+'/'+pin] = [(ox+a, oy+b, ox+c, oy+d) for a, b, c, d in shapes]
        columns = [(round(a*dbu), die.yMin(), round(b*dbu), die.yMax()) for a, b in plan['nets'][name]]
        if any(not contains(rectangle(die), column) for column in columns):
            raise click.ClickException('Supply column extends outside the die')
        contact_counts = {}
        for pin, shapes in contacts.items():
            count = sum(any(contains((a, die.yMin(), c, die.yMax()), col)
                            for a, b, c, d in shapes) for col in columns)
            if count < 2:
                raise click.ClickException('Too few loaded direct supply contacts: '+pin)
            contact_counts[pin] = count
        for column in columns:
            for inst in instances:
                pin = pin_names[0]
                if not any(contains((a, die.yMin(), c, die.yMax()), column)
                           for a, b, c, d in contacts[inst.getName()+'/'+pin]):
                    raise click.ClickException('Stripe misses loaded supply column')
            for term in block.getBTerms():
                if term.getSigType() != 'SIGNAL':
                    continue
                for p in term.getBPins():
                    for r in p.getBoxes():
                        if r.getTechLayer() is not None and r.getTechLayer().getName() == 'Metal4':
                            if overlaps(column, rectangle(r), clearance):
                                raise click.ClickException('Stripe collides with actual template signal pin')
        swires = list(net.getSWires())
        if len(swires) != 1:
            raise click.ClickException('Expected one generated supply special wire')
        swire = swires[0]
        wires = list(swire.getWires())
        rails = [r for r in wires if r.getTechLayer() is not None
                 and r.getTechLayer().getName() == 'Metal1' and r.xMax()-r.xMin() > r.yMax()-r.yMin()]
        removed_x = [(r.xMin(), r.xMax()) for r in wires if is_corridor_metal4(r, xlo, xhi)]
        retained = [rectangle(r) for r in wires if r.getTechLayer() is not None
                    and r.getTechLayer().getName() == 'Metal4' and not is_corridor_metal4(r, xlo, xhi)]
        bpins = [p for term in net.getBTerms() for p in term.getBPins()]
        if not bpins:
            raise click.ClickException('Missing generated power boundary pin')
        via_sites = []
        for column in columns:
            cx = (column[0]+column[2])//2
            sites = []
            for rail in rails:
                y = (rail.yMin()+rail.yMax())//2
                if any(b-3*dbu <= y <= d+3*dbu for a, b, c, d in macro_boxes):
                    continue
                landings = [landing_rectangles(via, cx, y) for via in stacks]
                if stack_fits(landings, column, rectangle(rail)):
                    sites.append((cx, y))
            if len(sites) < 2:
                raise click.ClickException('Supply column lacks two enclosed same-net rail via stacks')
            via_sites.append(sites)
        net_data[name] = dict(net=net, swire=swire, columns=columns, contacts=contact_counts,
                              supply_rectangles=supply_rectangles, removed_x=removed_x,
                              retained=retained, bpins=bpins, via_sites=via_sites)

    minimum_gap = None
    for name, data in net_data.items():
        opposite = net_data['VGND' if name == 'VPWR' else 'VPWR']
        targets = opposite['columns'] + opposite['retained'] + opposite['supply_rectangles']
        for column in data['columns']:
            for other in targets:
                if overlaps(column, other, clearance):
                    raise click.ClickException('New column conflicts with opposite-net Metal4 geometry')
                if column[1] < other[3] and column[3] > other[1]:
                    gap = max(other[0]-column[2], column[0]-other[2])
                    minimum_gap = gap if minimum_gap is None else min(minimum_gap, gap)

    report = dict(schema='pinwheel-buffered-tt-power-geometry-v2', nets={},
                  old_core_endpoints_um=[core.yMin()/dbu, core.yMax()/dbu],
                  new_die_endpoints_um=[die.yMin()/dbu, die.yMax()/dbu],
                  tile_edge_access='Each replacement stripe and power BPin reaches both die y boundaries.',
                  minimum_opposite_metal4_gap_um=minimum_gap/dbu,
                  required_clearance_um=clearance/dbu,
                  via_stack=[v.getName() for v in stacks],
                  boundary='Geometry and same-layer/via landing checks only; downstream power continuity, DRC, IR drop and tile precheck required.')
    for name, data in net_data.items():
        swire = data['swire']
        removed_segments = removed_vias = removed_patches = 0
        for r in list(swire.getWires()):
            layer = r.getTechLayer()
            on_removed = any(r.xMax() > a and r.xMin() < b for a, b in data['removed_x'])
            remove_column = is_corridor_metal4(r, xlo, xhi)
            remove_landing = on_removed and (layer is None or layer.getName() in ('Metal2', 'Metal3'))
            if remove_column or remove_landing:
                removed_segments += int(remove_column)
                removed_vias += int(layer is None)
                removed_patches += int(layer is not None and layer.getName() in ('Metal2', 'Metal3'))
                odb.dbSBox_destroy(r)
        for p in data['bpins']:
            for r in list(p.getBoxes()):
                if is_corridor_metal4(r, xlo, xhi):
                    odb.dbBox_destroy(r)
        vias = 0
        for column, sites in zip(data['columns'], data['via_sites']):
            a, b, c, d = column
            odb.dbSBox_create(swire, metal, a, b, c, d, 'STRIPE')
            odb.dbBox_create(data['bpins'][0], metal, a, b, c, d)
            for cx, y in sites:
                for via in stacks:
                    odb.dbSBox_create(swire, via, cx, y, 'STRIPE')
                    vias += 1
        report['nets'][name] = dict(die_height_column_stripes=len(data['columns']),
                                  loaded_macro_contact_columns=data['contacts'],
                                  removed_base_segments=removed_segments,
                                  removed_base_vias=removed_vias,
                                  removed_base_patches=removed_patches,
                                  rail_via_stacks_added=sum(map(len, data['via_sites'])),
                                  rail_vias_added=vias,
                                  minimum_rail_stacks_per_column=min(map(len, data['via_sites'])))
    Path('buffered-sram-power.json').write_text(json.dumps(report, indent=2)+'\n')
    print('[INFO] Buffered SRAM power columns: '+json.dumps(report['nets'], sort_keys=True))


if __name__ == '__main__':
    connect()
