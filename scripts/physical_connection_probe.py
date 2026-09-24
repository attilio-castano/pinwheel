"""Read-only connection measurements in the pinned OpenROAD image.

The caller supplies hash-bound ODBs, configuration and exact driver/net pairs.
Geometry reads saved grid values; STA estimates existing routes without routing.
Neither mode writes a database or changes the source design.
"""
import hashlib
import json
from pathlib import Path
import re
import sys


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def connection_tcl(connections):
    lines = ['puts "%OL_CREATE_REPORT connections.rpt"']
    seen = set()
    for row in connections:
        net, driver = row['net'], row['driver']
        if (net in seen or any(not re.fullmatch(r'[A-Za-z0-9_./\[\]$-]+', s)
                              for s in [net, driver])):
            raise ValueError('Duplicate or unsafe connection selector')
        seen.add(net)
        lines += [f'set it [$::block findITerm {{{driver}}}]',
                  f'if {{$it eq "NULL" || [$it getNet] eq "NULL" || [[$it getNet] getName] ne {{{net}}}}} {{error "Changed connection selector"}}',
                  f'puts {{PINWHEEL_CONNECTION {net}}}',
                  f'report_net -digits 9 {{{net}}}',
                  f'report_check_types -net {{{net}}} -max_slew -max_capacitance -max_fanout -digits 9 -no_line_splits',
                  f'report_checks -through [get_pins [list {{{driver}}}]] -path_delay min_max -group_path_count 1 -digits 9 -fields {{slew cap fanout}} -format full_clock_expanded']
    return '\n'.join(lines + ['puts "%OL_END_REPORT"']) + '\n'


def geometry(request, out):
    import odb
    rows = {}
    for label, entry in request['checkpoints'].items():
        path = Path(entry['database'])
        if digest(path) != entry['sha256']:
            raise ValueError('Changed geometry database')
        db = odb.read_db(odb.dbDatabase.create(), str(path))
        block = db.getChip().getBlock(); grid = block.getGCellGrid()
        x, y = list(grid.getGridX()), list(grid.getGridY())
        layers = {}
        for name in request['layers']:
            layer = db.getTech().findLayer(name)
            capacity = [[grid.getCapacity(layer, ix, iy) for iy in range(len(y))] for ix in range(len(x))]
            usage = [[grid.getUsage(layer, ix, iy) for iy in range(len(y))] for ix in range(len(x))]
            hotspots = [dict(index=[ix, iy], lower_left_dbu=[x[ix], y[iy]],
                capacity=capacity[ix][iy], usage=usage[ix][iy], overflow=usage[ix][iy]-capacity[ix][iy])
                for ix in range(len(x)) for iy in range(len(y)) if usage[ix][iy] > capacity[ix][iy]]
            layers[name] = dict(capacity=capacity, usage=usage, hotspots=hotspots,
                total_capacity=sum(map(sum, capacity)), total_usage=sum(map(sum, usage)),
                overflow=sum(p['overflow'] for p in hotspots))
        pins = {}
        for row in request['connections']:
            net = block.findNet(row['net'])
            driver = block.findITerm(row['driver'])
            if (net is None or driver is None or driver.getNet() is None or
                    driver.getNet().getName() != net.getName()):
                raise ValueError('Changed geometry connection: ' + row['driver'])
            for pin in net.getITerms():
                key = pin.getInst().getName() + '/' + pin.getMTerm().getName()
                shapes = [dict(layer=layer.getName(), bbox_dbu=[rect.xMin(), rect.yMin(), rect.xMax(), rect.yMax()])
                          for layer, rect in pin.getGeometries()]
                if not shapes:
                    raise ValueError('Missing terminal geometry: ' + key)
                pins[key] = shapes
        bindings = {n.getName(): n.getNonDefaultRule().getName()
                    for n in block.getNets() if n.getNonDefaultRule()}
        rules = sorted(r.getName() for r in block.getNonDefaultRules())
        masters = {}
        for name in ['sg13cmos5l_buf_1', 'sg13cmos5l_buf_8']:
            m = db.findMaster(name)
            masters[name] = dict(width_dbu=m.getWidth(), height_dbu=m.getHeight())
        rows[label] = dict(database_sha256=entry['sha256'], dbu_per_micron=block.getDbUnitsPerMicron(),
            grid_x=x, grid_y=y, layers=layers, pins=pins, nondefault_rules=rules,
            net_nondefault_rules=bindings, buffer_masters=masters,
            source_unchanged=digest(path) == entry['sha256'])
    (out/'geometry.json').write_text(json.dumps(rows, separators=(',', ':'))+'\n')


def sta(request, out, label):
    from decimal import Decimal
    from librelane.flows.classic import Classic
    from librelane.state import State
    from librelane.steps.openroad import STAMidPNR
    from physical_checkpoint_sta import analysis_tcl
    entry = request['checkpoints'][label]
    if digest(entry['database']) != entry['sha256'] or digest(request['config']) != request['config_sha256']:
        raise ValueError('Changed timing input')
    cfg = json.loads(Path(request['config']).read_text())
    extra = out/'connections.tcl'
    extra.write_text(analysis_tcl({'verify_nominal_layer_rc': True}) + connection_tcl(request['connections']))
    results = {}
    for corner in cfg['STA_CORNERS']:
        config = Classic(dict(cfg, DEFAULT_CORNER=corner, STA_CORNERS=[corner],
            OPENROAD_THREADS=2, STA_EXTRA_CORNER_TCL_FILE=str(extra)),
            pdk_root='/work/pdk', pdk='ihp-sg13cmos5l', design_dir='/work/core').config
        result = STAMidPNR(config=config, state_in=State.load({'odb': entry['database'], 'metrics': {}})).start(
            step_dir=str(out/corner))
        results[corner] = {k: float(v) if isinstance(v, Decimal) else v for k, v in result.metrics.items()}
    (out/'fresh-timing.json').write_text(json.dumps(results, indent=2)+'\n')
    if digest(entry['database']) != entry['sha256']:
        raise ValueError('Timing source changed')


if __name__ == '__main__':
    request = json.loads(Path('/probe/request.json').read_text())
    if sys.argv[1:] == ['geometry']:
        geometry(request, Path('/probe'))
    elif len(sys.argv) == 2 and sys.argv[1] in request['checkpoints']:
        sta(request, Path('/probe')/sys.argv[1], sys.argv[1])
    else:
        raise ValueError('Select geometry or an exact checkpoint label')
