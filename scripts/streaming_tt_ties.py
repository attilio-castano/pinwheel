"""Explicit constant-net clustering; electrical/routing acceptance is separate.

Run with the pinned OpenROAD Python interpreter. Never edits the input ODB.
Only the two pinned Liberty literal-constant cells may be replaced. Every
other instance, location, terminal and public pin is checked after re-reading
the written ODB. This is a physical transformation, not a kernel certificate.
"""
import argparse
from dataclasses import dataclass
from hashlib import sha256
import json
import math
from pathlib import Path

from streaming_mapped_liberty import parse_document, group_name, scalar


TIES = {'sg13cmos5l_tielo': ('L_LO', False), 'sg13cmos5l_tiehi': ('L_HI', True)}
POWER = {'POWER', 'GROUND'}
CORNERS_SHA256 = frozenset((
    '34163f3e7de9f854afac57332ba06f1739b78e7ac35660a8a5ddd39c570124ad',
    'af12d75a72d19648fa690027d29843fbae550aa91f4e40dd3339c7116d6e425d',
    '3ee222c580ba33acb2131ac2bf224ff8ee9700751835b73aaec72b670bb31d3c'))


def require(value, message):
    if not value: raise ValueError(message)


def digest(path): return sha256(Path(path).read_bytes()).hexdigest()


def tie_contract(paths):
    """Interpret actual Liberty functions and inherited electrical limits."""
    require(paths, 'At least one actual Liberty corner is required')
    caps, limits, ff_masters, identities = {}, [], set(), {}
    for path in paths:
        path = Path(path)
        require(path.is_file() and not path.is_symlink(), 'Liberty must be a regular file')
        data = path.read_bytes(); roots = parse_document(data.decode())
        require(len(roots) == 1 and roots[0].name == 'library', 'One Liberty library required')
        root = roots[0]
        default_cap = float(scalar(root.children, 'default_input_pin_cap'))
        max_cap = float(scalar(root.children, 'default_max_capacitance'))
        max_fanout = float(scalar(root.children, 'default_max_fanout'))
        require(all(math.isfinite(x) and x > 0 for x in (default_cap, max_cap, max_fanout)),
            'Invalid inherited Liberty limits')
        cells = {}
        for item in root.children:
            if item.name != 'cell': continue
            name = group_name(item)
            require(name not in cells, 'Duplicate Liberty cell')
            cells[name] = item
            if any(child.name == 'ff' for child in item.children): ff_masters.add(name)
            for pin in [child for child in item.children if child.name == 'pin']:
                pin_name = group_name(pin)
                if scalar(pin.children, 'direction') != 'input': continue
                cap = scalar(pin.children, 'capacitance', required=False)
                cap = default_cap if cap is None else float(cap)
                require(math.isfinite(cap) and cap >= 0, 'Invalid input-pin capacitance')
                caps[(name, pin_name)] = max(caps.get((name, pin_name), 0.0), cap)
        for name, (output, value) in TIES.items():
            require(name in cells, 'Pinned constant cell absent')
            cell = cells[name]
            require(not any(child.name in ('ff', 'latch', 'statetable') for child in cell.children),
                'Stateful constant cell is unsupported')
            pins = [child for child in cell.children if child.name == 'pin']
            require(len(pins) == 1 and group_name(pins[0]) == output and
                scalar(pins[0].children, 'direction') == 'output' and
                scalar(pins[0].children, 'function') == str(int(value)), 'Actual tie function changed')
            for name_limit, inherited in [('max_capacitance', max_cap), ('max_fanout', max_fanout)]:
                explicit = scalar(pins[0].children, name_limit, required=False)
                limit = inherited if explicit is None else float(explicit)
                require(math.isfinite(limit) and limit > 0, 'Invalid tie-output limit')
                limits.append((name_limit, limit))
        identities[str(path)] = sha256(data).hexdigest()
    return dict(input_caps=caps, max_fanout=min(v for k, v in limits if k == 'max_fanout'),
        max_capacitance_pf=min(v for k, v in limits if k == 'max_capacitance'),
        ff_masters=ff_masters, liberty_sha256=identities)


@dataclass(frozen=True)
class Sink:
    key: tuple
    value: bool
    x: int
    y: int
    capacitance_pf: float


def cluster(sinks, *, max_fanout, max_distance, max_capacitance_pf, anchor):
    """Deterministic, bounded groups; anchor returns an actual output location."""
    require(type(max_fanout) is int and max_fanout > 0 and max_distance > 0 and
        math.isfinite(max_capacitance_pf) and max_capacitance_pf > 0, 'Invalid clustering limits')
    require(len({s.key for s in sinks}) == len(sinks), 'Duplicate physical sink')
    bins = {}
    pitch = max(1, max_distance // 2)
    for sink in sinks:
        require(type(sink.value) is bool and math.isfinite(sink.capacitance_pf) and
            0 <= sink.capacitance_pf <= max_capacitance_pf, 'Invalid or excessive sink load')
        bins.setdefault((sink.value, sink.x // pitch, sink.y // pitch), []).append(sink)
    groups = []
    for key in sorted(bins):
        pending = sorted(bins[key], key=lambda s: (s.x, s.y, s.key))
        while pending:
            first = pending[0]
            point = anchor(first.value, len(groups), (first.x, first.y))
            selected, remainder, cap = [], [], 0.0
            for sink in pending:
                distance = abs(sink.x - point[0]) + abs(sink.y - point[1])
                if len(selected) < max_fanout and distance <= max_distance and cap + sink.capacitance_pf <= max_capacitance_pf:
                    selected.append(sink); cap += sink.capacitance_pf
                else: remainder.append(sink)
            require(first in selected, 'Placed constant output is too far from its first sink')
            groups.append(dict(value=first.value, point=point, sinks=selected, capacitance_pf=cap,
                max_distance=max(abs(s.x-point[0]) + abs(s.y-point[1]) for s in selected)))
            pending = remainder
    require(sum(len(group['sinks']) for group in groups) == len(sinks), 'Incomplete sink partition')
    return groups


def term_point(term):
    result = tuple(term.getAvgXY())
    require(len(result) == 3 and result[0], 'Physical terminal has no geometric location')
    return int(result[1]), int(result[2])


def bterm_point(term):
    boxes = [box for pin in term.getBPins() for box in pin.getBoxes()]
    require(boxes, 'Public constant sink has no placed shape')
    # Full extent is retained in the report; the named bound is center-to-center.
    return ((min(b.xMin() for b in boxes) + max(b.xMax() for b in boxes)) // 2,
        (min(b.yMin() for b in boxes) + max(b.yMax() for b in boxes)) // 2)


def inventory(block):
    instances, terms = {}, {}
    for inst in block.getInsts():
        name, kind = inst.getName(), inst.getMaster().getName()
        require(name not in instances, 'Duplicate instance')
        instances[name] = dict(master=kind, location=list(inst.getLocation()),
            orientation=str(inst.getOrient()), status=str(inst.getPlacementStatus()))
        for term in inst.getITerms():
            key = ('iterm', name, term.getMTerm().getName())
            require(key not in terms, 'Duplicate instance pin')
            terms[key] = None if term.getNet() is None else term.getNet().getName()
    for term in block.getBTerms():
        key = ('bterm', term.getName())
        require(key not in terms, 'Duplicate public pin')
        terms[key] = None if term.getNet() is None else term.getNet().getName()
    return instances, terms


def constants(block):
    nets, ties = {}, set()
    for inst in block.getInsts():
        kind = inst.getMaster().getName()
        if kind not in TIES: continue
        output, value = TIES[kind]; ties.add(inst.getName())
        signal = [t for t in inst.getITerms() if str(t.getMTerm().getSigType()) not in POWER]
        require(len(signal) == 1 and signal[0].getMTerm().getName() == output and
            str(signal[0].getIoType()) == 'OUTPUT', 'Actual tie master pin inventory differs')
        net = signal[0].getNet()
        if net is None: continue
        name = net.getName()
        require(str(net.getSigType()) == 'SIGNAL' and (name not in nets or nets[name] == value),
            'Tie output shorts a non-signal or opposite constant')
        nets[name] = value
    for net in block.getNets():
        if net.getName() not in nets: continue
        require(not any(str(t.getIoType()) != 'INPUT' and t.getInst().getName() not in ties for t in net.getITerms()),
            'Constant net has a second functional driver')
        require(not any(str(t.getIoType()) != 'OUTPUT' for t in net.getBTerms()), 'Constant net shorts a public input')
    return nets, ties


def verify_transform(before, after, before_constants, after_constants, old_ties, new_ties):
    old_instances, old_terms = before; new_instances, new_terms = after
    old_non = {k:v for k,v in old_instances.items() if k not in old_ties}
    new_non = {k:v for k,v in new_instances.items() if k not in new_ties}
    require(old_non == new_non, 'A non-tie instance/type/location/orientation/status changed')
    old_pins = {k:v for k,v in old_terms.items() if not (k[0] == 'iterm' and k[1] in old_ties)}
    new_pins = {k:v for k,v in new_terms.items() if not (k[0] == 'iterm' and k[1] in new_ties)}
    require(set(old_pins) == set(new_pins), 'Functional/public terminal inventory changed')
    for key, old_net in old_pins.items():
        new_net = new_pins[key]
        if old_net in before_constants:
            require(new_net in after_constants and after_constants[new_net] == before_constants[old_net],
                'A literal constant sink changed value')
        else: require(new_net == old_net, 'A nonconstant terminal connection changed')


def verify_groups(block, groups, contract, max_fanout, max_distance_um, external_load_pf):
    """Recompute bounds from the written native database, never report flags."""
    unit = block.getDbUnitsPerMicron(); maximum = 0.0
    for group in groups:
        driver = block.findInst(group['driver']); require(driver is not None, 'Cluster driver absent')
        kind = driver.getMaster().getName()
        require(kind in TIES and TIES[kind][1] == group['value'], 'Cluster driver changed constant value')
        output = driver.findITerm(TIES[kind][0]); net = output.getNet()
        require(net is not None and net.getName() == group['net'], 'Cluster output net changed')
        point = term_point(output)
        actual, actual_caps = {}, {}
        for term in net.getITerms():
            if term.getInst().getName() == group['driver']:
                require(term.getMTerm().getName() == TIES[kind][0], 'Unexpected second driver pin')
                continue
            require(str(term.getIoType()) == 'INPUT', 'Cluster has a functional second driver')
            key = ('iterm', term.getInst().getName(), term.getMTerm().getName())
            actual[key] = term_point(term)
            cap_key = (term.getInst().getMaster().getName(), term.getMTerm().getName())
            require(cap_key in contract['input_caps'], 'Written sink absent from actual Liberty')
            actual_caps[key] = contract['input_caps'][cap_key]
        for term in net.getBTerms():
            require(str(term.getIoType()) == 'OUTPUT', 'Cluster shorts a public input')
            actual[('bterm',term.getName())] = bterm_point(term)
            actual_caps[('bterm',term.getName())] = external_load_pf
        expected = {tuple(sink['key']):sink for sink in group['sinks']}
        require(set(actual) == set(expected) and 0 < len(actual) <= max_fanout and
            max_fanout <= contract['max_fanout'], 'Actual cluster sink/fanout inventory differs')
        require(all(expected[key]['capacitance_pf'] == cap for key,cap in actual_caps.items()),
            'Reported sink capacitance differs from actual Liberty')
        cap = sum(actual_caps.values())
        require(cap <= contract['max_capacitance_pf'], 'Actual initial sink-pin load exceeds Liberty')
        distance = max((abs(x-point[0]) + abs(y-point[1])) / unit for x,y in actual.values())
        require(distance <= max_distance_um, 'Actual cluster center-distance bound exceeded')
        maximum = max(maximum, distance)
    return maximum


def transform(odb, db, contract, *, max_fanout, max_distance_um, external_load_pf):
    block = db.getChip().getBlock(); unit = block.getDbUnitsPerMicron()
    before = inventory(block); old_constants, old_ties = constants(block)
    require(max_fanout <= contract['max_fanout'], 'Requested fanout exceeds actual Liberty limit')
    sinks, objects = [], {}
    for net in block.getNets():
        if net.getName() not in old_constants: continue
        value = old_constants[net.getName()]
        for term in net.getITerms():
            if term.getInst().getName() in old_ties: continue
            require(str(term.getIoType()) == 'INPUT', 'Non-input constant sink')
            key = ('iterm', term.getInst().getName(), term.getMTerm().getName())
            point = term_point(term); cap_key = (term.getInst().getMaster().getName(), key[2])
            require(cap_key in contract['input_caps'], 'Sink pin absent from actual Liberty')
            sinks.append(Sink(key, value, *point, contract['input_caps'][cap_key])); objects[key] = term
        for term in net.getBTerms():
            require(str(term.getIoType()) == 'OUTPUT', 'Non-output constant public sink')
            key = ('bterm', term.getName()); point = bterm_point(term)
            sinks.append(Sink(key, value, *point, external_load_pf)); objects[key] = term
    rows = list(block.getRows()); require(rows, 'No physical placement rows')
    rows.sort(key=lambda row: (row.getOrigin()[1], row.getOrigin()[0]))
    supply_nets = {signal:[net for net in block.getNets() if str(net.getSigType()) == signal]
        for signal in POWER}
    require(all(len(nets) == 1 for nets in supply_nets.values()), 'Ambiguous physical supply net')
    created, outputs = [], []
    def anchor(value, number, point):
        name = 'streaming_tt_tie_' + str(int(value)) + '_' + str(number)
        require(block.findInst(name) is None and block.findNet(name) is None, 'Tie-cluster name collision')
        kind = next(kind for kind, (_, bit) in TIES.items() if bit == value)
        master = db.findMaster(kind); require(master is not None, 'Tie master missing from actual database')
        row = min(rows, key=lambda row: abs(row.getOrigin()[1] - point[1]))
        x0, y0 = row.getOrigin(); width = row.getSite().getWidth()
        x = x0 + round((point[0] - x0) / width) * width
        box = row.getBBox(); x = max(box.xMin(), min(x, box.xMax() - master.getWidth()))
        inst = odb.dbInst_create(block, master, name); require(inst is not None, 'Tie creation failed')
        inst.setOrient(row.getOrient()); inst.setLocation(x, y0); inst.setPlacementStatus('PLACED')
        output = inst.findITerm(TIES[kind][0]); require(output is not None, 'New tie output missing')
        for term in inst.getITerms():
            signal = str(term.getMTerm().getSigType())
            if signal in POWER:
                term.connect(supply_nets[signal][0])
        created.append(inst); outputs.append(output)
        return term_point(output)
    groups = cluster(sinks, max_fanout=max_fanout, max_distance=round(max_distance_um*unit),
        max_capacitance_pf=contract['max_capacitance_pf'], anchor=anchor)
    for index, group in enumerate(groups):
        net = odb.dbNet_create(block, created[index].getName()); require(net is not None, 'Tie-net creation failed')
        net.setSigType('SIGNAL'); outputs[index].connect(net)
        for sink in group['sinks']: objects[sink.key].connect(net)
    for name in sorted(old_ties): odb.dbInst_destroy(block.findInst(name))
    # Original now-empty nets may carry DEF metadata; retain rather than guess.
    after = inventory(block); new_constants, new_ties = constants(block)
    verify_transform(before, after, old_constants, new_constants, old_ties, new_ties)
    expected = {s.key for s in sinks}
    require(len(expected) == len(sinks), 'A source sink was counted twice')
    detailed = []
    for index, group in enumerate(groups):
        net = outputs[index].getNet()
        require(len(list(net.getITerms())) + len(list(net.getBTerms())) - 1 == len(group['sinks']),
            'Actual written net has an unexpected sink')
        detailed.append(dict(net=net.getName(), driver=created[index].getName(), value=group['value'],
            output_point_dbu=list(group['point']), fanout=len(group['sinks']),
            max_center_manhattan_distance_um=group['max_distance']/unit,
            sink_pin_capacitance_pf=group['capacitance_pf'],
            sinks=[dict(key=list(s.key), point_dbu=[s.x,s.y], capacitance_pf=s.capacitance_pf) for s in group['sinks']]))
    return dict(before=before, after=after, old_constants=old_constants, new_constants=new_constants,
        old_ties=old_ties, new_ties=new_ties, groups=detailed,
        ff_bits=sum(v['master'] in contract['ff_masters'] for v in before[0].values()))


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--database', required=True); parser.add_argument('--liberty', action='append', required=True)
    parser.add_argument('--out', required=True); parser.add_argument('--max-fanout', type=int, default=8)
    parser.add_argument('--max-distance-um', type=float, default=40)
    parser.add_argument('--external-load-pf', type=float, default=0.010)
    args = parser.parse_args(argv)
    source, out = Path(args.database), Path(args.out)
    require(source.is_file() and not source.is_symlink() and not out.exists(), 'Fresh output and regular source ODB required')
    require(math.isfinite(args.max_distance_um) and 0 < args.max_distance_um <= 100 and
        math.isfinite(args.external_load_pf) and args.external_load_pf >= 0, 'Invalid physical bound')
    input_sha = digest(source); contract = tie_contract(args.liberty)
    require(len(contract['liberty_sha256']) == 3 and set(contract['liberty_sha256'].values()) == CORNERS_SHA256,
        'All three pinned CMOS5L1.2V Liberty corners are required')
    import odb
    db = odb.dbDatabase.create(); odb.read_db(db, str(source))
    result = transform(odb, db, contract, max_fanout=args.max_fanout,
        max_distance_um=args.max_distance_um, external_load_pf=args.external_load_pf)
    out.mkdir(parents=True, exist_ok=False); target = out/'clustered.odb'; odb.write_db(db, str(target))
    check = odb.dbDatabase.create(); odb.read_db(check, str(target)); block = check.getChip().getBlock()
    readback = inventory(block); constants_after, ties_after = constants(block)
    require(readback == result['after'] and constants_after == result['new_constants'] and ties_after == result['new_ties'],
        'Native written ODB readback differs')
    verify_transform(result['before'], readback, result['old_constants'], constants_after, result['old_ties'], ties_after)
    actual_distance = verify_groups(block, result['groups'], contract, args.max_fanout,
        args.max_distance_um, args.external_load_pf)
    require(digest(source) == input_sha and all(digest(path) == value for path,value in contract['liberty_sha256'].items()),
        'Source ODB or Liberty changed during transformation')
    receipt = dict(schema='pinwheel.streaming-tt-tie-clustering.v1', qualified=False,
        source_odb=str(source), source_odb_sha256=input_sha, clustered_odb_sha256=digest(target),
        source_sha256=digest(__file__), liberty_sha256=contract['liberty_sha256'],
        old_ties=len(result['old_ties']), new_ties=len(result['new_ties']), sink_count=sum(g['fanout'] for g in result['groups']),
        max_fanout=args.max_fanout, max_center_manhattan_distance_um=args.max_distance_um,
        actual_max_center_manhattan_distance_um=actual_distance,
        max_sink_pin_capacitance_pf=contract['max_capacitance_pf'], ff_bits=result['ff_bits'],
        non_tie_instances_and_locations_unchanged=True, all_logical_pins_preserved_modulo_literal_constants=True,
        native_odb_readback_checked=True, input_unchanged=True, groups=result['groups'],
        boundary='Literal-constant regrouping only. Distance is initial pin-center Manhattan distance. Wire capacitance is excluded from the initial pin-load check. Legalization and routing may move cells; final routed fanout/capacitance/slew, physical distance, power connectivity, post-PNR kernel proof and official precheck remain required.')
    (out/'report.json').write_text(json.dumps(receipt, indent=2, sort_keys=True)+'\n')
    print(json.dumps({k:v for k,v in receipt.items() if k != 'groups'}, sort_keys=True))


if __name__ == '__main__': main()
