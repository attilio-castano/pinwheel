"""Pinned OpenROAD readback and view export. No edit/repair/routing commands."""
import json
from pathlib import Path
import re
from openroad import Tech, Design
from audits import sha, write, def_routing_layers
from native_inventory import snapshot

R = Path('/work/diagnostic')
request = json.loads((R / 'prepared.json').read_text())
assert sha('/proc/self/exe') == request['native_binary_sha256']
# OpenROAD Design keeps a native Tech pointer; retain the Python owner for the whole export.
tech = Tech()
design = Design(tech)
design.readDb(str(R / 'input/checkpoint.odb'))
block = design.getBlock()
assert block is not None
(R / 'export').mkdir()
before = snapshot(design.getDb(), block, 'export/before')
assert before == json.loads((R / 'input/inventory.json').read_text()), 'Input ODB/full native inventory mismatch'


def masters_snapshot():
    result = {}
    for inst in block.getInsts():
        master = inst.getMaster()
        name = master.getName()
        if name in result:
            continue
        obs = sorted([box.getTechLayer().getName(), [box.xMin(), box.yMin(), box.xMax(), box.yMax()]]
            for box in master.getObstructions() if box.getTechLayer() is not None)
        terms = []
        for term in master.getMTerms():
            shapes = sorted([box.getTechLayer().getName(), [box.xMin(), box.yMin(), box.xMax(), box.yMax()]]
                for pin in term.getMPins() for box in pin.getGeometry() if box.getTechLayer() is not None)
            terms.append([term.getName(), str(term.getIoType()), str(term.getSigType()), shapes])
        result[name] = {'width': master.getWidth(), 'height': master.getHeight(), 'type': str(master.getType()),
                        'origin': list(master.getOrigin()), 'obstructions': obs, 'terminals': sorted(terms)}
    return result


def vias_snapshot():
    result = {}
    for scope, obj in [('tech', design.getDb().getTech()), ('block', block)]:
        for via in obj.getVias():
            result[scope + '/' + via.getName()] = sorted([box.getTechLayer().getName(), box.getTechLayer().getRoutingLevel(),
                [box.xMin(), box.yMin(), box.xMax(), box.yMax()]] for box in via.getBoxes() if box.getTechLayer() is not None)
    return result


assert masters_snapshot() == json.loads((R / 'input/master-OBS.json').read_text()), 'Master pins/OBS differ'
assert vias_snapshot() == json.loads((R / 'input/vias.json').read_text()), 'Via definitions differ'
for command in ('write_verilog /work/diagnostic/export/netlist.v',
                'write_verilog -include_pwr_gnd /work/diagnostic/export/powered.v',
                'write_def /work/diagnostic/export/checkpoint.def'):
    result = design.evalTclString('if {[catch {' + command + '} message]} {error $message}')
after = snapshot(design.getDb(), block, 'export/after')
assert before == after, 'View export changed frozen inventory'
assert masters_snapshot() == json.loads((R / 'input/master-OBS.json').read_text())
assert vias_snapshot() == json.loads((R / 'input/vias.json').read_text())


def tokens(text):
    text = re.sub(r'(?m)^\s*#.*$', '', text)
    return re.findall(r'"[^"\n]*"|\\\S+|[();+]|[^\s();+]+', text)


original = tokens((R / 'input/checkpoint.def').read_text())
exported = tokens((R / 'export/checkpoint.def').read_text())
exact = original == exported
write(R / 'export/scope.json', {'status': 'passed' if exact else 'failed',
    'full_native_inventory_exact': True, 'master_pins_OBS_exact': True, 'via_definitions_exact': True,
    'DEF_tokens_including_TAPER_exact': exact,
    'first_DEF_token_difference': next((i for i, (a, b) in enumerate(zip(original, exported)) if a != b),
                                     None if len(original) == len(exported) else min(len(original), len(exported))),
    'source_ODB_sha256': sha(R / 'input/checkpoint.odb'), 'source_DEF_sha256': sha(R / 'input/checkpoint.def'),
    'netlist_sha256': sha(R / 'export/netlist.v'), 'powered_netlist_sha256': sha(R / 'export/powered.v'),
    'native_binary_sha256': sha('/proc/self/exe'),
    'used_routing_layers': def_routing_layers((R / 'input/checkpoint.def').read_text()),
    'technology_routing_levels': [[layer.getName(), layer.getRoutingLevel()] for layer in design.getDb().getTech().getLayers() if layer.getRoutingLevel()],
    'cell_or_route_edit_commands': [], 'physical_connectivity_proven': False})
assert exact, 'Input DEF is not a token-exact same-ODB native export, including per-path routing rules'
