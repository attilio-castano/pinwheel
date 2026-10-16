"""Exact local input and geometry checks for the buffered Tiny Tapeout candidate."""
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
MASTER = 'RM_IHPSG13_1P_64x64_c2_bm_bist'
TOP = 'tt_um_pinwheel_buffered'
PLACEMENTS = {
    'engine.memory.storage0': {'location': [252, 30], 'orientation': 'N'},
    'engine.memory.storage1': {'location': [252, 144], 'orientation': 'N'},
}


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def blob(data):
    return hashlib.sha1(f'blob {len(data)}\0'.encode() + data).hexdigest()


def read(path):
    return json.loads(Path(path).read_text())


def write(path, value):
    Path(path).write_text(json.dumps(value, indent=2) + '\n')


def validate_flow_config(config):
    meta=config.get('meta',{})
    power_only = {'+OpenROAD.GeneratePDN':'Project.BufferedSramPower'}
    capacity_placement = {**power_only, 'OpenROAD.GlobalPlacement':'Project.BufferedCapacityPlacement'}
    if meta.get('flow') != 'Classic' or meta.get('substituting_steps') not in (power_only, capacity_placement):
        raise ValueError('Explicit Classic flow and exact buffered SRAM power step are required')
    if not config.get('PDN_CONNECT_MACROS_TO_GRID',False):
        raise ValueError('Explicit SRAM supply hooks require PDN_CONNECT_MACROS_TO_GRID=true')
    if config['PDN_MULTILAYER'] or config['RT_MAX_LAYER'] != 'Metal4' or not config['RUN_KLAYOUT_DRC'] or not config['RUN_MAGIC_DRC']:
        raise ValueError('Changed metal/check boundary')


def supply_geometry(lef):
    """Read every Metal4 supply column, including the irregular centre band."""
    text = Path(lef).read_text()
    size = re.search(r'\bSIZE\s+([\d.]+)\s+BY\s+([\d.]+)\s*;', text)
    if not size:
        raise ValueError('Missing SRAM size')
    geometry = dict(size_um=list(map(float, size.groups())), pins={})
    for name in ('VDD!', 'VDDARRAY!', 'VSS!'):
        match = re.search(r'^\s*PIN\s+' + re.escape(name) + r'\s*\n(.*?)^\s*END\s+' + re.escape(name) + r'\s*$', text, re.M | re.S)
        if not match:
            raise ValueError('Missing SRAM power pin: ' + name)
        layer, rectangles = None, []
        for line in match.group(1).splitlines():
            found = re.search(r'\bLAYER\s+(\S+)\s*;', line)
            if found:
                layer = found.group(1)
            found = re.search(r'\bRECT\s+([\d.]+)\s+([\d.]+)\s+([\d.]+)\s+([\d.]+)\s*;', line)
            if found and layer == 'Metal4':
                rectangles.append(list(map(float, found.groups())))
        if not rectangles:
            raise ValueError('No Metal4 geometry for SRAM supply: ' + name)
        geometry['pins'][name] = rectangles
    return geometry


def template_signal_columns(template):
    text = Path(template).read_text()
    units = int(re.search(r'UNITS DISTANCE MICRONS (\d+) ;', text).group(1))
    entries = text.split('PINS 43 ;', 1)[1].split('END PINS', 1)[0]
    columns = []
    for entry in entries.split('    - ')[1:]:
        rectangle = re.search(r'LAYER Metal4 \( (-?\d+) (-?\d+) \) \( (-?\d+) (-?\d+) \)', entry)
        position = re.search(r'PLACED \( (\d+) (\d+) \) N', entry)
        if not rectangle or not position or '+ USE SIGNAL' not in entry:
            raise ValueError('Unrecognized official template pin geometry')
        a, _, b, _ = map(int, rectangle.groups())
        x = int(position.group(1))
        columns.append([(x+a)/units, (x+b)/units])
    if len(columns) != 43:
        raise ValueError('Expected all 43 official template signal pins')
    return columns


def column_plan(geometry, signal_columns, *, width=2.1, clearance=0.24):
    """Select direct-contact full-height stripes, rejecting signal-pin collisions."""
    if width <= 0 or clearance < 0:
        raise ValueError('Invalid stripe dimensions')
    x = PLACEMENTS['engine.memory.storage0']['location'][0]
    plan = dict(width_um=width, clearance_um=clearance, nets={}, skipped={},
                boundary='Geometry proposal only; actual OpenDB connectivity, DRC and power analysis remain required.')
    for net, pins in {'VPWR': ('VDD!', 'VDDARRAY!'), 'VGND': ('VSS!',)}.items():
        columns = sorted({(r[0], r[2]) for pin in pins for r in geometry['pins'][pin]})
        accepted, skipped = [], []
        for a, b in columns:
            if b-a < width:
                raise ValueError('Supply column narrower than selected stripe')
            centre = x+(a+b)/2
            stripe = [round(centre-width/2, 6), round(centre+width/2, 6)]
            if any(stripe[1]+clearance > sa and stripe[0]-clearance < sb for sa, sb in signal_columns):
                skipped.append(stripe)
            else:
                accepted.append(stripe)
        if len(accepted) < 2:
            raise ValueError('Insufficient clear power columns')
        plan['nets'][net], plan['skipped'][net] = accepted, skipped
    for a in plan['nets']['VPWR']:
        for b in plan['nets']['VGND']:
            if a[1]+clearance > b[0] and a[0]-clearance < b[1]:
                raise ValueError('Supply stripe collision')
    for pin, rectangles in geometry['pins'].items():
        net = 'VGND' if pin == 'VSS!' else 'VPWR'
        contacts = sum(any(x+r[0] <= a and b <= x+r[2] for r in rectangles) for a, b in plan['nets'][net])
        if contacts < 2:
            raise ValueError('Supply pin has too few clear direct contacts: ' + pin)
    return plan


def verify_prepared(design):
    design = Path(design).resolve()
    receipt = read(design/'inputs.json')
    if receipt.get('schema') != 'pinwheel-buffered-tt-physical-input-v1':
        raise ValueError('Not a prepared buffered Tiny Tapeout input')
    for relative, digest in receipt['files_sha256'].items():
        path = (design/relative).resolve()
        if not path.is_relative_to(design) or sha(path) != digest:
            raise ValueError('Changed staged input: ' + relative)
    for relative, digest in receipt['source_sha256'].items():
        if sha(ROOT/relative) != digest:
            raise ValueError('Changed preparation source: ' + relative)
    validation = Path(receipt['validation_receipt'])
    if sha(validation) != receipt['validation_receipt_sha256'] or read(validation).get('status') != 'passed':
        raise ValueError('Changed or failed wrapper validation')
    return receipt
