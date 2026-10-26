"""Exact, separately scoped official 8x4 allocation and power-grid admission.

Only the hash-bound official DEF supplies pin positions. HOST admission is not
generated geometry, routing, connectivity, DRC, LVS or power qualification.
"""
from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
ALLOCATION = ROOT / 'physical/streaming_8x4/allocation.json'
DIE = (0, 0, 1724160, 710640)
CORE = (2880, 3780, 1721280, 706860)
DBU = 1000
MIN_SPACING = 240


def require(value, message):
    if not value:
        raise ValueError(message)


def sha(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def regular(path):
    path = Path(path).absolute()
    require(path.is_file() and not path.is_symlink(), 'Missing/aliased 8x4 input: ' + str(path))
    return path


def public_names():
    return {'clk', 'ena', 'rst_n'} | {f'{prefix}[{index}]' for prefix in
        ('ui_in', 'uio_in', 'uio_oe', 'uio_out', 'uo_out') for index in range(8)}


def template_pins(text):
    require(re.findall(r'UNITS DISTANCE MICRONS (\d+) ;', text) == ['1000'], 'Wrong official 8x4 DBU scale')
    dies = re.findall(r'DIEAREA \( (-?\d+) (-?\d+) \) \( (-?\d+) (-?\d+) \) ;', text)
    require(len(dies) == 1 and tuple(map(int, dies[0])) == DIE, 'Wrong official 8x4 die')
    rows=re.findall(r'^ROW ROW_(\d+) CoreSite (\d+) (\d+) (N|FS) DO (\d+) BY 1 STEP (\d+) 0 ;$',text,re.M)
    require(len(rows)==186 and all(tuple((int(index),int(x),int(y),orientation,int(count),int(step))) ==
            (k,CORE[0],CORE[1]+k*3780,'N' if k%2==0 else 'FS',3580,480)
            for k,(index,x,y,orientation,count,step) in enumerate(rows)), 'Wrong official8x4 row/core geometry')
    sections = re.findall(r'(?ms)^PINS (\d+) ;\s*(.*?)^END PINS\s*$', text)
    require(len(sections) == 1 and sections[0][0] == '43', 'Wrong official 8x4 pin section')
    records = re.findall(r'(?ms)^\s*-\s+(\S+)(.*?)(?=^\s*-\s+|\Z)', sections[0][1])
    require(len(records) == 43, 'Incomplete official 8x4 pin records')
    grammar = (r'\s*\+ NET (\S+) \+ DIRECTION (INPUT|OUTPUT) \+ USE SIGNAL\s*'
               r'\+ PORT\s*\+ LAYER (\S+) \( (-?\d+) (-?\d+) \) \( (-?\d+) (-?\d+) \)\s*'
               r'\+ PLACED \( (-?\d+) (-?\d+) \) (\S+) ;\s*')
    pins = {}
    for name, body in records:
        match = re.fullmatch(grammar, body)
        require(match is not None and name in public_names() and name not in pins,
                'Unsupported official 8x4 public pin: ' + name)
        net, direction, layer, *values, orient = match.groups()
        lx, by, rx, ty, ox, oy = map(int, values)
        bounds = (lx + ox, by + oy, rx + ox, ty + oy)
        expected_direction = 'INPUT' if name in {'clk', 'ena', 'rst_n'} or name.startswith(('ui_in[', 'uio_in[')) else 'OUTPUT'
        require(net == name and direction == expected_direction and layer == 'Metal4' and orient == 'N' and
                bounds[2] - bounds[0] == 300 and bounds[1] == DIE[3] - 1000 and bounds[3] == DIE[3] and
                0 <= bounds[0] < bounds[2] <= DIE[2], 'Changed official 8x4 pin shape: ' + name)
        pins[name] = bounds
    require(set(pins) == public_names(), 'Missing official 8x4 public pins')
    return pins


@dataclass(frozen=True)
class Grid:
    width: int = 2100
    pitch: int = 49880
    first_center: int = 16400
    pair_delta: int = 7680
    public_clearance: int = 600

    def rectangles(self):
        require(all(type(value) is int and value > 0 for value in self.__dict__.values()), 'Invalid 8x4 grid integer')
        require(self.width % 2 == 0 and self.width >= 2100 and self.public_clearance >= MIN_SPACING,
                '8x4 grid width/clearance below admitted limits')
        require(self.pair_delta - self.width >= MIN_SPACING and self.pitch - self.pair_delta - self.width >= MIN_SPACING,
                '8x4 power stripes lack spacing')
        require(self.first_center - self.width // 2 >= 2880, '8x4 power stripe lies outside core')
        rows = []
        first = self.first_center
        while first + self.pair_delta + self.width // 2 <= DIE[2]:
            for net, center in [('VPWR', first), ('VGND', first + self.pair_delta)]:
                rows.append(dict(net=net, layer='Metal4', bounds_dbu=[center - self.width // 2, 0, center + self.width // 2, DIE[3]]))
            first += self.pitch
        require(rows, 'Empty 8x4 power grid')
        require(rows[-1]['bounds_dbu'][2] <= CORE[2], 'Last complete8x4 power stripe exceeds core')
        require(first - self.width // 2 >= DIE[2], 'Incomplete boundary power-stripe pair would fit8x4 die')
        return rows


def clearance(left, right):
    return max(right[0] - left[2], left[0] - right[2], right[1] - left[3], left[1] - right[3])


def admit(template, allocation=ALLOCATION, grid=Grid()):
    template, allocation = regular(template), regular(allocation)
    manifest = json.loads(allocation.read_text())
    require(manifest.get('schema') == 'pinwheel.streaming-8x4-allocation.v1' and
            manifest.get('tiles') == '8x4' and manifest.get('die_dbu') == list(DIE) and
            manifest.get('dbu_per_micron') == DBU and manifest.get('public_pin_count') == 43 and
            manifest.get('core_dbu') == list(CORE) and
            type(manifest.get('support_commit')) is str and re.fullmatch('[0-9a-f]{40}', manifest['support_commit']) and
            sha(template) == manifest.get('template_sha256'), 'Official 8x4 allocation identity differs')
    pins = template_pins(template.read_text())
    rows = grid.rectangles()
    minimum = min(clearance(row['bounds_dbu'], pin) for row in rows for pin in pins.values())
    require(minimum >= grid.public_clearance, '8x4 PDN collides with fixed official public pins')
    return dict(schema='pinwheel.streaming-8x4-geometry-admission.v1', tiles='8x4', die_dbu=list(DIE),core_dbu=list(CORE),
        allocation_sha256=sha(allocation), template_sha256=sha(template), public_pins_dbu={name:list(pin) for name,pin in sorted(pins.items())},
        grid_dbu=grid.__dict__, expected_power_ports=rows, minimum_public_clearance_dbu=minimum,
        proposed_geometry_admitted=True, native_geometry_validated=False, qualified=False, physical_acceptance=False)


def allocation_tcl(admission):
    require(admission.get('schema') == 'pinwheel.streaming-8x4-geometry-admission.v1' and
            admission.get('die_dbu') == list(DIE), 'Wrong 8x4 geometry admission')
    lines = ['# Generated only from the hash-bound official 8x4 DEF; do not edit.',
             'set streaming8_die {0 0 1724160 710640}', 'set streaming8_core_bounds {2880 3780 1721280 706860}',
             'set streaming8_pins [dict create]']
    for name, bounds in sorted(admission['public_pins_dbu'].items()):
        require(name in public_names() and len(bounds) == 4 and all(type(value) is int for value in bounds), 'Invalid 8x4 Tcl pin')
        lines.append('dict set streaming8_pins {' + name + '} {' + ' '.join(map(str, bounds)) + '}')
    for key,value in admission['grid_dbu'].items():
        require(key in Grid().__dict__ and type(value) is int, 'Invalid 8x4 Tcl grid')
        lines.append('set streaming8_' + key + ' ' + str(value))
    return '\n'.join(lines) + '\n'


def validate_power_ports(rows, grid=Grid()):
    expected = grid.rectangles()
    seen = set()
    require(type(rows) is list and rows, 'Missing generated 8x4 power ports')
    for row in rows:
        require(type(row) is dict and set(row) == {'net', 'layer', 'bounds_dbu'}, 'Invalid 8x4 power-port record')
        box = row['bounds_dbu']
        require(type(box) in (list, tuple) and len(box) == 4 and all(type(value) is int for value in box) and
                box[0] < box[2] and box[1] < box[3], 'Invalid generated 8x4 power box')
        matches = [stripe for stripe in expected if stripe['net'] == row['net'] and stripe['layer'] == row['layer'] and
                   stripe['bounds_dbu'][0] <= box[0] < box[2] <= stripe['bounds_dbu'][2] and
                   stripe['bounds_dbu'][1] <= box[1] < box[3] <= stripe['bounds_dbu'][3]]
        require(len(matches) == 1, 'Unexpected generated 8x4 power-port geometry')
        if list(box) == matches[0]['bounds_dbu']:
            seen.add((row['net'], tuple(box)))
    require(seen == {(row['net'], tuple(row['bounds_dbu'])) for row in expected}, 'Missing full-height 8x4 power stripe')
    return dict(power_port_geometry_matches_admitted_grid=True, full_height_power_stripes=len(seen),
                qualified=False, physical_acceptance=False)
