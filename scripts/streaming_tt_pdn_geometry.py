"""Exact host admission for the TT Metal4 power grid and fixed public pins.

This checks proposed geometry before CAD.  It does not establish generated
geometry, rail connectivity, DRC, LVS, IR drop, or tapeout acceptance.
"""
from dataclasses import dataclass
import hashlib
from pathlib import Path
import re


TEMPLATE_SHA256 = 'b46d9a0ee8352160e48dbc8312f092f985629061df736c7f46d58686535a76f4'
DIE = (0, 0, 1289280, 710640)
DBU_PER_MICRON = 1000
CORE_X_MIN = 2880
M4_MIN_SPACING_DBU = 240  # Conservative entry for a 2.1 um stripe in pinned M4 LEF.
OFFICIAL_POWER_MIN_WIDTH_DBU = 2100
OFFICIAL_POWER_EDGE_DISTANCE_DBU = 10000


def require(value, message):
    if not value:
        raise ValueError(message)


def official_pin_centers():
    result = {'clk': 187200, 'ena': 191040, 'rst_n': 183360}
    for prefix, first in [('ui_in', 179520), ('uio_in', 148800), ('uio_oe', 56640),
                          ('uio_out', 87360), ('uo_out', 118080)]:
        result.update({f'{prefix}[{k}]': first - 3840 * k for k in range(8)})
    return result


def template_pins(text):
    """Parse only the admitted one-rectangle, north-facing official DEF grammar."""
    require(re.findall(r'UNITS DISTANCE MICRONS (\d+) ;', text) == ['1000'], 'Wrong template DBU scale')
    dies = re.findall(r'DIEAREA \( (-?\d+) (-?\d+) \) \( (-?\d+) (-?\d+) \) ;', text)
    require(len(dies) == 1 and tuple(map(int, dies[0])) == DIE, 'Wrong official die geometry')
    sections = re.findall(r'(?ms)^PINS (\d+) ;\s*(.*?)^END PINS\s*$', text)
    require(len(sections) == 1 and sections[0][0] == '43', 'Wrong public-pin section')
    records = re.findall(r'(?ms)^\s*-\s+(\S+)(.*?)(?=^\s*-\s+|\Z)', sections[0][1])
    require(len(records) == 43, 'Incomplete public-pin records')
    grammar = (r'\s*\+ NET (\S+) \+ DIRECTION (INPUT|OUTPUT) \+ USE SIGNAL\s*'
               r'\+ PORT\s*\+ LAYER (\S+) \( (-?\d+) (-?\d+) \) \( (-?\d+) (-?\d+) \)\s*'
               r'\+ PLACED \( (-?\d+) (-?\d+) \) (\S+) ;\s*')
    expected = official_pin_centers()
    result = {}
    for name, body in records:
        match = re.fullmatch(grammar, body)
        require(match is not None and name in expected and name not in result, 'Unsupported public-pin record: ' + name)
        net, direction, layer, *values, orient = match.groups()
        lx, by, rx, ty, ox, oy = map(int, values)
        rectangle = (lx + ox, by + oy, rx + ox, ty + oy)
        expected_direction = 'INPUT' if name in ('clk', 'ena', 'rst_n') or name.startswith(('ui_in[', 'uio_in[')) else 'OUTPUT'
        require(net == name and direction == expected_direction and layer == 'Metal4' and orient == 'N' and
                rectangle == (expected[name] - 150, 709640, expected[name] + 150, 710640),
                'Changed official public-pin geometry: ' + name)
        result[name] = rectangle
    require(result.keys() == expected.keys(), 'Missing public pins')
    return result


@dataclass(frozen=True)
class Grid:
    width: int
    pitch: int
    first_center: int
    pair_delta: int
    public_clearance: int

    @classmethod
    def from_tcl(cls, text):
        fields = {}
        for field in ('m4_width', 'm4_pitch', 'm4_first_center', 'm4_pair_delta', 'public_clearance'):
            matches = re.findall(r'^set streaming_pdn_' + field + r'_dbu ([0-9]+)\s*$', text, re.M)
            require(len(matches) == 1, 'Missing/duplicate PDN integer parameter: ' + field)
            fields[field] = int(matches[0])
        return cls(*(fields[name] for name in ('m4_width', 'm4_pitch', 'm4_first_center', 'm4_pair_delta', 'public_clearance')))

    def rectangles(self):
        require(all(type(value) is int and value > 0 for value in self.__dict__.values()), 'Nonpositive/noninteger PDN geometry')
        require(self.width % 2 == 0 and self.width >= OFFICIAL_POWER_MIN_WIDTH_DBU, 'Power stripe is too narrow or half-DBU')
        require(self.public_clearance >= M4_MIN_SPACING_DBU, 'Public clearance is below conservative pinned M4 spacing')
        require(self.pair_delta - self.width >= M4_MIN_SPACING_DBU and
                self.pitch - self.pair_delta - self.width >= M4_MIN_SPACING_DBU, 'Power/ground stripes lack spacing')
        require(self.first_center - self.width // 2 >= CORE_X_MIN, 'First power stripe lies outside the admitted core')
        rows = []
        first = self.first_center
        while first + self.pair_delta + self.width // 2 <= DIE[2]:
            for net, x in [('VPWR', first), ('VGND', first + self.pair_delta)]:
                rows.append(dict(net=net, layer='Metal4', bounds_dbu=[x - self.width // 2, 0, x + self.width // 2, DIE[3]]))
            first += self.pitch
        require(len(rows) >= 2, 'No complete power/ground stripe pair fits')
        return rows


def clearance(left, right):
    """Signed axis gap. Overlap and abutment yield <=0 for these full-height strips."""
    return max(right[0] - left[2], left[0] - right[2], right[1] - left[3], left[1] - right[3])


def admit_geometry(pins, grid):
    require(pins.keys() == official_pin_centers().keys(), 'Admission requires all43 public pins')
    stripes = grid.rectangles()
    distances = [(clearance(stripe['bounds_dbu'], rectangle), name, stripe['net'], stripe['bounds_dbu'])
                 for stripe in stripes for name, rectangle in pins.items()]
    minimum, name, net, rectangle = min(distances)
    require(minimum >= grid.public_clearance,
            f'Public pin {name} violates {net} power-strap clearance: {minimum} < {grid.public_clearance} DBU')
    return dict(schema='pinwheel.streaming-tt-pdn-geometry-admission.v1',
                proposed_geometry_admitted=True, native_geometry_validated=False, qualified=False,
                physical_acceptance=False, dbu_per_micron=DBU_PER_MICRON,
                public_pin_count=len(pins), expected_power_stripe_count=len(stripes),
                grid_dbu=grid.__dict__, minimum_public_clearance_dbu=minimum,
                conservative_pinned_m4_spacing_dbu=M4_MIN_SPACING_DBU,
                closest_pair=dict(public_pin=name, power_net=net, power_rectangle_dbu=rectangle),
                expected_power_ports=stripes)


def admit(template, pdn):
    template, pdn = Path(template), Path(pdn)
    require(template.is_file() and not template.is_symlink() and pdn.is_file() and not pdn.is_symlink(), 'Missing/aliased PDN input')
    template_bytes, pdn_bytes = template.read_bytes(), pdn.read_bytes()
    template_sha = hashlib.sha256(template_bytes).hexdigest()
    require(template_sha == TEMPLATE_SHA256, 'Official pin template bytes changed')
    result = admit_geometry(template_pins(template_bytes.decode()), Grid.from_tcl(pdn_bytes.decode()))
    result.update(template_sha256=template_sha, pdn_sha256=hashlib.sha256(pdn_bytes).hexdigest())
    return result


def validate_power_ports(rows, grid):
    """Strict readback admission; accepts redundant endcaps only inside full straps.

    Native PDN writes full-stripe ports and redundant endcap rectangles. Requiring
    each full rectangle explicitly avoids claiming a rectangular union when only
    disjoint endcaps are present. The official checker still runs independently.
    """
    expected = grid.rectangles()
    seen = set()
    require(type(rows) is list and rows, 'Missing actual power-port geometry')
    for row in rows:
        require(type(row) is dict and set(row) == {'net', 'layer', 'bounds_dbu'}, 'Invalid power-port row schema')
        rectangle = row['bounds_dbu']
        require(type(rectangle) in (list, tuple) and len(rectangle) == 4 and all(type(x) is int for x in rectangle) and
                rectangle[0] < rectangle[2] and rectangle[1] < rectangle[3], 'Invalid power-port rectangle')
        matches = [stripe for stripe in expected if row['net'] == stripe['net'] and row['layer'] == stripe['layer'] and
                   stripe['bounds_dbu'][0] <= rectangle[0] < rectangle[2] <= stripe['bounds_dbu'][2] and
                   stripe['bounds_dbu'][1] <= rectangle[1] < rectangle[3] <= stripe['bounds_dbu'][3]]
        require(len(matches) == 1, 'Unexpected power-port layer, net, or geometry')
        if list(rectangle) == matches[0]['bounds_dbu']:
            seen.add((row['net'], tuple(rectangle)))
    require(seen == {(row['net'], tuple(row['bounds_dbu'])) for row in expected}, 'Missing full-height power-port rectangle')
    return dict(power_port_geometry_matches_admitted_grid=True, full_height_power_stripes=len(seen),
                qualified=False, physical_acceptance=False)
