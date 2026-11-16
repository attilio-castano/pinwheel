"""Join frozen PSM via currents to the candidate's DEF arrays and GDS cuts."""

import bisect
from collections import Counter, defaultdict
from decimal import Decimal, ROUND_CEILING
import itertools
import json
import math
from pathlib import Path
import re

from streaming_8x4_draft_rc_timing import bound
from streaming_8x4_e982_native import TOP, read, require, sha
from streaming_8x4_hold_cap_ir_readback import DBU, PROCESS_SPEC, VIA, csv_rows, node
from streaming_8x4_hold_cap_physical import TARGET, TRIAL


DEF_SHA = "0ebc4418da924037d2c9cb5beeff5a7d9c830b5ca8091a5cdf1616b790475962"
DC_SHA = "d1bb974807b3caf1e1daa85cbddd314e06dede45980074f6d8c932d03c8de7e9"
RAILS = ("VPWR", "VGND")
VIA_LAYERS = {"Via1": 19, "Via2": 29, "Via3": 49}
LIMIT_MA = Decimal("0.4")
CUT_RESISTANCE_OHM = 20


def parse_def(path):
    definition = re.compile(
        r"\s*- (\w+) \+ VIARULE (\w+) \+ CUTSIZE (\d+) (\d+)\s+"
        r"\+ LAYERS (Metal[1-4]) (Via[1-3]) (Metal[1-4])\s+"
        r"\+ CUTSPACING (\d+) (\d+)\s+\+ ENCLOSURE (?:\d+ ){3}\d+\s+"
        r"\+ ROWCOL (\d+) (\d+)\s+;\s*"
    )
    placement = re.compile(r"\s*(?:\+ ROUTED|NEW) (Metal[1-3]) 0 \+ SHAPE STRIPE "
                           r"\( (-?\d+) (-?\d+) \) (\w+)\s*;?\s*")
    families, arrays = {}, defaultdict(dict)
    section, rail, unit_seen = None, None, False
    with path.open() as stream:
        for line in stream:
            if line.startswith("UNITS DISTANCE MICRONS "):
                require(line.strip() == f"UNITS DISTANCE MICRONS {DBU} ;" and not unit_seen,
                        "Wrong DEF units")
                unit_seen = True
            if line.startswith("VIAS "):
                require(line.strip() == "VIAS 3 ;", "Unexpected generated-via census")
                section = "VIAS"
                continue
            if line.startswith("SPECIALNETS "):
                require(line.strip() == "SPECIALNETS 2 ;", "Unexpected special-net census")
                section = "SPECIALNETS"
                continue
            if line.strip() == "END VIAS":
                section = None
                continue
            if line.strip() == "END SPECIALNETS":
                break
            if section == "VIAS":
                match = definition.fullmatch(line)
                require(match is not None, "Unexpected generated via definition")
                name, rule, wx, wy, lower, cut, upper, gx, gy, rows, cols = match.groups()
                wx, wy, gx, gy, rows, cols = map(int, (wx, wy, gx, gy, rows, cols))
                require(name not in families and VIA[lower, upper] == (cut, rows * cols)
                        and rule == f"{cut.lower()}Array" and (wx, wy) == (190, 190), "Wrong via family")
                offsets_x = [(2 * j + 1 - cols) * (wx + gx) // 2 for j in range(cols)]
                offsets_y = [(2 * j + 1 - rows) * (wy + gy) // 2 for j in range(rows)]
                boxes = {(x - wx // 2, y - wy // 2, x + wx // 2, y + wy // 2)
                         for x, y in itertools.product(offsets_x, offsets_y)}
                families[name] = dict(layers=(lower, upper), cut=cut, boxes=boxes, cuts=rows * cols)
            if section == "SPECIALNETS":
                if re.match(r"\s*- ", line):
                    rail = line.split()[1]
                    require(rail in RAILS, "Unexpected special net")
                if not re.search(r"\bMetal\d+ 0 \+ SHAPE STRIPE", line):
                    continue
                match = placement.fullmatch(line)
                require(match is not None and rail in RAILS, "Unexpected rail via placement")
                lower, x, y, family = match.groups()
                center = int(x), int(y)
                require(families[family]["layers"][0] == lower and center not in arrays[rail, family],
                        "Repeated or mismatched rail via placement")
                arrays[rail, family][center] = True
    require(unit_seen and len(families) == 3 and set(arrays) == set(itertools.product(RAILS, families)),
            "Incomplete rail via geometry")
    require({rail: sum(len(points) for (actual, _name), points in arrays.items() if rail == actual)
             for rail in RAILS} == {"VPWR": 4235, "VGND": 4270}, "Unexpected physical array count")
    return families, {key: set(points) for key, points in arrays.items()}


def dbu(value):
    result = round(value * DBU)
    require(math.isclose(value * DBU, result, rel_tol=0, abs_tol=1e-6), "Non-grid coordinate")
    return result


def gds_arrays(path, families, arrays):
    import gdstk

    require(gdstk.__version__ == "0.9.52", "Use the retained gdstk 0.9.52 reader")
    library = gdstk.read_gds(path)
    require(library.unit == 1e-6 and library.precision == 1e-9, "Wrong GDS units")
    top, = library.top_level()
    require(top.name == TOP, "Wrong GDS top")
    cells = {cell.name: cell for cell in library.cells}
    names = {"VIA_" + name: name for name in families}
    locations = defaultdict(set)
    for reference in top.references:
        if reference.cell_name in names:
            name = names[reference.cell_name]
            center = tuple(dbu(x) for x in reference.origin)
            require(reference.rotation == 0 and not reference.x_reflection and reference.magnification == 1
                    and reference.repetition.size == 0 and center not in locations[name], "Unexpected GDS via reference")
            locations[name].add(center)
    for cell_name, name in names.items():
        family = families[name]
        cell = cells[cell_name]
        polygons = [polygon for polygon in cell.polygons if polygon.layer in VIA_LAYERS.values()]
        require(len(polygons) == family["cuts"] and not cell.paths and not cell.references,
                "Incomplete or nested GDS via cut geometry")
        boxes = set()
        for polygon in polygons:
            points = [(dbu(x), dbu(y)) for x, y in polygon.points]
            views = sorted(set(x for x, _ in points)), sorted(set(y for _, y in points))
            require((polygon.layer, polygon.datatype) == (VIA_LAYERS[family["cut"]], 0)
                    and len(points) == 4 and all(len(axis) == 2 for axis in views)
                    and set(points) == set(itertools.product(*views)), "Unexpected GDS cut rectangle")
            (x0, x1), (y0, y1) = views
            boxes.add((x0, y0, x1, y1))
        require(boxes == family["boxes"] and locations[name] == arrays["VPWR", name] | arrays["VGND", name]
                and not (arrays["VPWR", name] & arrays["VGND", name]), "GDS and DEF physical cuts differ")
    return gdstk.__version__


def nearest(values, coordinate):
    position = bisect.bisect_left(values, coordinate)
    choices = values[max(0, position - 1):position + 1]
    ranked = sorted((abs(value - coordinate), value) for value in choices)
    require(len(ranked) == 1 or ranked[0][0] < ranked[1][0], "Ambiguous PSM via center")
    return ranked[0][1]


def via_currents(path, rail, families, arrays):
    pair_to_family = {item["layers"]: name for name, item in families.items()}
    axes = {}
    for name in families:
        positions = arrays[rail, name]
        axes[name] = [sorted({position[axis] for position in positions}) for axis in (0, 1)]
        require(set(itertools.product(*axes[name])) == positions, "Via placements are not the candidate grid")
    seen, groups, rounding_sensitive = defaultdict(set), {}, 0
    with (path / f"{rail}.spice").open() as spice, (path / f"{rail}-current.csv").open() as current:
        rows = csv_rows(current, "Node0 Layer,Node0 X location,Node0 Y location,Node1 Layer,Node1 X location,"
                                 "Node1 Y location,Current")
        for line in spice:
            if not line.startswith("R"):
                continue
            _, a, b, resistance = line.split()
            kind_a, layer_a, x_a, y_a = node(a)
            kind_b, layer_b, x_b, y_b = node(b)
            if (kind_a, kind_b) != ("Node", "Node"):
                require({kind_a, kind_b} & {"ITermNode", "BPinNode"}, "Unexpected non-geometric edge")
                continue
            layer0, x0, y0, layer1, x1, y1, value = next(rows)
            require((layer0, layer1) == (layer_a, layer_b)
                    and tuple(dbu(float(v)) for v in (x0, y0, x1, y1)) == (x_a, y_a, x_b, y_b),
                    "SPICE and current record differ")
            if layer_a == layer_b:
                continue
            name = pair_to_family[layer_a, layer_b]
            family = families[name]
            from_center = nearest(axes[name][0], x_a), nearest(axes[name][1], y_a)
            to_center = nearest(axes[name][0], x_b), nearest(axes[name][1], y_b)
            require(from_center == to_center and from_center in arrays[rail, name] and from_center not in seen[name],
                    "Merged PSM endpoints do not identify one unique physical array")
            x, y = from_center
            distance = max(abs(x_a - x), abs(y_a - y), abs(x_b - x), abs(y_b - y))
            require(distance < 2500, "PSM endpoint offset exceeds frozen-array association radius")
            seen[name].add(from_center)
            effective_cuts = CUT_RESISTANCE_OHM / float(resistance.removeprefix("R="))
            require(math.isclose(effective_cuts, family["cuts"], rel_tol=0, abs_tol=1e-4),
                    "PSM effective cuts differ from frozen physical array")
            raw_amperes = Decimal(value)
            require(raw_amperes.is_finite() and raw_amperes >= 0, "Invalid via current magnitude")
            modeled = raw_amperes * 1000
            half_unit = Decimal(5).scaleb(raw_amperes.as_tuple().exponent + 2) if raw_amperes else Decimal(0)
            upper = modeled + half_unit
            rounding_sensitive += (modeled <= LIMIT_MA < upper)
            group = groups.setdefault(family["cut"], dict(arrays=0, physical_cuts=0, arrays_over_equal_share_limit=0,
                arrays_without_one_cut_total_bound=0, maximum_endpoint_offset_um=0.0, maximum=None,
                arrays_requiring_sharing=[]))
            sample = dict(array_current_ma=modeled, current_upper_rounding_ma=upper,
                equal_share_ma_per_cut=modeled / family["cuts"], center_um=[x / DBU, y / DBU], cuts=family["cuts"],
                max_fraction_of_array_current_for_one_cut=min(Decimal(1), LIMIT_MA / upper) if upper else None,
                at_least_this_many_cuts_to_carry_rounded_upper_current=int((upper / LIMIT_MA).to_integral_value(
                    rounding=ROUND_CEILING)))
            group["arrays"] += 1
            group["physical_cuts"] += family["cuts"]
            group["arrays_over_equal_share_limit"] += upper > LIMIT_MA * family["cuts"]
            group["arrays_without_one_cut_total_bound"] += upper > LIMIT_MA
            if upper > LIMIT_MA:
                group["arrays_requiring_sharing"].append(sample)
            group["maximum_endpoint_offset_um"] = max(group["maximum_endpoint_offset_um"], distance / DBU)
            if group["maximum"] is None or modeled > group["maximum"]["array_current_ma"]:
                group["maximum"] = sample
        require(next(rows, None) is None, "Extra current records")
    require(all(seen[name] == arrays[rail, name] for name in families), "Unmapped physical via arrays")
    for group in groups.values():
        group["arrays_requiring_sharing"].sort(key=lambda sample: sample["center_um"])
    return groups, rounding_sensitive


def audit():
    def_path, gds = TRIAL / "trial.def", TARGET["gds"]
    require(sha(def_path) == DEF_SHA and sha(gds) == TARGET["gds_sha256"]
            and sha(TARGET["odb"]) == TARGET["odb_sha256"], "Frozen candidate geometry differs")
    power_root = TRIAL / "power-dc"
    dc_path = power_root / "ir-em-readback.json"
    require(sha(dc_path) == DC_SHA, "Expected the exact screened PSM matrix")
    dc = read(dc_path)
    require(dc["process_spec"] == PROCESS_SPEC and dc["target_odb_sha256"] == TARGET["odb_sha256"]
            and dc["target_gds_sha256"] == TARGET["gds_sha256"] and len(dc["cases"]) == 6, "DC matrix mismatch")
    families, arrays = parse_def(def_path)
    gdstk_version = gds_arrays(gds, families, arrays)
    cases = []
    for case in dc["cases"]:
        path = power_root / case["case"]
        require(bound(path / "readback.json") == case["native"] and bound(path / "request.json") == case["request"],
                "Native case and request identity differ")
        receipt = read(path / "readback.json")
        request = read(path / "request.json")
        require(request["inputs"]["/input/trial.odb"]["sha256"] == TARGET["odb_sha256"]
                and request["target_gds_sha256"] == TARGET["gds_sha256"], "Via model uses another target")
        artifacts = {Path(v["path"]).name: v for v in receipt["artifacts"]}
        inputs = {}
        for rail in RAILS:
            for filename in (f"{rail}.spice", f"{rail}-current.csv"):
                row = bound(path / filename)
                require(row == artifacts[filename], "PSM current evidence changed")
                inputs[filename] = row
        results, rounding_checks = {}, {}
        for rail in RAILS:
            groups, rounding_checks[rail] = via_currents(path, rail, families, arrays)
            for cut, result in groups.items():
                reference = case["rails"][rail]["segments"][cut]
                require(result["arrays"] == reference["edges"] and math.isclose(float(result["maximum"]["array_current_ma"]),
                        reference["max_current"]["current_ma"], rel_tol=1e-10), "Previous current screen disagrees")
            results[rail] = groups
        require(all(bound(path / name) == item for name, item in inputs.items()), "Current evidence changed during readback")
        cases.append(dict(case=case["case"], rails=results, threshold_rounding_cases=rounding_checks, inputs=inputs))
    return dict(schema="pinwheel.streaming-8x4-hold-cap-via-audit.v1", status="diagnostic",
        target_odb_sha256=TARGET["odb_sha256"], target_gds_sha256=TARGET["gds_sha256"],
        def_view=bound(def_path), gds=bound(gds), dc_readback=bound(dc_path), gdstk_version=gdstk_version,
        process_spec=PROCESS_SPEC, via_limit_ma_per_cut=float(LIMIT_MA),
        geometry=dict(arrays=sum(map(len, arrays.values())),
                      cuts=sum(len(points) * families[name]["cuts"] for (_, name), points in arrays.items())),
        cases=cases, qualified_em=False, physical_per_cut_electrical_solution=False,
        screen_scope="Every modeled Via1–3 array and physical cut is associated. Per-cut equal share assumes the solver's "
                     "lumped equipotential endpoints. An array total below one cut's limit bounds every cut only "
                     "conditional on all cuts carrying current in the same direction and the retained modeled total.")


if __name__ == "__main__":
    print(json.dumps(audit(), default=float, indent=2, sort_keys=True))
