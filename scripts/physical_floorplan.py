"""Derive a chip experiment from explicit macro placements and row exclusions.

The placed database and power-grid checks remain responsible for geometric
legality and pin access. This helper protects the RTL, views, die and timing
boundary while making a separate, resumable experiment configuration.
"""
from copy import deepcopy
from decimal import Decimal
import math


def apply_placement(config, placements):
    if not isinstance(placements, dict) or not placements:
        raise ValueError("Macro placements must be a nonempty instance mapping")
    result = deepcopy(config)
    instances = {}
    for macro in result.get("MACROS", {}).values():
        for name, instance in macro.get("instances", {}).items():
            if name in instances:
                raise ValueError(f"Duplicate macro instance: {name}")
            instances[name] = instance
    for name, placement in placements.items():
        if name not in instances:
            raise ValueError(f"Unknown macro instance: {name}")
        if not isinstance(placement, dict) or set(placement) != {"location", "orientation"}:
            raise ValueError("Each macro placement needs only location and orientation")
        location = placement["location"]
        if (not isinstance(location, list) or len(location) != 2 or
                any(type(v) not in (int, float) or not math.isfinite(v) for v in location)):
            raise ValueError("Macro location must contain two finite numbers")
        x0, y0, x1, y1 = config["DIE_AREA"]
        if not (x0 <= location[0] < x1 and y0 <= location[1] < y1):
            raise ValueError("Macro location is outside the die")
        if placement["orientation"] not in ("N", "S", "E", "W", "FN", "FS", "FE", "FW"):
            raise ValueError("Invalid macro orientation")
        instances[name].update(deepcopy(placement))
    return result


def overlaps(a, b):
    """Positive-area overlap; boundary contact alone is allowed."""
    return max(a[0], b[0]) < min(a[2], b[2]) and max(a[1], b[1]) < min(a[3], b[3])


def to_dbu(rect, units):
    if type(units) is not int or units <= 0:
        raise ValueError("Invalid database units")
    result = [Decimal(str(x)) * units for x in rect]
    if any(not x.is_finite() or x != x.to_integral_value() for x in result):
        raise ValueError("Geometry is not on the integer database grid")
    return list(map(int, result))


def apply_exclusions(config, exclusions):
    """Remove placement sites using the pinned flow's FP_OBSTRUCTIONS setting.

    These are placement exclusions: signal routing remains permitted. Physical
    reports must still check row removal, macro intersections and placed cells.
    """
    if not isinstance(exclusions, list) or not exclusions:
        raise ValueError("Placement exclusions must be a nonempty rectangle list")
    die = config["DIE_AREA"]
    for rect in exclusions:
        if (not isinstance(rect, list) or len(rect) != 4 or
                any(type(v) not in (int, float) or not math.isfinite(v) for v in rect)):
            raise ValueError("Each placement exclusion needs four finite numbers")
        if not (die[0] <= rect[0] < rect[2] <= die[2] and
                die[1] <= rect[1] < rect[3] <= die[3]):
            raise ValueError("Placement exclusion must have positive area inside the die")
    result = deepcopy(config)
    result["FP_OBSTRUCTIONS"] = deepcopy(config.get("FP_OBSTRUCTIONS") or []) + deepcopy(exclusions)
    return result


def exclusion_report(context, exclusions):
    """Check actual row and instance geometry, including boundary straddlers."""
    apply_exclusions({"DIE_AREA": context["die"]}, exclusions)
    regions = []
    for rect in exclusions:
        exact = context.get("schema", 1) >= 2
        key = "bbox_dbu" if exact else "bbox"
        checked_rect = to_dbu(rect, context["dbu_per_micron"]) if exact else rect
        instances = {n: v for n, v in context["instances"].items() if overlaps(checked_rect, v[key])}
        rows = [r for r in context["rows"] if overlaps(checked_rect, r[key])]
        blockages = [b for b in context["placement_blockages"] if b[key] == checked_rect and not b["soft"]]
        regions.append(dict(bbox=rect, overlapping_instances=instances, overlapping_rows=rows,
                            matching_blockages=blockages, clear=not instances and not rows and bool(blockages)))
    return dict(regions=regions, clear=all(r["clear"] for r in regions))
