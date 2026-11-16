"""Audit the equal-plane cut-resistance sensitivity and sparse landing geometry."""

import argparse
from pathlib import Path

from streaming_8x4_draft_rc_timing import bound
from streaming_8x4_e982_native import read, require, sha, write
from streaming_8x4_hold_cap_via_audit import parse_def
from streaming_8x4_hold_cap_via_feeds import DEF_SHA, ROOT, VIA_READBACK, VIA_SHA
from streaming_8x4_hold_cap_physical import TARGET, TRIAL


FEEDS = ROOT / "via-feeds-01.json"
FEEDS_SHA = "4cad8af2c8271f58277efc49202ae20e8b710c5058796fb5eeba768b07a7045b"
CUT_LIMIT_MA = 0.4


def corner_ratio(cuts, resistance_ratio):
    """Fraction through one low-resistance cut between equipotential planes."""
    require(cuts >= 2 and resistance_ratio >= 1, "Invalid parallel via model")
    return resistance_ratio / (resistance_ratio + cuts - 1)


def maximum_ratio(cuts, total_ma):
    """Largest R_other/R_selected before the closed-form reference is reached."""
    require(total_ma > CUT_LIMIT_MA, "No finite resistance ratio needed for the stated total")
    return CUT_LIMIT_MA * (cuts - 1) / (total_ma - CUT_LIMIT_MA)


def contact_footprints(feed, families, half_width_dbu):
    family_by_cut = {row["cut"]: row for row in families.values()}
    rows = []
    for array in feed["arrays"]:
        x, y = array["center_dbu"]
        family = family_by_cut[array["cut"]]
        for side in array["sides"]:
            for edge in side["other"]:
                if edge["neighbor"]["kind"] != "Source Node":
                    continue
                sx, sy = edge["neighbor"]["point_dbu"]
                sx, sy = sx - x, sy - y
                overlaps = []
                for box in sorted(family["boxes"]):
                    x0, y0, x1, y1 = box
                    width = max(0, min(sx + half_width_dbu, x1) - max(sx - half_width_dbu, x0))
                    height = max(0, min(sy + half_width_dbu, y1) - max(sy - half_width_dbu, y0))
                    if width * height:
                        overlaps.append(dict(cut_relative_bounds_dbu=box, intersection_area_dbu2=width * height))
                rows.append(dict(rail=array["rail"], cut=array["cut"], via_center_dbu=(x, y),
                                 source_center_dbu=(sx + x, sy + y), outward_a=edge["outward_a"],
                                 projected_cut_intersections=overlaps))
    require(len(rows) == 8 and {row["cut"] for row in rows} == {"Via3"}, "Wrong sparse contact inventory")
    return rows


def audit():
    def_path = TRIAL / "trial.def"
    require(sha(VIA_READBACK) == VIA_SHA and sha(FEEDS) == FEEDS_SHA and sha(def_path) == DEF_SHA,
            "Frozen via inputs changed")
    previous = read(VIA_READBACK)
    feeds = read(FEEDS)
    families, _ = parse_def(def_path)
    bound_centers = {row["cut"]: row["cuts"] for row in families.values()}
    cases = []
    for case in previous["cases"]:
        by_rail = {}
        for rail, layers in case["rails"].items():
            by_rail[rail] = {}
            for cut, observations in layers.items():
                modeled = []
                for row in observations["arrays_requiring_sharing"]:
                    current = row["current_upper_rounding_ma"]
                    cuts = row["cuts"]
                    require(cuts == bound_centers[cut], "Cut count changed")
                    modeled.append(dict(center_um=row["center_um"], cuts=cuts, total_upper_ma=current,
                                        uniform_ma=current / cuts,
                                        one_5_others_20_ma=current * corner_ratio(cuts, 4),
                                        max_ratio_before_limit=maximum_ratio(cuts, current)))
                by_rail[rail][cut] = modeled
        cases.append(dict(case=case["case"], rails=by_rail))
    return dict(schema="pinwheel.streaming-8x4-hold-cap-cut-parallel.v1", status="diagnostic",
                target_odb_sha256=TARGET["odb_sha256"], target_gds_sha256=TARGET["gds_sha256"],
                cut_limit_ma=CUT_LIMIT_MA, def_view=bound(def_path), via_readback=bound(VIA_READBACK),
                feeds=bound(FEEDS), cases=cases, sparse_landing_side_dbu=1000,
                sparse_landings=contact_footprints(feeds, families, 500),
                scope="Fixed total current, equipotential sheets and deliberately mixed 5/20 ohm cuts. "
                      "This is a resistance-ratio control, without a local mismatch distribution or a spatial solution.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", required=True, type=Path)
    out = parser.parse_args().out.resolve()
    require(out.parent == ROOT and not out.exists(), "Use a fresh result in power-dc")
    write(out, audit())


if __name__ == "__main__":
    main()
