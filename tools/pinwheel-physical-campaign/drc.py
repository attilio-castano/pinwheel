"""Read-only OpenROAD evidence parsing. Progress, final native counts and report
subsets deliberately have separate ledgers. This module never runs CAD.
"""
from __future__ import annotations

import argparse
from collections import Counter
import json
from pathlib import Path
import re
from typing import Any

_START = re.compile(r"Start (\d+)(?:st|nd|rd|th) optimization iteration\.")
_COUNT = re.compile(r"Number of violations\s*=\s*(\d+)")
_PROGRESS = re.compile(r"Completing\s+(\d+)%\s+with\s+(\d+)\s+violations")
_ROW = re.compile(r"^\s*([A-Za-z][A-Za-z0-9 _/()\-]*?)\s+((?:\d+\s+)*\d+)\s*$")


def _cut_layer(name: str) -> bool:
    return bool(re.match(r"^(?:Via|TopVia|Cut|V\d+$)", name, re.I))


def native_type_counts(table: dict[str, Any]) -> dict[str, int]:
    """Translate the native combined Short row into report category names."""
    result: dict[str, int] = {}
    for kind, values in table["rows"].items():
        if kind == "Short":
            result["Short"] = sum(v for layer, v in values.items() if not _cut_layer(layer))
            result["Cut Short"] = sum(v for layer, v in values.items() if _cut_layer(layer))
        else:
            result[kind] = sum(values.values())
    return result


def parse_report_subset(text: str, native_table: dict[str, Any] | None = None,
                        category_limit: int | None = None) -> dict[str, Any]:
    """Count actual records. A supplied limit is provenance, never an assumption
    that a limit-sized category is complete or represents the whole design.
    """
    types: Counter[str] = Counter()
    layers: Counter[str] = Counter()
    incomplete: list[int] = []
    records = list(re.finditer(r"(?m)^violation type:\s*(.+?)\s*$", text))
    for i, match in enumerate(records):
        body = text[match.end():records[i + 1].start() if i + 1 < len(records) else len(text)]
        types[match[1]] += 1
        layer = re.search(r"bbox\s*=.*?\bon Layer\s+(\S+)", body)
        if layer:
            layers[layer[1]] += 1
        if not layer or not re.search(r"(?m)^\s*srcs:", body):
            incomplete.append(text.count("\n", 0, match.start()) + 1)
    full = native_type_counts(native_table) if native_table else None
    missing = {k: v - types.get(k, 0) for k, v in (full or {}).items()}
    extra = {k: v for k, v in types.items() if full is not None and k not in full}
    consistent = full is not None and not extra and all(v >= 0 for v in missing.values())
    complete = bool(consistent and not incomplete and all(v == 0 for v in missing.values()))
    return {
        "record_count": len(records), "type_counts": dict(types), "layer_counts": dict(layers),
        "incomplete_record_start_lines": incomplete, "native_type_counts": full,
        "native_minus_report_by_type": missing if full is not None else None,
        "unexpected_report_categories": extra, "report_is_complete_native_ledger": complete,
        "report_counts_do_not_exceed_native": consistent,
        "known_category_limit": category_limit,
        "categories_at_known_limit": [k for k, v in types.items() if category_limit is not None and v == category_limit],
        "spatial_and_source_denominator": "actual report records only",
    }


def parse_native_log(text: str, report_text: str | None = None, *,
                     category_limit: int | None = None,
                     producer_status: str | None = None) -> dict[str, Any]:
    lines = text.splitlines()
    starts: list[dict[str, int]] = []
    counters: list[dict[str, Any]] = []
    progress: list[dict[str, Any]] = []
    tables: list[dict[str, Any]] = []
    complete_lines: list[int] = []
    errors: list[dict[str, Any]] = []
    connectivity_failures: list[dict[str, Any]] = []
    unsupported: list[dict[str, Any]] = []
    pa: dict[str, int] = {}
    current_iteration: int | None = None
    for i, line in enumerate(lines):
        number = i + 1
        if match := _START.search(line):
            current_iteration = int(match[1])
            starts.append({"iteration": current_iteration, "line": number})
        if match := _COUNT.search(line):
            counters.append({"count": int(match[1]), "line": number, "iteration": current_iteration})
        if match := _PROGRESS.search(line):
            progress.append({"percent": int(match[1]), "count": int(match[2]),
                             "line": number, "iteration": current_iteration})
        if "Complete detail routing." in line:
            complete_lines.append(number)
        if re.search(r"\[ERROR\b", line) or re.match(r"^(?:\w*Error|\w*Exception):", line):
            errors.append({"line": number, "text": line})
        if re.search(r"DRT-0?206\b|checkConnectivity\s+break", line):
            connectivity_failures.append({"line": number, "text": line})
        if "DRT-0349" in line:
            unsupported.append({"line": number, "text": line})
        if match := re.match(r"\s*#(\w+)\s*=\s*(\d+)\s*$", line):
            pa[match[1]] = int(match[2])
        if not re.match(r"^\s*Viol/Layer\s+", line):
            continue
        columns = line.split()[1:]
        rows: dict[str, dict[str, int]] = {}
        issues: list[str] = []
        if not columns or len(columns) != len(set(columns)):
            issues.append("empty or duplicate layer columns")
        j = i + 1
        while j < len(lines):
            row = _ROW.match(lines[j])
            if not row:
                break
            values = [int(v) for v in row[2].split()]
            if len(values) != len(columns):
                issues.append(f"row at line {j + 1} has {len(values)} cells for {len(columns)} layers")
                break
            if row[1] in rows:
                issues.append(f"duplicate row {row[1]}")
            rows[row[1]] = dict(zip(columns, values))
            j += 1
        nearest = next((v for v in reversed(counters)
                        if v["iteration"] == current_iteration and 0 < number - v["line"] <= 8), None)
        total = sum(sum(values.values()) for values in rows.values())
        if nearest is None:
            issues.append("no adjacent native violation counter")
        elif total != nearest["count"]:
            issues.append(f"table sum {total} differs from native counter {nearest['count']}")
        if not rows and (nearest is None or nearest["count"] != 0):
            issues.append("empty nonzero table")
        tables.append({"line": number, "end_line": j, "iteration": current_iteration,
                       "layers": columns, "rows": rows, "table_sum": total,
                       "native_counter": nearest, "sum_verified": not issues, "issues": issues})
    final_table = None
    latest_route_completed = bool(complete_lines and (not starts or complete_lines[-1] > starts[-1]["line"]))
    if latest_route_completed:
        completion = complete_lines[-1]
        preceding = [v for v in tables if v["line"] < completion]
        # Never fall back to an earlier valid table when the latest one is corrupt.
        if preceding:
            candidate = preceding[-1]
            later_starts = [v for v in starts if candidate["line"] < v["line"] < completion]
            if candidate["sum_verified"] and not later_starts:
                final_table = candidate
    result = {
        "schema": "pinwheel-native-DRT-evidence-v1", "producer_status_retained": producer_status,
        "iteration_starts": starts, "progress_observations": progress,
        "native_counter_observations": counters, "native_table_observations": tables,
        "detail_route_completion_lines": complete_lines,
        "native_route_command_completion_observed": bool(complete_lines),
        "latest_native_route_completed": latest_route_completed,
        "completed_native_final_table": final_table,
        "completed_native_final_count": final_table["table_sum"] if final_table else None,
        "completed_native_type_counts": native_type_counts(final_table) if final_table else None,
        "native_error_lines": errors, "native_modified_mapped_pin_checker_failure_lines": connectivity_failures,
        "all_native_terminal_connectivity_proven": False,
        "connectivity_scope": "native modified-net route-endpoint-mapped-pin checker only; absence of errors does not enumerate all native terminals",
        "pin_access_complete": any("Complete pin access." in line for line in lines),
        "pin_access_counters": pa, "unsupported_rule_warning_lines": unsupported,
        "power_connected_messages": [line for line in lines if "All shapes on net" in line and "are connected" in line],
        "physical_signoff_or_acceptance_claim": False,
    }
    result["report_subset"] = parse_report_subset(report_text, final_table, category_limit) if report_text is not None else None
    return result


def compare_native_stages(control: dict[str, Any], candidate: dict[str, Any], *,
                          required_candidate_iteration: int | None = None) -> dict[str, Any]:
    """Evidence comparison only. Frozen scope/control-wire gates remain external."""
    before, after = control["completed_native_final_count"], candidate["completed_native_final_count"]
    available = before is not None and after is not None
    kinds = set(control["completed_native_type_counts"] or {}) | set(candidate["completed_native_type_counts"] or {})
    deltas = {kind: (candidate["completed_native_type_counts"] or {}).get(kind, 0)
              - (control["completed_native_type_counts"] or {}).get(kind, 0)
              for kind in sorted(kinds)} if available else None
    return {
        "schema": "pinwheel-native-DRT-comparison-v1",
        "both_completed_native_counts_available": available,
        "control_count": before, "candidate_count": after,
        "candidate_minus_control_count": after - before if available else None,
        "candidate_minus_control_type_counts": deltas,
        "control_producer_status_retained": control["producer_status_retained"],
        "candidate_producer_status_retained": candidate["producer_status_retained"],
        "required_candidate_iteration": required_candidate_iteration,
        "required_candidate_iteration_observed": (any(v["iteration"] == required_candidate_iteration
                                                       for v in candidate["iteration_starts"])
                                                   if required_candidate_iteration is not None else None),
        "control_native_error_lines": control["native_error_lines"],
        "candidate_native_error_lines": candidate["native_error_lines"],
        "control_native_checker_failure_lines": control["native_modified_mapped_pin_checker_failure_lines"],
        "candidate_native_checker_failure_lines": candidate["native_modified_mapped_pin_checker_failure_lines"],
        "all_native_terminal_connectivity_proven": False,
        "frozen_scope_and_no_edit_control_must_be_verified_separately": True,
        "physical_acceptance_claim": False,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("native_log", type=Path)
    parser.add_argument("--report", type=Path)
    parser.add_argument("--category-limit", type=int)
    args = parser.parse_args()
    print(json.dumps(parse_native_log(args.native_log.read_text(),
                                     args.report.read_text() if args.report else None,
                                     category_limit=args.category_limit), indent=2))


if __name__ == "__main__":
    main()
