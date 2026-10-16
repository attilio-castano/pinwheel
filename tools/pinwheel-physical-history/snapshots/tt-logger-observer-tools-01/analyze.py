"""Host-only, fail-closed interpretation of the logger observer's JSONL."""
from __future__ import annotations
import json
from pathlib import Path


def read_events(path: Path):
    rows = [json.loads(line) for line in path.read_text().splitlines() if line.strip()]
    assert rows and rows[0]["event"] == "installed", "Missing install record"
    assert rows[-1]["event"] == "removed" and rows[-1]["io_ok"] is True, "Incomplete/failed sink output"
    assert not any(r["event"] == "observer_error" for r in rows), "Observer failed"
    return rows


def analyze_events(rows, mode: str):
    assert mode in ("threads", "control", "probe")
    assert rows[0]["event"] == "installed" and rows[-1] == {"event": "removed", "io_ok": True}
    headers, errors, ids = {}, [], set()
    for row in rows:
        if row["event"] == "worker":
            tid = row["thread_id"]
            assert isinstance(tid, int) and tid > 0, "Native thread IDs unavailable"
            assert len(row["route_box_um"]) == 4
            headers[tid] = row
            ids.add(tid)
        elif row["event"] == "DRT1231":
            assert row.get("capture_error") is None and row["correlated"] and row["target_matches"]
            assert row["thread_id"] in headers
            header = headers[row["thread_id"]]
            assert header["iteration"] == row["iteration"], "Stale worker header"
            if mode == "threads":
                assert row["fixture"] is True
                assert header["route_box_um"] == [20, 0, 21, 1]
            elif mode == "probe":
                assert row["fixture"] is False
                aps = row["fresh_aps"]
                assert aps["source"] == "fresh_global_frDesign_inside_original_error_log_call"
                assert aps["instance"] == "engine.memory.storage1" and aps["terminal"] == "A_BM[31]"
                box = aps["route_box_dbu"]
                assert [round(v * aps["dbu_per_micron"]) for v in header["route_box_um"]] == box
                points = [p for pin in aps["pins"] for p in pin["aps"]]
                assert points and len(points) == aps["generated_ap_count"], "Vacuous AP capture"
                for point in points:
                    x, y = point["global_dbu"]
                    inside = box[0] <= x <= box[2] and box[1] <= y <= box[3]
                    assert point["inside_route_box"] == inside, "Incorrect AP/clip predicate"
                assert sum(p["inside_route_box"] for p in points) == aps["eligible_ap_count"] == 0
                assert aps["selected_truncated_endpoints_captured"] is False
            else:
                raise AssertionError("No-edit control emitted DRT1231")
            errors.append(row)
        elif row["event"] == "observer_error":
            raise AssertionError("Observer failed")
    assert len(ids) >= 4, "Actual four-thread worker-header ID coverage required"
    assert len(errors) == (0 if mode == "control" else 1)
    return {"status": "logger_observation_complete", "mode": mode,
            "distinct_worker_thread_ids": sorted(ids), "DRT1231_count": len(errors),
            "fresh_AP_ledger": errors[0].get("fresh_aps") if errors else None,
            "route_box_only_from_same_thread_header": True,
            "selected_truncated_endpoints_captured": False,
            "physical_acceptance_claim": False}


def analyze(path: Path, mode: str):
    return analyze_events(read_events(path), mode)
