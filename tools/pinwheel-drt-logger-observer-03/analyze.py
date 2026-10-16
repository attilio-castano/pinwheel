"""Host-only, fail-closed interpretation of the logger observer's JSONL."""
from __future__ import annotations
import json
import re
from collections import Counter
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
            tid = row["kernel_thread_id"]
            assert row["thread_id"] == tid
            assert isinstance(row["raw_msg_thread_id"], int) and row["raw_msg_thread_id"] >= 0
            if mode != "threads": assert row["cfg_max_threads"] == 1
            assert isinstance(tid, int) and tid > 0, "Native thread IDs unavailable"
            assert len(row["route_box_um"]) == 4
            headers[tid] = row
            ids.add(tid)
        elif row["event"] == "DRT1231":
            assert row.get("capture_error") is None and row["correlated"] and row["target_matches"]
            assert row["thread_id"] == row["kernel_thread_id"]
            assert row["kernel_thread_id"] in headers
            header = headers[row["kernel_thread_id"]]
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
    if mode == "threads":
        assert len(ids) >= 4, "Actual four-thread fixture kernel ID coverage required"
    else:
        assert len(ids) == 1, "Unchanged Design context requires one actual kernel worker ID"
    assert len(errors) == (0 if mode == "control" else 1)
    return {"status": "logger_observation_complete", "mode": mode,
            "distinct_worker_thread_ids": sorted(ids),
            "identity_source": "Linux_syscall_SYS_gettid_in_synchronous_sink_callback",
            "raw_msg_id_mismatch_worker_records": sum(r["raw_msg_thread_id"] != r["kernel_thread_id"] for r in rows if r["event"] == "worker"), "DRT1231_count": len(errors),
            "fresh_AP_ledger": errors[0].get("fresh_aps") if errors else None,
            "route_box_only_from_same_thread_header": True,
            "selected_truncated_endpoints_captured": False,
            "physical_acceptance_claim": False}


def analyze(path: Path, mode: str):
    return analyze_events(read_events(path), mode)


def reconcile_native_log(rows, native_text):
    actual = Counter(line.strip() for line in native_text.splitlines() if line.startswith("start DR worker (BOX)"))
    observed = Counter(r["payload"].strip() for r in rows if r["event"] == "worker")
    assert actual and actual == observed, "Incomplete or invented native worker-header ledger"
    errors = [line.strip() for line in native_text.splitlines() if "[ERROR DRT-1231]" in line]
    assert errors == [r["payload"].strip() for r in rows if r["event"] == "DRT1231"], "Native error ledger differs"
    return {"all_native_worker_headers_reconciled": True, "native_worker_header_count": sum(actual.values()), "native_DRT1231_count": len(errors)}


def qualify_context(after_load, before_route):
    for context in [after_load,before_route]:
        assert context['context']=='current_Design_evalTclString_native_context'
        assert context['openroad_thread_count']==context['cfg_max_threads']==1
        assert context['kernel_thread_id']>0
    for key in ['openroad_pointer','router_pointer','kernel_thread_id']:
        assert after_load[key]==before_route[key], "Changed native Design context"
    return {'status':'current_Design_context_one_thread_verified','no_thread_count_mutation':True}
