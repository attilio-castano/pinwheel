#!/usr/bin/env python3
"""Bundle the local Pinwheel explorer, its recorded trace and source excerpts."""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
from dataclasses import asdict
from datetime import datetime, timezone
from html.parser import HTMLParser
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
EXPLORER = ROOT / "docs" / "explorer"
CACHE = ROOT / "build" / "explorer"
LARGE_RECORDINGS = ("buffered-session.json", "i2c-traces.json")
RECEIPT_SCHEMA = "pinwheel-explorer-recording-receipts-v1"
SEMANTIC_DIGEST = "sha256-canonical-json-v1"


def canonical_sha256(value) -> str:
    """Hash JSON values, independently of indentation or object member order."""
    encoded = json.dumps(value, ensure_ascii=False, allow_nan=False,
        sort_keys=True, separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def read_json(text: str):
    def unique_members(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                raise ValueError(f"Duplicate JSON member: {key}")
            result[key] = value
        return result

    def invalid_constant(value):
        raise ValueError(f"Non-finite JSON number: {value}")

    return json.loads(text, object_pairs_hook=unique_members, parse_constant=invalid_constant)


class SnapshotData(HTMLParser):
    """Read the inert data script; never evaluate JavaScript or HTML."""

    def __init__(self):
        super().__init__(convert_charrefs=False)
        self.blocks = []
        self.current = None

    def handle_starttag(self, tag, attrs):
        attributes = dict(attrs)
        if tag == "script" and attributes.get("id") == "explorer-data":
            if attributes.get("type") != "application/json" or self.current is not None:
                raise ValueError("Explorer snapshot has an invalid recording data script.")
            self.current = []

    def handle_data(self, data):
        if self.current is not None:
            self.current.append(data)

    def handle_endtag(self, tag):
        if tag == "script" and self.current is not None:
            self.blocks.append("".join(self.current))
            self.current = None


def snapshot_payload(path: Path):
    if not path.is_file():
        raise ValueError("No recording cache or standalone explorer snapshot; regenerate the recordings first.")
    parser = SnapshotData()
    parser.feed(path.read_text())
    parser.close()
    if parser.current is not None or len(parser.blocks) != 1:
        raise ValueError("Explorer snapshot must contain exactly one complete JSON data script.")
    return read_json(parser.blocks[0])


def large_recordings():
    """Prefer generated caches; a bad cache must fail, not silently fall back."""
    recordings = {}
    snapshot = None
    for name in LARGE_RECORDINGS:
        cached = CACHE / name
        if cached.exists():
            recordings[name] = read_json(cached.read_text())
            continue
        if snapshot is None:
            snapshot = snapshot_payload(EXPLORER / "index.html")
        if name == "buffered-session.json":
            recordings[name] = snapshot["bufferedSession"]
        else:
            recordings[name] = {"traces": [trace for trace in snapshot["protocolTraces"]
                if trace["protocol"] == "i2c"]}
    return recordings


def recording_receipts(recordings):
    session = recordings["buffered-session.json"]
    i2c = recordings["i2c-traces.json"]["traces"]
    if len(i2c) != 4 or any(trace["protocol"] != "i2c" for trace in i2c):
        raise ValueError("I2C recording must contain exactly four I2C scenarios.")
    source_hashes = {}
    for trace in i2c:
        for path, digest in trace["sourceHashes"].items():
            if path in source_hashes and source_hashes[path] != digest:
                raise ValueError(f"I2C recordings disagree about source bytes: {path}")
            source_hashes[path] = digest
    evidence = session["executionEvidence"]
    return {
        "schema": RECEIPT_SCHEMA,
        "digestConvention": SEMANTIC_DIGEST,
        "digestEncoding": "UTF-8 JSON; sorted object keys; compact separators; unescaped Unicode; finite numbers",
        "recordings": {
            "buffered-session.json": {
                "sha256": canonical_sha256(session),
                "id": session["id"],
                "target": session["target"],
                "sourceRevision": session["sourceRevision"],
                "frameCount": len(session["frames"]),
                "stageCount": len(session["stages"]),
                "imageCount": len(session["images"]),
                "transfers": [{key: transfer[key] for key in (
                    "id", "startFrame", "completeFrame", "imageId", "expectedRxHex", "decodedRxHex")}
                    for transfer in session["transfers"]],
                "checks": session["checks"],
                "executionDigests": {key: evidence[key] for key in (
                    "producerSHA256", "transcriptSHA256", "recordedOutputSHA256")},
                "sourceHashes": session["sourceHashes"],
            },
            "i2c-traces.json": {
                "sha256": canonical_sha256(recordings["i2c-traces.json"]),
                "scenarioCount": len(i2c),
                "frameCount": sum(len(trace["frames"]) for trace in i2c),
                "scenarios": [{
                    **{key: trace[key] for key in ("id", "scenario", "sourceRevision", "activeCycles", "parameters", "outcome")},
                    "frameCount": len(trace["frames"]),
                } for trace in i2c],
                "sourceHashes": source_hashes,
            },
        },
    }


def verify_receipts(expected):
    path = EXPLORER / "recordings.json"
    if not path.is_file():
        raise ValueError("Missing recordings.json; validate and accept recordings with --refresh-receipts.")
    actual = read_json(path.read_text())
    if actual != expected:
        raise ValueError("Recording data or receipt changed; regenerate and validate with --refresh-receipts before accepting it.")


def revision() -> str:
    return subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()


def revision_on_remote(source_revision: str) -> bool:
    """Only offer GitHub links for revisions known to local origin tracking refs."""
    refs = subprocess.check_output(
        ["git", "for-each-ref", "--contains", source_revision,
         "--format=%(refname)", "refs/remotes/origin"],
        cwd=ROOT, text=True,
    )
    return bool(refs.strip())


def references(value):
    if isinstance(value, dict):
        if {"path", "start", "end"} <= value.keys():
            yield value
        for child in value.values():
            yield from references(child)
    elif isinstance(value, list):
        for child in value:
            yield from references(child)


def validate_source_hashes(trace):
    if not trace.get("sourceHashes"):
        raise ValueError(f"Recording {trace['id']} must identify its source bytes.")
    for rel, expected in trace["sourceHashes"].items():
        path = (ROOT / rel).resolve()
        if not path.is_relative_to(ROOT) or not path.is_file():
            raise ValueError(f"Missing or invalid trace source: {rel}")
        actual = hashlib.sha256(path.read_bytes()).hexdigest()
        if actual != expected:
            raise ValueError(f"Recorded trace source changed: {rel}; regenerate it first.")


def validate_recording(trace):
    validate_source_hashes(trace)
    frames = trace["frames"]
    end = trace["activeCycles"]
    if len(frames) != end + 2 or [f["cycle"] for f in frames] != list(range(len(frames))):
        raise ValueError(f"Recording {trace['id']} must include active intervals and two terminal states.")
    if any(f["busy"] != (f["cycle"] < end) for f in frames):
        raise ValueError(f"Recording {trace['id']} has inconsistent completion timing.")
    if trace.get("protocol") not in {"spi", "i2c"}:
        return
    pcs = {p["pc"] for p in trace["program"]}
    if len(pcs) != len(trace["program"]):
        raise ValueError(f"Duplicate program rows in {trace['id']}")
    seen = set()
    for frame in frames:
        if frame["busy"] and frame["pc"] not in pcs:
            raise ValueError(f"Unknown active PC in {trace['id']}")
        if not frame["busy"] and (frame["pc"] is not None or frame["remaining"] is not None):
            raise ValueError(f"Stopped state exposes an active counter in {trace['id']}")
        if len(frame["captures"]) != 16 or any(v not in {0, 1} for v in frame["captures"]):
            raise ValueError(f"Invalid capture values in {trace['id']}")
        slots = set(frame["validSlots"])
        if not seen <= slots or not slots <= set(range(16)):
            raise ValueError(f"Invalid capture provenance in {trace['id']}")
        seen = slots
        if frame["captureIndex"] is not None and frame["captureIndex"] not in slots:
            raise ValueError(f"Capture marker has no observation in {trace['id']}")
        raw = sum(v << i for i, v in enumerate(frame["captures"]))
        if raw != frame["rawResult"]:
            raise ValueError(f"Capture packing mismatch in {trace['id']}")
        for signal in trace["signals"]:
            if frame["signals"].get(signal["key"]) not in {0, 1}:
                raise ValueError(f"Invalid signal in {trace['id']}")
        if trace["protocol"] == "i2c":
            s = frame["signals"]
            if s["scl"] != int(not (s["sclEnable"] or s["peerHeldSCL"])) or s["sda"] != int(not (s["sdaEnable"] or s["peerHeldSDA"])):
                raise ValueError(f"Open-drain resolution mismatch in {trace['id']}")
    final = frames[-1]
    if final["complete"] != (trace["outcome"]["engine"] == "complete"):
        raise ValueError(f"Terminal outcome mismatch in {trace['id']}")
    if trace["protocol"] == "spi" and (final["rawResult"] != 0x69 or final["decoded"] != 0x96 or seen != set(range(8))):
        raise ValueError(f"SPI receive outcome mismatch in {trace['id']}")


def validate_buffered_session(session):
    from buffered_counted_hardware import _read_program, decode_control
    from buffered_reactive_hardware import decode_reactive_instruction
    from buffered_sram_hardware import (ALLOCATED_SRAM_BITS, FORMAT,
        ROW_METADATA_WIDTH, SRAM_COPIES, SRAM_WORD_WIDTH, lower_sram)
    from buffered_reactive_hardware_rtl import STATE_WIDTHS

    validate_source_hashes(session)
    if (session.get("schema") != "pinwheel-explorer-buffered-session-v1" or
            session["target"] != FORMAT or session["checks"].get("passed") is not True):
        raise ValueError("Buffered session must identify the checked SRAM target.")
    frames, stages, images = session["frames"], session["stages"], session["images"]
    if not frames or [f["edge"] for f in frames] != list(range(len(frames))):
        raise ValueError("Buffered session must retain every controller edge in order.")
    evidence = session["executionEvidence"]
    transcript = [dict(command=f["command"], raw_inputs=f["rawInputs"]) for f in frames]
    outputs = [dict(state=f["state"], fetch=f["fetch"]) for f in frames]
    digest = lambda value: hashlib.sha256(json.dumps(value,
        sort_keys=True, separators=(",", ":")).encode()).hexdigest()
    if (digest(transcript) != evidence["transcriptSHA256"] or
            digest(outputs) != evidence["recordedOutputSHA256"] or
            hashlib.sha256(evidence["producerSource"].encode()).hexdigest() != evidence["producerSHA256"]):
        raise ValueError("Buffered retained producer, transcript or model observations changed.")
    if len({s["id"] for s in stages}) != len(stages) or len({i["id"] for i in images}) != len(images):
        raise ValueError("Buffered session stage and image identities must be unique.")
    image_by_id = {image["id"]: image for image in images}
    stage_ids = {stage["id"] for stage in stages}
    for image in images:
        bound = lower_sram(_read_program(image["source"]["definition"]))
        rows = image["rows"]
        if image["target"] != FORMAT or image["programKey"] != bound.program_key or image["imageKey"] != bound.key:
            raise ValueError("Buffered source/image identity differs from canonical lowering.")
        if (image["virtualSpan"], image["txBits"], image["rxBits"], len(rows)) != (
                bound.virtual_span, bound.tx_bits, bound.rx_bits, len(bound.words)):
            raise ValueError("Buffered image geometry differs from its source.")
        if [row["pc"] for row in rows] != list(range(len(rows))):
            raise ValueError("Buffered resident rows must preserve address order.")
        if ([int(row["wordHex"], 16) for row in rows] != list(bound.words) or
                [int(row["controlHex"], 16) for row in rows] != list(bound.controls) or
                [row["branchIndex"] for row in rows] != list(bound.branch_indices) or
                [d["index"] for d in image["dictionary"]] != list(range(16)) or
                [int(d["wordHex"], 16) for d in image["dictionary"]] != list(bound.branch_table)):
            raise ValueError("Buffered recorded rows/dictionary differ from admitted source bytes.")
        for row, word, control in zip(rows, bound.words, bound.controls):
            if (row["instruction"] != asdict(decode_reactive_instruction(word)) or
                    row["loop"] != asdict(decode_control(control))):
                raise ValueError("Buffered displayed instruction/loop differs from its resident bytes.")
        storage = dict(bound.storage(), instructionWordBits=SRAM_WORD_WIDTH,
            metadataBits=ROW_METADATA_WIDTH, physicalRowBits=SRAM_WORD_WIDTH + ROW_METADATA_WIDTH,
            dictionaryWordBits=56, instructionReplicas=SRAM_COPIES,
            allocatedInstructionSRAMBits=ALLOCATED_SRAM_BITS)
        if (image["storage"] != storage or image["wireOrder"] != bound.wire_order or
                image["idleLevels"] != bound.idle_levels or image["idleEnabled"] != bound.idle_enabled):
            raise ValueError("Buffered displayed storage/wire contract differs from its canonical image.")
    for stage in stages:
        if not stage.get("sources"):
            raise ValueError("Every buffered stage must navigate to its governing sources.")
        first, last = stage["firstFrame"], stage["lastFrame"]
        if first is None and last is None:
            continue
        if type(first) is not int or type(last) is not int or not 0 <= first <= last < len(frames):
            raise ValueError("Invalid buffered stage interval.")
        if any(f["stage"] != stage["id"] for f in frames[first:last + 1]):
            raise ValueError("Buffered stage interval misidentifies its actual transitions.")
    for frame in frames:
        if frame["stage"] not in stage_ids or frame["imageId"] not in image_by_id or frame["rawInputs"] not in range(4):
            raise ValueError("Buffered frame has an unknown stage, image or input.")
        state, image = frame["state"], image_by_id[frame["imageId"]]
        for key, width in STATE_WIDTHS.items():
            if type(state.get(key)) is not int or not 0 <= state[key] < 2 ** width:
                raise ValueError(f"Invalid buffered observation {key} at edge {frame['edge']}.")
        if state["busy"] and (not state["valid"] or state["retained"] or state["pc"] >= len(image["rows"])):
            raise ValueError("Buffered busy state lacks an admitted resident instruction.")
        if state["valid"] and not frame["fetch"]["ready"]:
            raise ValueError("Buffered valid frame lacks its checked prospective responses.")
        if state["rx_length"] > 32 or state["tx_consumed"] > 32:
            raise ValueError("Buffered transfer exceeds its declared data capacity.")
    for transfer in session["transfers"]:
        first, last = transfer["startFrame"], transfer["completeFrame"]
        if not 0 <= first < last < len(frames) or transfer["imageId"] not in image_by_id:
            raise ValueError("Invalid buffered transfer interval.")
        image = image_by_id[transfer["imageId"]]
        if any(f["imageId"] != image["id"] or not f["state"]["busy"] for f in frames[first:last]):
            raise ValueError("Buffered transfer changes resident image or stops before its completion.")
        final = frames[last]["state"]
        if final["busy"] or not final["retained"] or final["phase"] != 5:
            raise ValueError("Buffered SPI completion must retain its completed owner.")
        raw = sum(int(byte) << (8 * k) for k, byte in enumerate(
            int(f'{byte:08b}'[::-1], 2) for byte in bytes.fromhex(transfer["expectedRxHex"])))
        if (final["rx_data"], final["rx_length"], final["tx_consumed"]) != (raw, image["rxBits"], image["txBits"]):
            raise ValueError("Buffered retained receive prefix differs from the independent reply.")
        if transfer["decodedRxHex"] != transfer["expectedRxHex"] or last - first != transfer["peer"]["execution_edges"]:
            raise ValueError("Buffered transfer result or elapsed edges differ from its peer.")
    checks = session["checks"]
    if checks["edges"] != len(frames) or checks["sourceWireTransfers"] != len(session["transfers"]):
        raise ValueError("Buffered recording check counts omit recorded work.")
    if any(checks.get(key, 0) <= 0 for key in ("coreFieldChecks", "publicOutputChecks", "residentFieldChecks",
            "ordinaryBoundaries", "sourceStateChecks", "sourceWireChecks", "storageMutationControls",
            "acceptedSourceOperandChecks")):
        raise ValueError("Buffered recording must retain executed comparisons and mutation controls.")
    if not checks["canonicalImageMutations"] or not all(c["rejected"] is True for c in checks["canonicalImageMutations"]):
        raise ValueError("Buffered image mutation controls did not reject changed encodings.")
    cases = checks.get("typedConstructorCases", [])
    if ({case["imageId"] for case in cases} != set(image_by_id) or
            len(cases) != len(images) or not all(case["passed"] is True for case in cases)):
        raise ValueError("Buffered images must match their executed typed constructor exports.")


def bundle(*, refresh_receipts: bool = False) -> tuple[str, dict]:
    content = json.loads((EXPLORER / "content.json").read_text())
    proofs = content.get("executionProofs", [])
    if ({p["id"] for p in proofs} != {"spi", "i2c"} or len(proofs) != 2 or
            any(not p.get("sources") or any(not p.get(key) for key in ("name", "scope", "proved", "open"))
                for p in proofs)):
        raise ValueError("Explorer requires both scoped source/interpreter proofs and their open state relations.")
    trace = json.loads((EXPLORER / "uart-trace.json").read_text())
    recordings = large_recordings()
    protocol_traces = [
        *json.loads((EXPLORER / "spi-traces.json").read_text())["traces"],
        *recordings["i2c-traces.json"]["traces"],
    ]
    buffered_session = recordings["buffered-session.json"]
    source_revision = revision()
    for recording in [trace, *protocol_traces]:
        validate_recording(recording)
    validate_buffered_session(buffered_session)
    if len({t["id"] for t in [trace, *protocol_traces]}) != 9:
        raise ValueError("Explorer requires unique UART, four SPI and four I2C recordings.")
    receipts = recording_receipts(recordings)
    if not refresh_receipts:
        verify_receipts(receipts)
    sources = {}
    path_sources = [{"path": "docs/architecture.md", "start": 84, "end": 110, "label": "Hardware and program paths"}]
    revision_files = {}
    for ref in references([content, trace, protocol_traces, buffered_session, path_sources]):
        path = (ROOT / ref["path"]).resolve()
        if not path.is_relative_to(ROOT) or not path.is_file():
            raise ValueError(f"Missing or invalid source: {ref['path']}")
        lines = path.read_text().splitlines()
        start, end = ref["start"], ref["end"]
        if not isinstance(start, int) or not isinstance(end, int) or not 1 <= start <= end <= len(lines):
            raise ValueError(f"Invalid source range: {ref}")
        key = f"{ref['path']}:{start}:{end}"
        if ref["path"] not in revision_files:
            original = subprocess.run(
                ["git", "show", f"{source_revision}:{ref['path']}"],
                cwd=ROOT, capture_output=True, check=False,
            )
            revision_files[ref["path"]] = original.returncode == 0 and original.stdout == path.read_bytes()
        sources[key] = {
            **ref,
            "text": "\n".join(lines[start - 1 : end]),
            "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
            "atRevision": revision_files[ref["path"]],
        }
    for target in content["targets"]:
        node_ids = {node["id"] for node in target["nodes"]}
        if len(node_ids) != len(target["nodes"]):
            raise ValueError(f"Duplicate components in {target['id']}")
        for edge in target["edges"]:
            if edge["from"] not in node_ids or edge["to"] not in node_ids:
                raise ValueError(f"Unknown component in connection: {edge}")
    payload = {
        **content,
        "trace": trace,
        "protocolTraces": protocol_traces,
        "bufferedSession": buffered_session,
        "sources": sources,
        "pathSources": path_sources,
        "snapshot": {
            "revision": source_revision,
            "revisionOnRemote": revision_on_remote(source_revision),
            "generatedAt": datetime.now(timezone.utc).isoformat(timespec="seconds"),
            "repository": "https://github.com/attilio-castano/pinwheel",
            "traceSha256": hashlib.sha256((EXPLORER / "uart-trace.json").read_bytes()).hexdigest(),
            "recordingHashes": {
                **{name: hashlib.sha256((EXPLORER / name).read_bytes()).hexdigest()
                    for name in ("uart-trace.json", "spi-traces.json")},
                **{name: receipt["sha256"] for name, receipt in receipts["recordings"].items()},
            },
            "recordingDigestConventions": {
                "uart-trace.json": "sha256-file-bytes",
                "spi-traces.json": "sha256-file-bytes",
                **{name: SEMANTIC_DIGEST for name in LARGE_RECORDINGS},
            },
        },
    }
    encoded = json.dumps(payload, ensure_ascii=False, separators=(",", ":"))
    encoded = encoded.replace("<", "\\u003c").replace("\u2028", "\\u2028").replace("\u2029", "\\u2029")
    template = (EXPLORER / "explorer.template.html").read_text()
    if template.count("__PINWHEEL_DATA__") != 1:
        raise ValueError("Explorer template must have exactly one data placeholder.")
    return template.replace("__PINWHEEL_DATA__", encoded), receipts


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument("--check", action="store_true", help="Validate inputs and committed recording receipts without writing")
    modes.add_argument("--refresh-receipts", action="store_true",
        help="Validate recordings and source bytes, then update their receipts and standalone page")
    args = parser.parse_args()
    page, receipts = bundle(refresh_receipts=args.refresh_receipts)
    if args.check:
        print("Explorer inputs, trace identity and source references are valid.")
    else:
        if args.refresh_receipts:
            (EXPLORER / "recordings.json").write_text(json.dumps(receipts,
                ensure_ascii=False, allow_nan=False, sort_keys=True, indent=2) + "\n")
        output = EXPLORER / "index.html"
        output.write_text(page)
        print(f"Built {output.relative_to(ROOT)} ({len(page.encode()):,} bytes).")


if __name__ == "__main__":
    main()
