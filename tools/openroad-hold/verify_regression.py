"""Check observed native failures, timing, and protected circuit readbacks."""
import hashlib
import json
import re
import sys
from pathlib import Path


def verify(out):
    out = Path(out)
    records = json.loads((out / "commands.json").read_text())
    cases = {"all_protected", "mixed_passing", "mixed_failing", "unprotected"}
    expected = {(c, i) for c in cases for i in ["native", "original", "patched"]}
    if len(records) != len(expected) or {(r["case"], r["implementation"]) for r in records} != expected:
        raise ValueError("Incomplete native regression matrix")

    def snapshot(path):
        result = {}
        for line in path.read_text().splitlines():
            fields = line.split()
            size = 2 if fields[0] == "instance" else 3
            key = tuple(fields[:size])
            if key in result or fields[0] not in ("instance", "pin"):
                raise ValueError("Malformed circuit snapshot")
            result[key] = " ".join(fields[size:])
        return result

    def slacks(text):
        found = re.findall(r"Endpoint: (\w+).*?([-\d.]+)\s+slack \((?:MET|VIOLATED)\)", text, re.S)
        if len(found) != len(dict(found)) or not found:
            raise ValueError("Missing or repeated endpoint timing")
        return {n: float(s) for n, s in found}

    outcomes = {}
    for record in records:
        case, impl = record["case"], record["implementation"]
        folder = out / f"{case}-{impl}"
        log = (folder / "run.log").read_text()
        if hashlib.sha256((folder / "run.tcl").read_bytes()).hexdigest() != record["script_sha256"]:
            raise ValueError("Changed executed regression script")
        before = snapshot(folder / "before.txt")
        initial = slacks(log.split("PINWHEEL_BEFORE\n")[1].split("PINWHEEL_REPAIR\n")[0])
        should_fail = impl != "patched" and case != "unprotected"
        if should_fail:
            if record["returncode"] == 0 or "RSZ-3015" not in log or "RSZ-3009" not in log or (folder / "after.txt").exists():
                raise ValueError("Original optimizer did not reproduce the empty-load failure")
            outcomes[f"{case}-{impl}"] = dict(expected_empty_load_failure=True, before_slack_ns=initial)
            continue
        if record["returncode"] or "RSZ-3015" in log or "RSZ-3009" in log:
            raise ValueError("Unexpected optimizer failure")
        after = snapshot(folder / "after.txt")
        final = slacks(log.split("PINWHEEL_AFTER\n")[1])
        old_instances = {k[1] for k in before if k[0] == "instance"}
        new_instances = {k[1] for k in after if k[0] == "instance"} - old_instances
        if any(after.get(k) != v for k, v in before.items() if k[0] == "instance" or k[1] in record["protected"]):
            raise ValueError("Changed original cell geometry or protected connectivity")
        if case in ("all_protected", "mixed_passing"):
            if after != before or final != initial or not initial["keep0"] < 0.2:
                raise ValueError("Protected-only timing failure was modified or hidden")
            if case == "mixed_passing" and not initial["keep1"] > 0.2:
                raise ValueError("Mixed-load fixture did not distinguish passing editable branch")
        else:
            if len(new_instances) != 8 or not initial["keep1"] < 0.2 <= final["keep1"]:
                raise ValueError("Editable hold path was not repaired")
            for name in new_instances:
                if not after[("instance", name)].startswith("CLKBUF_X1 "):
                    raise ValueError("Unexpected inserted cell")
            if case == "mixed_failing":
                if final["keep0"] != initial["keep0"]:
                    raise ValueError("Protected branch timing changed")
                # The only new path is a noninverting chain from d to branch0/A.
                outputs = {after[("pin", n, "Z")]: n for n in new_instances}
                net = after[("pin", "branch0", "A")]
                seen = set()
                while net != "d":
                    if net not in outputs or outputs[net] in seen:
                        raise ValueError("Unexpected delay-chain connection")
                    name = outputs[net]
                    seen.add(name)
                    net = after[("pin", name, "A")]
                if seen != new_instances:
                    raise ValueError("New cells outside the editable branch")
        outcomes[f"{case}-{impl}"] = dict(before_slack_ns=initial, after_slack_ns=final,
                                           added_buffers=len(new_instances), protected_unchanged=True)
    for case in cases:
        a = out / f"{case}-native"
        b = out / f"{case}-original"
        if (a / "before.txt").read_bytes() != (b / "before.txt").read_bytes():
            raise ValueError("Native and extension started from different circuits")
        if case == "unprotected":
            for impl in ["original", "patched"]:
                other = out / f"{case}-{impl}"
                for name in ["after.txt", "after.v"]:
                    if (a / name).read_bytes() != (other / name).read_bytes():
                        raise ValueError("Unprotected control differs from native executable")
                if outcomes[f"{case}-native"] != outcomes[f"{case}-{impl}"]:
                    raise ValueError("Unprotected control timing differs")
    return dict(status="passed", cases=outcomes, native_extension_control="identical circuit and timing",
                scope="Pinned native regression; residual protected hold shortfalls remain reported")


if __name__ == "__main__":
    result = verify(sys.argv[1])
    print(json.dumps(result, indent=2))
