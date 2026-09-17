#!/usr/bin/env python3
"""Independent immediate-commit/start and bank-switch tests for emitted RTL."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import runpy
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def vectors():
    oracle = runpy.run_path(str(ROOT / "scripts/loader-vectors.py"))

    class Small(oracle["Atomic"]):
        def __init__(self):
            super().__init__()
            for image in self.images: image[32:64] = [4] * 32

        def edge(self, init=0, reset=0, command=0, data=0, incoming=0):
            fits = self.cursor < 32 or (data == 4 if self.cursor < 64 else data < 32 if self.cursor < 320 else True)
            super().edge(init, reset, 6 if command == 2 and not fits else command, data, incoming)
            self.rows[-1][2] = command

    m = Small()
    m.edge(init=1)
    pack, stream = oracle["pack"], oracle["stream"]
    transitions = []
    for levels in (1, 6, 3, 4):
        payload = stream([pack(dict(kind=0, levels=levels, enabled=7)), 4], 1, (levels ^ 7, 7))
        m.edge(command=1)
        for word in payload[:-1]: m.edge(command=2, data=word)
        m.edge(command=3)
        assert m.gates == [0, 0, 0, 1] and m.cursor == 321
        last_edge = len(m.rows)
        m.edge(command=2, data=payload[-1])
        m.edge(command=3)
        assert m.gates == [0, 1, 0, 0] and m.s[4:6] == [levels ^ 7, 7]
        bank = m.active
        m.edge(command=5)
        assert m.gates == [0, 0, 1, 0] and m.s[4:6] == [levels, 7] and m.s[1] == 0
        transitions.append({"last_upload_edge": last_edge, "commit_edge": last_edge + 1,
                            "start_edge": last_edge + 2, "bank": bank, "levels": levels})
        m.edge(command=3)
        assert m.gates == [0, 0, 0, 1] and m.s[0] == 5
    # Reset wins over an otherwise eligible commit, including on the last upload boundary.
    payload = stream([pack(dict(kind=0, levels=7, enabled=7)), 4], 1)
    m.edge(command=1)
    for word in payload: m.edge(command=2, data=word)
    bank = m.active
    m.edge(reset=1, command=3)
    assert m.active == bank and m.pending == 0 and m.cursor == 0
    m.edge(command=3)
    assert m.gates == [0, 0, 0, 1]
    m.edge(command=5)
    assert m.s[4] == 4
    m.edge(reset=1, command=5)
    assert m.s[0] == 0
    # Input-dependent branches on every edge, including self branches and busy commands.
    words = [pack(dict(kind=2, levels=p + 1, enabled=3, terminal=63,
                       entry=61, finish=2, sample=15, yes=1-p, no=p)) for p in range(2)]
    m.load("continuous-live-input-branches", words, 1)
    m.edge(command=5)
    for n in range(128):
        incoming = n % 4
        expected_pc = m.s[1] ^ (incoming >> 1)
        m.edge(incoming=incoming, command=n % 7 + 1, data=(1 << 64)-1)
        assert m.s[0] == 3 and m.s[1] == expected_pc and m.s[6] >> 15 == incoming & 1
        assert m.gates == [0, 0, 0, 1]
    return m.rows, {"edges": len(m.rows), "immediate_transitions": transitions,
                    "continuous_branch_edges": 128, "counters": dict(m.counters)}


def mutations(rtl):
    # Exchange only combinational bank reads; declarations and sequential writes retain their identities.
    count = 0
    def swap(match):
        nonlocal count
        text, replacements = re.subn(r"\br_bank([01])_(word|index)(\d+)\b",
            lambda m: f"r_bank{1-int(m[1])}_{m[2]}{m[3]}", match[2])
        count += replacements
        return match[1] + text + ";"
    wrong_bank = re.sub(r"(\bwire\s+(?:\[\d+:0\]\s+)?\w+\s*=)([^;]+);", swap, rtl)
    if count < 2: raise RuntimeError("Missing combinational bank-read mutation anchors")
    early, count = re.subn(r"\br_loader_cursor\s*==\s*9'h142", "r_loader_cursor == 9'h141", rtl)
    if count != 1: raise RuntimeError("Missing unique complete-upload comparator")
    stale, count = re.subn(r"(\br_cached_word\s*<=)[^;]+;", r"\1 r_cached_word;", rtl)
    if count != 1: raise RuntimeError("Missing unique cache-update register")
    return {"wrong-bank": wrong_bank, "early-commit": early, "stale-cache": stale}


def main(*, vector_factory=vectors, mutate=mutations, transform_tb=lambda text: text, extra_sources=()):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--control", type=Path, required=True)
    parser.add_argument("--candidate", type=Path, required=True)
    parser.add_argument("--testbench", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists(): raise RuntimeError("Preserve earlier regression evidence")
    out = args.output
    out.mkdir(parents=True)
    rows, coverage = vector_factory()
    (out / "vectors.txt").write_text("".join(" ".join(map(str, row)) + "\n" for row in rows))
    tb, count = re.subn(r'\$fopen\("[^"\n]+", "r"\)',
                       '$fopen("' + str((out / "vectors.txt").resolve()) + '", "r")', args.testbench.read_text())
    if count != 1: raise RuntimeError("Missing unique testbench vector input")
    tb = transform_tb(tb)
    (out / "tb.sv").write_text(tb)
    included = [ROOT / name for name in re.findall(r'`include "([^"]+)"', tb)]
    sources = [Path(__file__).resolve(), ROOT / "scripts/loader-vectors.py", ROOT / "scripts/reactive-core-vectors.py",
               ROOT / "scripts/execution-vectors.py", args.control, args.candidate, args.testbench, *included, *extra_sources]
    hashes = {str(p.resolve().relative_to(ROOT)): sha(p) for p in sources}
    suite = ROOT / "build/tools/oss-cad-suite/bin"
    commands = []
    candidate_mutants = mutate(args.candidate.read_text())
    for variant, path in (("control", args.control), ("candidate", args.candidate)):
        fixtures = {"positive": path.read_text()}
        if variant == "candidate": fixtures.update(candidate_mutants)
        for name, rtl in fixtures.items():
            label = variant + "-" + name
            design = out / f"{label}.sv"
            design.write_text(rtl)
            for step, command in (("compile", [suite / "iverilog", "-g2012", "-s", "loader_tb", "-o", out / f"{label}.vvp", design, out / "tb.sv"]),
                                  ("simulate", [suite / "vvp", out / f"{label}.vvp"])):
                started = time.monotonic()
                result = subprocess.run(list(map(str, command)), cwd=ROOT, capture_output=True, text=True, timeout=120)
                text = result.stdout + result.stderr
                (out / f"{label}-{step}.log").write_text(text)
                reject = step == "simulate" and name != "positive"
                if (reject and (result.returncode == 0 or "LOADER edge" not in text)) or (not reject and result.returncode):
                    raise RuntimeError(f"Unexpected {label} {step} result: {text[-2000:]}")
                commands.append({"argv": list(map(str, command)), "exit_code": result.returncode,
                                 "seconds": round(time.monotonic()-started, 3)})
            print(label + ": " + ("passed" if name == "positive" else "corruption rejected"), flush=True)
    if hashes != {str(p.resolve().relative_to(ROOT)): sha(p) for p in sources}:
        raise RuntimeError("Regression inputs changed")
    report = {"coverage": coverage, "mutations_rejected": list(candidate_mutants),
              "source_sha256": hashes, "commands": commands,
              "artifact_sha256": {p.name: sha(p) for p in out.iterdir() if p.is_file()},
              "boundary": "Independent cycle-by-cycle oracle and storage/cache observations with uninitialized RTL. "
                          "Both program banks are exercised; no timing or universal-equivalence claim."}
    (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__": main()
