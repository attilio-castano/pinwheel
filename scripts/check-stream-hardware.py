#!/usr/bin/env python3
"""Fresh-source stream milestone: proofs, two RTL forms, replay and certificates."""
from __future__ import annotations

import argparse
import csv
import hashlib
import itertools
import json
import os
from pathlib import Path
import random
import re
import subprocess
import time

import generic_stream_readback as readback

ROOT = Path(__file__).resolve().parents[1]
TOOLS = ROOT / "build/tools"
CIRCT = TOOLS / "firtool-1.159.0/bin/circt-opt"
CAD = TOOLS / "oss-cad-suite/bin"


class Run:
    def __init__(self, root):
        self.root, self.commands = root, []

    def command(self, args, log, *, timeout=180, env=None, stdout=None):
        start = time.monotonic()
        result = subprocess.run(list(map(str, args)), cwd=ROOT, env=env,
                                capture_output=True, text=True, timeout=timeout)
        log.write_text(result.stdout + result.stderr)
        self.commands.append({"argv": list(map(str, args)), "exit_code": result.returncode,
                              "seconds": time.monotonic() - start, "log": str(log.relative_to(self.root))})
        if result.returncode:
            raise RuntimeError(f"{log}: command failed\n{result.stdout[-1500:]}{result.stderr[-1500:]}")
        if stdout:
            stdout.write_text(result.stdout)
        return result.stdout

    def lean(self, directory, module):
        env = dict(os.environ)
        env["LEAN_PATH"] = str(directory) + os.pathsep + str(ROOT / ".lake/build/lib/lean")
        self.command(["lake", "env", "lean", "-DwarningAsError=true", "-o", directory / f"{module}.olean",
                      directory / f"{module}.lean"], directory / f"{module}.log", env=env, timeout=300)


def stimuli(width, depth, stages, seed):
    rng = random.Random(seed)
    mask = (1 << (2 * width)) - 1
    rows = [(1, 0, 0, 0)]
    # Empty/no-stall phase: every transfer has exactly L+1 cycles of latency.
    rows += [(0, 1, 1, x & mask) for x in range(48)]
    rows += [(0, 0, 1, mask)] * (depth + stages + 3)
    # Fill, long stall, full replacement, then drain.
    rows += [(1, 1, 0, mask)]
    rows += [(0, 1, 0, mask)] * (depth + stages + 8)
    rows += [(0, 1, 1, mask)] * 32
    rows += [(0, 0, 1, mask)] * (depth + stages + 3)
    for _ in range(400):
        rows.append((int(rng.randrange(43) == 0), rng.randrange(2), rng.randrange(2), rng.getrandbits(2 * width)))
    rows += [(0, 0, 1, mask)] * (depth + stages + 3)
    return rows


def testbench(width, directory):
    return f"""module tb;
reg clk = 0, reset = 1, in_valid = 0, out_ready = 0;
reg [{2*width-1}:0] in_data = 0;
wire in_ready, out_valid; wire [{width-1}:0] out_data;
pinwheel_stream dut(.*);
integer f, rc, cycle = 0;
reg pre_ready, pre_valid; reg [{width-1}:0] pre_data;
initial begin
  if ($test$plusargs("waves")) begin $dumpfile("{directory / 'waves.vcd'}"); $dumpvars(0, tb); end
  f = $fopen("{directory / 'stimulus.csv'}", "r");
  if (!f) $fatal(1, "missing stimulus");
  while (!$feof(f)) begin
    clk = 0;
    rc = $fscanf(f, "%d,%d,%d,%d\\n", reset, in_valid, out_ready, in_data);
    if (rc == 4) begin
      #5; pre_ready = in_ready; pre_valid = out_valid; pre_data = out_data;
      clk = 1; #5;
      $display("%0d,%0d,%0d,%0d,%0d,%0d,%0d", cycle, pre_ready, pre_valid, pre_data, in_ready, out_valid, out_data);
      cycle = cycle + 1;
    end
  end
  $finish;
end
endmodule
"""


def read_rows(path):
    # Icarus may append a $finish diagnostic after the CSV observations.
    return [tuple(map(int, row)) for row in csv.reader(path.read_text().splitlines())
            if len(row) == 7 and row[0].isdigit()]


def scoreboard(stimulus, observations, width, stages):
    if len(stimulus) != len(observations):
        raise AssertionError("Missing or extra observed edges")
    pending = []
    accepted = emitted = 0
    mask = (1 << width) - 1
    previous = None
    for index, ((rst, valid, ready, data), row) in enumerate(zip(stimulus, observations, strict=True)):
        cycle, ir, ov, od, _, _, _ = row
        if cycle != index or ir not in (0, 1) or ov not in (0, 1):
            raise AssertionError("Invalid cycle or control observation")
        if rst:
            if ir or ov:
                raise AssertionError("Transfer enabled during reset")
            pending.clear()
        else:
            if previous and previous[0] and not previous[1] and (ov, od) != (previous[0], previous[2]):
                raise AssertionError(f"Stalled output changed at edge {cycle}")
            # Dequeue first: a newly accepted input cannot bypass the registered FIFO.
            if ready and ov:
                if not pending or od != pending[0][0]:
                    raise AssertionError(f"Incorrect/duplicated/reordered result at edge {cycle}")
                _, birth = pending.pop(0)
                if 1 <= birth <= 48 and cycle != birth + stages + 1:
                    raise AssertionError("No-stall latency differs from L+1")
                emitted += 1
            if valid and ir:
                pending.append((((data & mask) + (data >> width)) & mask, cycle))
                accepted += 1
        previous = (ov, ready, od)
    if pending:
        raise AssertionError("Drain did not complete")
    return {"accepted_across_epochs": accepted, "emitted_across_epochs": emitted}


def lower(run, source, target):
    run.command([CIRCT, source, "--canonicalize", "--lower-seq-to-sv", "--lower-hw-to-sv",
                 "--hw-legalize-modules", "--export-verilog", "-o", "/dev/null"],
                target.with_suffix(".circt.log"), stdout=target)


def import_rtl(run, rtl, directory, descriptor, hierarchical):
    script = directory / "import.ys"
    script.write_text(f'read_verilog -sv "{rtl}"\nhierarchy -check -top pinwheel_stream\n'
                      f'flatten -noscopeinfo\nproc\nopt_clean\ncheck -assert\nwrite_json "{directory / "raw.json"}"\n')
    run.command([CAD / "yosys", "-Q", "-T", "-s", script], directory / "yosys.log")
    readback.prepare_json(directory / "raw.json", directory / "import.json", descriptor, hierarchical)


def configuration(run, config, seed):
    width, depth, stages = config
    directory = run.root / f"w{width}-d{depth}-l{stages}"
    directory.mkdir()
    stimulus = stimuli(width, depth, stages, seed)
    (directory / "stimulus.csv").write_text("".join(",".join(map(str, row)) + "\n" for row in stimulus))
    run.command([ROOT / ".lake/build/bin/stream_example", *config, directory, directory / "stimulus.csv"],
                directory / "lean-simulation.log")
    descriptor = json.loads((directory / "interface.json").read_text())
    lower(run, directory / "flat.mlir", directory / "flat.sv")
    for name in descriptor["leaves"]:
        lower(run, directory / f"{name}.mlir", directory / f"{name}.sv")
    hierarchy_sources = sorted(directory.glob("stream_core*.sv")) + [directory / "hierarchy_top.sv"]
    (directory / "hierarchical.sv").write_text("\n".join(p.read_text() for p in hierarchy_sources))
    (directory / "tb.sv").write_text(testbench(width, directory))
    expected = read_rows(directory / "lean.csv")
    result = {"configuration": config, "edges": len(stimulus), "forms": {}}
    for form in ("flat", "hierarchical"):
        artifact = directory / f"{form}.sv"
        binary = directory / f"{form}.vvp"
        run.command([CAD / "iverilog", "-g2012", "-s", "tb", "-o", binary, artifact, directory / "tb.sv"],
                    directory / f"{form}-compile.log")
        run.command([CAD / "vvp", binary], directory / f"{form}-simulate.log", stdout=directory / f"{form}.csv")
        observations = read_rows(directory / f"{form}.csv")
        if observations != expected:
            run.command([CAD / "vvp", binary, "+waves"], directory / f"{form}-waves.log")
            raise AssertionError(f"{form}: RTL differs from Lean; see {directory / 'waves.vcd'}")
        accounting = scoreboard(stimulus, observations, width, stages)
        proofdir = directory / form
        proofdir.mkdir()
        import_rtl(run, artifact, proofdir, descriptor, form == "hierarchical")
        modules, evidence = readback.generate(proofdir, config, descriptor, directory / "flat.mlir",
                                              proofdir / "import.json", CAD / "z3")
        for module in modules:
            run.lean(proofdir, module)
        result["forms"][form] = {**accounting, **evidence,
            "sha256": hashlib.sha256(artifact.read_bytes()).hexdigest()}
    print(f"PASS {width}/{depth}/{stages}: {len(stimulus)} edges; flat and hierarchical certificates", flush=True)
    return result


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def negative_controls(run, config):
    """Fresh malformed RTL must fail at the kernel proof boundary."""
    width, depth, stages = config
    source = run.root / f"w{width}-d{depth}-l{stages}"
    descriptor = json.loads((source / "interface.json").read_text())
    original = (source / "flat.sv").read_text()
    results = []
    for label, pattern in (("wrong-output", r"(assign out_data =)(.*?);"),
                           ("wrong-ready", r"(assign in_ready =)(.*?);"),
                           ("wrong-state-update", r"(r_state_0 <=)(.*?);")):
        directory = run.root / label
        directory.mkdir()
        changed, count = re.subn(pattern, lambda m: m[1] + " ~(" + m[2] + ");", original, flags=re.S)
        if count != 1:
            raise AssertionError(f"Mutation {label} did not change exactly one endpoint")
        artifact = directory / "mutated.sv"
        artifact.write_text(changed)
        import_rtl(run, artifact, directory, descriptor, False)
        modules, _ = readback.generate(directory, config, descriptor, source / "flat.mlir",
                                       directory / "import.json", CAD / "z3")
        rejected = None
        for module in modules:
            try:
                run.lean(directory, module)
            except RuntimeError:
                if module not in ("LocalProofs", "Links", "Proof"):
                    raise
                rejected = module
                break
        if rejected is None:
            raise AssertionError(f"Kernel accepted mutation: {label}")
        results.append({"mutation": label, "rejected_by": rejected,
                        "sha256": sha(artifact)})
    return results


def provenance():
    sources = list((ROOT / "Pinwheel").rglob("*.lean")) + [
        ROOT / name for name in ("lakefile.toml", "lean-toolchain", "test/StreamExample.lean",
        "test/StreamAudit.lean", "test/StreamLaws.lean", "test/test_generic_stream.py",
        "scripts/check-stream-hardware.py", "scripts/generic_stream_readback.py",
        "scripts/backend_readback.py", "scripts/install-hardware-tools.py")]
    return {"sources": {str(p.relative_to(ROOT)): sha(p) for p in sorted(sources)},
            "tools": {str(p.relative_to(ROOT)): sha(p) for p in
                      [CIRCT, CAD / "yosys", CAD / "iverilog", CAD / "vvp", CAD / "z3"]}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tag", required=True)
    parser.add_argument("--config", action="append", help="WIDTH,DEPTH,STAGES; default: full 27-configuration matrix")
    args = parser.parse_args()
    if not args.tag or any(c not in "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789-_" for c in args.tag):
        parser.error("tag must contain letters, numbers, hyphens or underscores")
    configs = [tuple(map(int, c.split(","))) for c in args.config] if args.config else list(
        itertools.product((1, 8, 17), (1, 3, 8), (1, 2, 4)))
    if any(len(c) != 3 or min(c) <= 0 for c in configs):
        parser.error("all configurations require three positive integers")
    root = ROOT / "build/stream-hardware" / args.tag
    root.mkdir(parents=True, exist_ok=False)
    run = Run(root)
    report = {"schema": 1, "status": "running", "configurations": [], "commands": run.commands,
              "boundary": "Two-state synchronous RTL; trusted Yosys frontend/JSON interpretation. No physical qualification."}
    try:
        report["provenance"] = provenance()
        run.command(["lake", "build", "stream_example", "Pinwheel.Hardware.Stream.Diamond"], root / "build.log", timeout=300)
        run.command(["lake", "env", "lean", "-DwarningAsError=true", "test/StreamAudit.lean"], root / "audit.log")
        run.command(["lake", "env", "lean", "test/StreamLaws.lean"], root / "laws.log")
        run.command(["python3", "-B", "-m", "unittest", "discover", "-s", "test", "-p", "test_generic_stream.py", "-v"],
                    root / "negative-unit.log")
        for config in configs:
            report["configurations"].append(configuration(run, config, 0x535452))
        report["negative_controls"] = negative_controls(run, configs[0])
        if provenance() != report["provenance"]:
            raise RuntimeError("Sources or tools changed during the validation run")
        report["artifacts"] = {str(p.relative_to(root)): sha(p) for p in sorted(root.rglob("*"))
                               if p.is_file() and p.suffix in (".lean", ".json", ".mlir", ".sv", ".csv")}
        report["status"] = "passed"
    except BaseException as error:
        report["status"], report["error"] = "failed", str(error)
        raise
    finally:
        (root / "report.json").write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
