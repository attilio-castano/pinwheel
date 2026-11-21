"""Independent Ready protocol and boundary replays for the TX FIFO refactor."""

from pathlib import Path

from streaming_8x4_ethernet import replay_schedules
from streaming_8x4_spi_modes import run_cases
from streaming_ready_compile import i2c_image, spi_image
from streaming_ready_wire_cases import check_deadline_alignment, check_i2c_cases, run_i2c_case, run_i2c_cases
from streaming_ready_wire_controls import check_controls, check_late_custody, observe, prepare_controls, run_ready_controls


SHORT_BUDGET = 19


def testbench(assembly):
    """Attempt a third push on the first reservation edge of a full queue."""
    inputs, outputs = assembly["inputs"], assembly["outputs"]
    declarations = ["reg clk = 0;"]
    declarations.extend(f'reg [{p["width"] - 1}:0] {p["name"]} = 0;' for p in inputs)
    declarations.extend(f'wire [{p["width"] - 1}:0] {p["name"]};' for p in outputs)
    header = "\n".join(declarations)
    ports = ", ".join(f'.{p["name"]}({p["name"]})' for p in inputs + outputs)
    image = spi_image(mode=0)
    writes = "\n".join(
        f"  address = 6'd{i}; word = 64'd{word}; tick();"
        for i, word in enumerate(image.words)
    )
    return f"""module tb;
{header}
{assembly["module"]} dut(.clk(clk), {ports});

task tick;
  begin
    #1; clk = 1; #1; clk = 0; #1;
  end
endtask

integer waited;
initial begin
  initialize = 1; tick();
  initialize = 0;
  command = 1;
{writes}
  command = 2; count = {len(image.words)}; idle_levels = {image.idle_levels};
  idle_enabled = {image.idle_enabled}; tick();
  command = 3; expected_generation = 1; start_count = 96; tick();

  command = 0; expected_transfer = 1; tx_push = 1; tx_bits = 32;
  tx_data = 32'h80000000; tick();
  tx_data = 32'h40000000; tick();
  tx_push = 0;
  for (waited = 0; phase !== 3'd2 && waited < 32; waited = waited + 1)
    tick();
  if (phase !== 3'd2 || tx_queued !== 4'd2 || tx_accepted !== 16'd64 ||
      tx_consumed !== 16'd0 || waiting_tx !== 1'b0)
    $fatal(1, "fixture failed to reach a full first reservation");

  tx_push = 1; tx_data = 32'h08000000;
  #1;
  if (rejected !== 1'b1)
    $fatal(1, "admitted a push into a queue full at the start of the edge");
  tick();
  if (tx_queued !== 4'd1 || tx_accepted !== 16'd64 || tx_consumed !== 16'd1)
    $fatal(1, "full edge failed to pop exactly the old head without admitting the push");
  $display("Ready full push/pop preserved");
  $finish;
end
endmodule
"""


def replay_short_budget(vvp, executable, out):
    image = i2c_image(wait_budget=SHORT_BUDGET, stretch_bound=SHORT_BUDGET - 3)
    last = run_i2c_case(vvp, executable, out / "lastpoll", depth=2, direction="read",
                        profile="lastpoll", image=image)
    if not last["passed"]:
        raise RuntimeError(f"Short-budget last-poll read failed: {last['error']}")
    peer = last["peer"]
    check_deadline_alignment(peer["deadline_alignment"], peer["deadline_trace"], budget=SHORT_BUDGET)
    late = observe(vvp, executable, out / "late", depth=2, profile="late", image=image)
    check_late_custody(late)
    observed = late["observation"]
    check_deadline_alignment(observed["deadline_alignment"], observed["deadline_trace"],
                             budget=SHORT_BUDGET, late=True)
    return dict(budget=SHORT_BUDGET, last_poll=last, late_poll=late)


def replay(run, tools, out, assembly, sources):
    core = sources[0]
    out.mkdir(parents=True, exist_ok=False)
    directed = out / "full-boundary.sv"
    directed.write_text(testbench(assembly))
    executable = out / "full-boundary.vvp"
    run([tools["iverilog"], "-g2012", "-s", "tb", "-o", executable, core, directed], "full-boundary-compile")
    result = run([tools["vvp"], executable], "full-boundary-run")
    if "Ready full push/pop preserved" not in result:
        raise RuntimeError("Full-queue pre-edge admission check did not run")

    bridge = out / "bridge.vvp"
    run([tools["iverilog"], "-g2012", "-s", "streaming_quad_host_bridge", "-o", bridge, *sources],
        "bridge-compile")
    spi = run_cases(tools["vvp"], bridge, out / "spi.bin")
    i2c = run_i2c_cases(tools["vvp"], bridge, out / "i2c", depth=2)
    check_i2c_cases(i2c)
    mutants = prepare_controls(sources, out / "mutants", tools, run)
    controls = run_ready_controls(tools["vvp"], bridge, mutants, out / "i2c-controls", depth=2)
    check_controls(controls)
    short = replay_short_budget(tools["vvp"], bridge, out / "i2c-short-budget")
    ethernet = replay_schedules(tools["vvp"], bridge, out / "ethernet.bin")
    return dict(spi=spi, i2c=i2c, i2c_controls=controls, i2c_short_budget=short,
                ethernet=ethernet, full_boundary_passed=True)


def compare(ring: Path, shift: Path):
    """Require byte-for-byte equality on every unchanged public-pin case."""
    paths = list(map(Path, ("spi.bin", "ethernet.bin", "i2c-controls/unchanged-late/wire.bin",
                           "i2c-short-budget/lastpoll/wire.bin", "i2c-short-budget/late/wire.bin")))
    paths.extend(sorted(path.relative_to(ring) for path in (ring / "i2c").glob("*/wire.bin")))
    if len(paths) != 15:
        raise RuntimeError("The Ready TX FIFO replay omitted an expected pin trace")
    for path in paths:
        if (ring / path).read_bytes() != (shift / path).read_bytes():
            raise RuntimeError(f"TX FIFO replacement changed public pin trace {path}")
    return [str(path) for path in paths]
