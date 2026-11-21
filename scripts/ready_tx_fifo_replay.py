"""Independent Ready protocol and boundary replays for the TX FIFO refactor."""

from dataclasses import asdict
from pathlib import Path
import struct

from streaming_8x4_ethernet import replay_schedules
from streaming_8x4_spi_modes import exchange, run_cases
from streaming_ready_compile import i2c_image, spi_image
from streaming_ready_peers import StreamingI2cPeer, payloads
from streaming_ready_transport import ReadyHost, pack_read, project
from streaming_ready_wire_cases import check_deadline_alignment, check_i2c_cases, require, run_i2c_case, run_i2c_cases
from streaming_ready_wire_controls import check_controls, check_late_custody, observe, prepare_controls, run_ready_controls
from streaming_rtl import QuadRTL
from streaming_transport import Code, Opcode, QuadTransport
from streaming_wire_cases import EdgeTrace


SHORT_BUDGET = 19
LATE_SLOT = 42
LATE_CASE = f"i2c-late-slot-{LATE_SLOT}"
LATE_BUDGETS = (31, SHORT_BUDGET)
RELOAD_TRACE = "i2c-to-spi.bin"


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
    late = replay_late(vvp, executable, out / "late", image, budget=SHORT_BUDGET)
    return dict(budget=SHORT_BUDGET, last_poll=last, late_poll=late)


def replay_late(vvp, executable, out, image, *, budget, deadline_slot=11):
    late = observe(vvp, executable, out, depth=2, profile="late", image=image, deadline_slot=deadline_slot)
    check_late_custody(late, deadline_slot=deadline_slot)
    observed = late["observation"]
    check_deadline_alignment(observed["deadline_alignment"], observed["deadline_trace"],
                             budget=budget, late=True, deadline_slot=deadline_slot)
    return late


def replay_later_slot(vvp, executable, out):
    results = {}
    for budget in LATE_BUDGETS:
        name = f"budget-{budget}"
        image = i2c_image(wait_budget=budget, stretch_bound=budget - 3)
        late = replay_late(vvp, executable, out / name, image, budget=budget, deadline_slot=LATE_SLOT)
        terminal = late["observation"]["terminal_reply"]
        if (terminal["rx_start"], terminal["rx_valid"]) != (32, LATE_SLOT - 32):
            raise RuntimeError("Later fault did not drain one full RX word followed by the exact partial word")
        results[name] = dict(budget=budget, image_words=list(image.words), late_poll=late)
    return results


def replay_protocol_reload(vvp, executable, path):
    """Use two successive images and one physical reset on the same pin transport."""
    i2c, spi = i2c_image(), spi_image(mode=0)
    require(len(i2c.words) == 7 and len(spi.words) == 4, "Expected a shorter SPI reload over the I2C image")
    read_plan = pack_read(0x52, 64)
    read_data = payloads()[1]
    spi_count = 33
    trace = EdgeTrace(path)
    try:
        with QuadRTL(vvp, executable, record_limit=0, record_sink=trace) as rtl:
            transport = QuadTransport(rtl)
            host = ReadyHost(transport, depth=2)
            host.initialize()
            first_image = host.load(i2c)
            i2c_loaded = rtl.cycle
            peer = StreamingI2cPeer(read_plan, read_data, profile="varying")
            rtl.device = peer
            pending = first_image.submit(read_plan.tx_bits, bit_count=read_plan.bit_count)
            transport.idle(64)
            terminal = pending.wait(max_exchanges=100)
            read = project(read_plan, pending.rx_bits, fault=terminal.fault)
            require(read.payload_valid and read.data == read_data, "I2C reload predecessor returned the wrong payload")
            i2c_result = peer.check(pending.rx_bits, fault=terminal.fault, require_host_stall=True)
            released = pending.release()
            require(pending.last.rx_start == read_plan.bit_count and pending.last.rx_valid == 0,
                    "I2C reload predecessor did not acknowledge its exact RX count")
            i2c_released = rtl.cycle
            rtl.device = None

            second_image = host.load(spi)
            stale_start = rtl.cycle
            stale = transport.request(Opcode.START, expected_generation=first_image.generation, bit_count=spi_count)
            stale_end = rtl.cycle
            require(stale.code is Code.REJECTED and stale.valid and not stale.busy and not stale.retained and
                    not stale.fault and not stale.tx_accepted and not stale.rx_valid and not stale.rx_queued and
                    (stale.generation, stale.transfer) == (second_image.generation, released.transfer),
                    "Stale-generation START acquired custody or changed the current owner tag")
            spi_result = exchange(rtl, transport, second_image, 0, spi_count)
            require((first_image.generation, second_image.generation) == (1, 2) and
                    (released.tag, spi_result["owner_tag"]) == (0x10001, 0x20002),
                    "Reload did not advance the image and transfer IDs exactly once")
            commands = transport.opcode_counts
            require(commands[Opcode.WRITE] == len(i2c.words) + len(spi.words) and
                    commands[Opcode.COMMIT] == 2 and commands[Opcode.START] == 3 and
                    commands[Opcode.RELEASE] == 2 and commands[Opcode.WARM_RESET] == 0,
                    "Reload used an unexpected reset or image/ownership command sequence")
    finally:
        recorded = trace.close()

    edges = list(struct.iter_unpack("<I16B", path.read_bytes()))
    reset_edges = [edge[0] for edge in edges if edge[1]]
    require(reset_edges == [1] and len(edges) == recorded["edges"] == rtl.cycle,
            "Reload trace does not cover one cold reset and every physical edge")
    idle = edges[stale_start - 1][11:14]
    require(idle == (0, i2c.idle_levels, i2c.idle_enabled) and stale_start < stale_end and
            all(edge[11:14] == idle for edge in edges[stale_start:stale_end]),
            "Stale-generation START disturbed the current idle pads or physical BUSY")
    return dict(i2c=dict(image_words=list(i2c.words), generation=first_image.generation, peer=i2c_result,
                        owner_tag=released.tag, acknowledged_bits=pending.last.rx_start,
                        payload_hex=read.data.hex(), load_end_edge=i2c_loaded, release_end_edge=i2c_released),
                spi=dict(image_words=list(spi.words), generation=second_image.generation, **spi_result),
                stale_start=dict(expected_generation=first_image.generation, receipt=asdict(stale),
                                 first_edge=stale_start + 1, end_edge=stale_end, idle_pins_preserved=True,
                                 idle_pins=dict(busy=idle[0], levels=idle[1], enabled=idle[2])),
                command_counts={opcode.name: commands[opcode] for opcode in Opcode if commands[opcode]},
                cold_reset_edges=reset_edges, warm_reset_commands=commands[Opcode.WARM_RESET],
                trace=recorded, exit_code=rtl.process.returncode)


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
    later = replay_later_slot(tools["vvp"], bridge, out / LATE_CASE)
    ethernet = replay_schedules(tools["vvp"], bridge, out / "ethernet.bin")
    reloaded = replay_protocol_reload(tools["vvp"], bridge, out / RELOAD_TRACE)
    return dict(spi=spi, i2c=i2c, i2c_controls=controls, i2c_short_budget=short, i2c_to_spi=reloaded,
                i2c_late_slot_42=later, ethernet=ethernet, full_boundary_passed=True)


def compare(ring: Path, shift: Path):
    """Require byte-for-byte equality on every unchanged public-pin case."""
    paths = list(map(Path, ("spi.bin", "ethernet.bin", RELOAD_TRACE, "i2c-controls/unchanged-late/wire.bin",
                           "i2c-short-budget/lastpoll/wire.bin", "i2c-short-budget/late/wire.bin")))
    paths.extend(Path(LATE_CASE) / f"budget-{budget}" / "wire.bin" for budget in LATE_BUDGETS)
    paths.extend(sorted(path.relative_to(ring) for path in (ring / "i2c").glob("*/wire.bin")))
    if len(paths) != 18:
        raise RuntimeError("The Ready TX FIFO replay omitted an expected pin trace")
    for path in paths:
        if (ring / path).read_bytes() != (shift / path).read_bytes():
            raise RuntimeError(f"TX FIFO replacement changed public pin trace {path}")
    return [str(path) for path in paths]
