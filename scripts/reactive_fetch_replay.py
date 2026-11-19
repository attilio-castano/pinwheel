"""Closed-loop I²C replay for the direct Reactive core's registered fetch cuts."""

from dataclasses import asdict, dataclass
import json
from pathlib import Path

from i2c_read_peers import I2CReadPeer
from pad_io import PadObservation
from pinwheel_host import Result
from pinwheel_sim import Simulation
from protocol_results import i2c_read_result
from validation_run import sha


ROOT = Path(__file__).resolve().parents[1]
MODULES = dict(baseline="pinwheel_reactive_direct", low="pinwheel_reactive_registered_low",
               late="pinwheel_reactive_registered_late")
PHASE_CYCLES = 4
ACK_SLOT = 8
ACK_HIGH_PC, ACK_LOW_PC = 36, 37


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def command(*, observe=False, start=False, write=False, bank=0, address=0, data=0):
    """Pack a setup command for the bridge's Simulation-compatible input."""
    return ((int(observe) << 12 | int(start) << 11 | int(write) << 10 |
             bank << 8 | address) << 64) | data


@dataclass(frozen=True)
class Edge:
    cycle: int
    pads: PadObservation

    @property
    def pc(self):
        return (self.pads.status >> 4) & 255

    @property
    def mode(self):
        return (self.pads.status >> 1) & 7

    @property
    def remaining(self):
        return (self.pads.status >> 12) & 255

    @property
    def samples(self):
        return (self.pads.status >> 20) & 65535

    @property
    def fetch_wait(self):
        return bool((self.pads.status >> 36) & 1)

    @property
    def sampled_raw(self):
        return (self.pads.status >> 37) & 3

    @property
    def wire(self):
        return (self.pads.levels, self.pads.enabled, self.pads.wires, self.pads.known)


def read_image(path):
    name, *fields = path.read_text().split()
    last, levels, enabled, *words = map(int, fields)
    require(name == "i2c-read" and (last, levels, enabled) == (154, 0, 0) and
            len(words) == 256 and all(0 <= word < 2**64 for word in words),
            "Expected the canonical one-byte I2C direct image")
    return last, levels, enabled, words


def execute(vvp, executable, image, *, ack_bits=(0, 0, 0), stretch_cycles=0,
            payload=0x96, fall_stretches=()):
    last, levels, enabled, words = image
    peer = I2CReadPeer(0x53, 0xA6, (payload,), ack_bits, phase_cycles=PHASE_CYCLES,
                       stretch_cycles=stretch_cycles, fall_stretches=fall_stretches)
    edges = []
    with Simulation(vvp, executable) as simulation:
        simulation.advance(0, 1, rst_n=0)
        for address, word in enumerate(words):
            simulation.advance(command(write=True, address=address, data=word), 1)
        simulation.advance(command(write=True, bank=2, data=levels | enabled << 3), 1)
        simulation.advance(command(write=True, bank=2, address=1, data=last), 1)
        simulation.advance(command(observe=True), 1, rst_n=0)
        simulation.device = peer
        for edge in range(2000):
            simulation.advance(command(observe=True, start=edge == 0), 1)
            current = Edge(simulation.cycle, simulation.observation)
            edges.append(current)
            if current.mode in (5, 6, 7):
                break
        else:
            raise TimeoutError("I2C fetch replay did not reach a terminal mode")
        peer.drive(simulation.cycle, simulation.observation, 0)
    require(simulation.process.returncode == 0 and not current.pads.enabled and
            (current.pads.bit(0), current.pads.bit(1)) == (1, 1),
            "The open-drain core did not terminate on released pads")
    require(current.mode == 5, "I2C read or precise NACK did not reach the compiled HALT")
    if not any(ack_bits):
        decoded = i2c_read_result(Result(current.samples, current.mode, False, False), byte_count=1)
        require(decoded.payload == (payload,), "Functional I2C result differs from the independent target")
    else:
        require(current.samples == 1 << (8 + ack_bits.index(1)),
                "I2C retained samples did not identify the exact NACK")
    return edges, peer, peer.check()


def check_fall_stretches(edges, peer):
    """Bind the peer's independent timers to observed SCL edges and controller release."""
    expected = [(index, duration) for index, duration in enumerate(peer.fall_stretches) if duration]
    anchors = peer.fall_stretch_arms
    require(expected == [(arm["fall_index"], arm["duration"]) for arm in anchors],
            "The falling-edge stretch plan did not run at every declared fall")
    samples = {edge.cycle: edge.pads for edge in edges}
    witnesses = []
    for arm in anchors:
        fall = arm["fall_edge"]
        target_release = arm["first_target_release_edge"]
        controller_release = next(edge.cycle for edge in edges if edge.cycle > fall and
                                  not edge.pads.logical.enabled & 1)
        rise = next(edge.cycle for edge in edges if edge.cycle > fall and edge.pads.bit(0))
        require(samples[fall - 1].bit(0) == 1 and samples[fall].bit(0) == 0 and
                target_release == fall + arm["duration"] and rise == max(target_release, controller_release),
                "Resolved stretch did not obey its falling-edge-relative release")
        witnesses.append(dict(arm, first_controller_release_edge=controller_release, resolved_rise_edge=rise,
                              independently_held_clocks=rise - controller_release))
    require(any(hold["independently_held_clocks"] > 0 for hold in witnesses),
            "No falling-edge timer held SCL after the controller released")
    return witnesses


def acknowledge(edges, peer):
    """Observe the first ACK aperture independently of the expected program bytes."""
    cuts = [current for prior, current in zip(edges, edges[1:]) if
            prior.mode == 3 and prior.pc == ACK_HIGH_PC and prior.remaining == 0 and current.pc == ACK_LOW_PC]
    require(len(cuts) == 1, "Expected one first-ACK capture transition")
    capture, rise = cuts[0], peer.rising_cycles[ACK_SLOT]
    bit = peer.bits[ACK_SLOT]
    require(capture.sampled_raw == (1 | bit << 1) and capture.samples >> ACK_SLOT & 1 == bit and
            capture.pads.bit(0) == 0, "First ACK did not consume its actual pre-edge resolved input")
    # SCL falls on the capture edge. The first resolved rise afterward can
    # prepare STOP for an address NACK instead of clocking another data bit.
    next_rise = next(edge.cycle for edge in edges if edge.cycle > capture.cycle and edge.pads.bit(0))
    lower, upper = PHASE_CYCLES, PHASE_CYCLES + 1
    low_limit = 2 * PHASE_CYCLES + 1 + peer.stretch_cycles
    offset = capture.cycle - rise
    low_span = next_rise - capture.cycle
    return dict(timing=dict(rise=rise, sample=capture.cycle, fall=capture.cycle, nextRise=next_rise),
                window=dict(earliestSample=lower, latestSample=upper, lowLimit=low_limit),
                offset=offset, sampled_sda=bit, low_span=low_span,
                sample_within_aperture=lower <= offset <= upper, low_within_limit=low_span <= low_limit)


def verify_hold(baseline, variant, *, low):
    waits = [index for index, prior in enumerate(variant[:-1]) if prior.fetch_wait]
    require(len(waits) == 1, "Expected exactly one registered successor request")
    index = waits[0]
    prior, held = variant[index:index + 2]
    require(prior.pc == held.pc == (ACK_LOW_PC if low else ACK_HIGH_PC) and
            prior.mode == held.mode == 3 and prior.remaining == held.remaining == 0 and
            prior.samples == held.samples and prior.pads.bit(0) == held.pads.bit(0) == int(not low),
            "The delayed row did not hold the intended ACK phase")
    expected = [edge.wire for edge in baseline]
    expected.insert(index + 1, expected[index])
    require(expected == [edge.wire for edge in variant],
            "The registered fetch changed more than one held pad observation")
    return held.cycle


def replay(run, tools, emitted, out):
    """Compile emitted RTL and require a timing rejection after successful decode."""
    out.mkdir(parents=True, exist_ok=False)
    bridge = ROOT / "test/reactive_fetch_bridge.sv"
    image = read_image(emitted / "images.txt")
    executables = {}
    for name, module in MODULES.items():
        design = out / f"{name}.sv"
        design.write_text(run([tools["circt"], emitted / f"{name}.mlir", "--canonicalize",
            "--lower-seq-to-sv", "--lower-hw-to-sv", "--hw-legalize-modules",
            "--export-verilog", "-o", "/dev/null"], f"{name}-lower"))
        executable = out / f"{name}.vvp"
        flags = [] if name == "baseline" else ["-DREGISTERED_FETCH"]
        run([tools["iverilog"], "-g2012", f"-DREACTIVE_MODULE={module}", *flags,
            "-s", "reactive_fetch_bridge", "-o", executable, design, bridge], f"{name}-compile")
        executables[name] = executable

    cases = {}
    # Falling edge 8 leads into the first ACK. Its timer finishes before the
    # retimed LOW cut at the end of the following controller phase.
    scenarios = {
        "read": {},
        "write-address-nack": dict(ack_bits=(1, 0, 0)),
        "register-nack": dict(ack_bits=(0, 1, 0)),
        "read-address-nack": dict(ack_bits=(0, 0, 1)),
        "stretched-read": dict(stretch_cycles=2),
        # Initial falling edge plus five following low samples, matching Fin 6 value 5.
        "causal-initial-stretch": dict(payload=0x3C, fall_stretches=(6,)),
        "causal-stretch-read": dict(payload=0x3C, fall_stretches=(0, 0, 9, 0, 0, 0, 0, 0, 10, 0, 0, 0, 9)),
        "causal-stretch-address-nack": dict(ack_bits=(1, 0, 0), fall_stretches=(0,) * 8 + (10,)),
    }
    for label, scenario in scenarios.items():
        baseline = None
        kinds = ("baseline", "low", "late") if label == "read" else ("baseline", "low")
        for kind in kinds:
            edges, peer, wire = execute(tools["vvp"], executables[kind], image, **scenario)
            if peer.fall_stretches:
                wire["fall_stretch_witnesses"] = check_fall_stretches(edges, peer)
            aperture = acknowledge(edges, peer)
            require(aperture["low_within_limit"] and aperture["sample_within_aperture"] == (kind != "late"),
                    "I2C capture aperture did not distinguish the late ACK variant")
            hold = None
            if kind == "baseline":
                baseline = edges
            else:
                hold = verify_hold(baseline, edges, low=kind == "low")
            trace = out / f"{label}-{kind}.jsonl"
            trace.write_text("".join(json.dumps(asdict(edge), separators=(",", ":")) + "\n" for edge in edges))
            cases[f"{label}-{kind}"] = dict(wire=wire, outcome=edges[-1].mode,
                samples=edges[-1].samples, edges=len(edges), held_edge=hold, ack_aperture=aperture,
                trace_sha256=sha(trace))
    return dict(cases=cases, image_sha256=sha(emitted / "images.txt"),
                scope="Closed-loop resolved digital pins and direct pre-edge input. "
                      "No upstream sampler, analog qualification or RTL equivalence claim.")
