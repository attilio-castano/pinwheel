"""Named hardware targets and gate-specific measured expectations.

Capabilities describe the semantic boundary; retained counts below belong to
specific validation recipes and must never be mistaken for proof obligations.
"""
from dataclasses import dataclass


@dataclass(frozen=True)
class Target:
    name: str
    emitter: str
    top: str
    readiness: bool
    boundary: str
    input_latency: int
    test: str


CORE_TOP = "pinwheel_atomic_small_dense_cached"
TARGETS = {
    "prefetch": Target("prefetch", "prefetch_emit", CORE_TOP, False, "core", 0, "test/Prefetch.lean"),
    "twoport": Target("twoport", "twoport_emit", CORE_TOP, False, "core", 0, "test/TwoPort.lean"),
    "oneport": Target("oneport", "oneport_emit", CORE_TOP, True, "core", 0, "test/OnePort.lean"),
    "chip-oneport": Target("chip-oneport", "chip_emit", "tt_um_pinwheel", True, "chip", 2, "test/ChipEmit.lean"),
    "chip-twoport": Target("chip-twoport", "chip_emit", "tt_um_pinwheel", False, "chip", 2, "test/ChipEmit.lean"),
    "chip-oneport-result": Target("chip-oneport-result", "chip_emit", "tt_um_pinwheel", True, "chip with admission and result mailbox", 2, "test/ChipEmit.lean"),
    "chip-twoport-result": Target("chip-twoport-result", "chip_emit", "tt_um_pinwheel", False, "chip with result mailbox", 2, "test/ChipEmit.lean"),
}

# Historical core gate expectations; changing a target does not update these.
CORE_EXPECTATIONS = {
    "prefetch": dict(exe="prefetch_emit", stem="prefetch", test="test/Prefetch.lean", ready=False,
                     fields=(610, 6425), sampled_fields=(612, 6429), ff=(6415, 6419), points=(6350, 6354), induction=2,
                     lean="Decoupled (FetchPolicy) refinement, Backend.Prefetch.netlist_next/netlist_output/"
                          "completeRefinement, Prefetch.sampled_trace_correct"),
    # Mapped flip-flop counts are what synthesis keeps, not the register layout (`fields`): it
    # deletes the constant top bit of each word register and any bit it can show unread. Since
    # the command-split lift, the sampled two-port mapping keeps bits 3-8 of the cached word,
    # which it had shown unread before; the other five mappings are unchanged.
    "twoport": dict(exe="twoport_emit", stem="twoport", test="test/TwoPort.lean", ready=False,
                    fields=(610, 6425), sampled_fields=(612, 6429), ff=(6415, 6425), points=(6350, 6354), induction=2,
                    lean="TwoPort (FetchPolicy) refinement, Backend.Policy netlist_next/netlist_output/"
                         "completeRefinement via Backend.TwoPort.realization, TwoPort.sampled_trace_correct"),
    "oneport": dict(exe="oneport_emit", stem="oneport", test="test/OnePort.lean", ready=True,
                    fields=(611, 6426), sampled_fields=(613, 6430), ff=(6416, 6420), points=(6350, 6354), induction=3,
                    lean="SinglePort (FetchPolicy) rule refinement, Backend.OnePort.netlist_next/netlist_output/"
                         "completeRefinement, OnePort.sampled_trace_correct, on ready programs"),
}
