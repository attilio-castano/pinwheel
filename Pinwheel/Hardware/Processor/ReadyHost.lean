import Pinwheel.Hardware.Processor.SystemModelProofs
import Pinwheel.Hardware.StreamingReady.SegmentPackage

/-! The processor drives the existing Ready quad transport through word MMIO.
The output latch and reply bus are the existing GPIO registers. Each CPU and
device edge sees pre-edge values. The independent peer owns the protocol
inputs, even when firmware writes arbitrary bits to GPIO. -/
namespace Pinwheel.Hardware.Processor.ReadyHost

open Pinwheel.Hardware.StreamingReady
open Pinwheel.Program.StreamingReady

structure Peer (E : Type) where
  reset : E → Bool
  sample : E → Pins → BitVec 2
  advance : E → Session.Pins → (TinyWiring.Pad → BitVec 8) → E

abbrev Host (aw : Nat) (E : Type) := SystemModel.State aw × E

/-- GPIO[0] selects the device, GPIO[1] clocks the host link and GPIO[5:2]
carry the request nibble. The reset value zero leaves chip select inactive. -/
def pins (reset : Bool) (word : BitVec 32) (raw : BitVec 2) : Session.Pins :=
  let word := if reset then 0 else word
  { «initialize» := reset, csn := !word.getLsbD 0, sck := word.getLsbD 1,
    mosi := word.extractLsb' 2 4, rawInputs := raw }

/-- GPIO input bits 0–3 hold MISO, 4 is ready, and 5 is busy. The package
already masks its reply while in reset. -/
def reply (pads : TinyWiring.Pad → BitVec 8) : BitVec 32 := (pads .uo).setWidth 32

def cpuInput (reset : Bool) (pads : TinyWiring.Pad → BitVec 8) : SystemModel.Input :=
  { reset := reset, gpio := reply pads }

def environment (layout : AddressMap.Layout rw aw) (rom : SystemModel.Rom rw)
    (peer : Peer E) : CausalSession.Environment (Host aw E) where
  inputs state drive :=
    pins (peer.reset state.2) state.1.mmio.gpioOut (peer.sample state.2 drive)
  advance state sampled pads :=
    (SystemModel.step layout rom (cpuInput (peer.reset state.2) pads) state.1,
     peer.advance state.2 sampled pads)

/-- A CPU read receives the public pad value visible on that service edge. -/
theorem read_reply (layout : AddressMap.Layout rw aw) (rom : SystemModel.Rom rw)
    (s : SystemModel.State aw) (pads : TinyWiring.Pad → BitVec 8)
    (route : SystemModel.pendingPlan layout rom s = some (.mmio ⟨.gpio, 0, false, 0⟩)) :
    (SystemModel.coreInput layout rom (cpuInput false pads) s).dataService =
      some (.atomic (.success (reply pads))) := by
  simp [SystemModel.coreInput, SystemModel.mmioInput, route, cpuInput,
    MmioModel.observe, MmioModel.access, SystemModel.mmioReply]

/-- An accepted GPIO output store becomes visible to Ready on the following
edge. The current edge samples the old output latch. -/
theorem write_drives_next (layout : AddressMap.Layout rw aw) (rom : SystemModel.Rom rw)
    (s : SystemModel.State aw) (pads : TinyWiring.Pad → BitVec 8) (word : BitVec 32)
    (route : SystemModel.pendingPlan layout rom s = some (.mmio ⟨.gpio, 1, true, word⟩)) :
    (SystemModel.step layout rom (cpuInput false pads) s).mmio.gpioOut = word := by
  simp [SystemModel.step, SystemModel.mmioInput, route, cpuInput, MmioModel.step,
    MmioModel.cpuState, MmioModel.autonomous, MmioModel.receive, MmioModel.access]

/-- Holding SCK across two edges cannot clock a second nibble, even when
the peer, output status, MOSI or processor instruction changes. -/
theorem held_clock (first second : Package.Pins) (same : second.sck = first.sck)
    (before after : Values StreamingReady.Core.Output) (regs : Values Streaming.Frontend.Register) :
    Streaming.Frontend.taking.eval (second.inputs after)
      (Streaming.Frontend.circuit.step (first.inputs before) regs) = 0 := by
  simp [Streaming.Frontend.taking, Streaming.Frontend.rising, Streaming.Frontend.both,
    Streaming.Frontend.circuit, Circuit.step, Streaming.Frontend.next, Expr.eval,
    Streaming.Package.Pins.inputs, same]

/-- Direct and registered Ready instruction storage couple to independently
executing processors and peers. Both resulting firmware states and the entire
observed pad history agree for every finite prefix. -/
theorem store_substitution (layout : AddressMap.Layout rw aw) (rom : SystemModel.Rom rw)
    (peer : Peer E) (initial : Host aw E) (direct cached : SegmentPackage.State a)
    (related : SegmentPackage.Related direct cached) (clocks : Nat) :
    let env := environment layout rom peer
    let l := (SegmentPackage.backend a false).run env direct initial clocks
    let r := (SegmentPackage.backend a true).run env cached initial clocks
    SegmentPackage.Related l.final r.final ∧ l.environment = r.environment ∧ l.edges = r.edges :=
  SegmentPackage.run_eq _ direct cached related initial clocks

end Pinwheel.Hardware.Processor.ReadyHost
