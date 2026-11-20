import Pinwheel.Hardware.StreamingReady.EthernetSession
import Pinwheel.Program.StreamingEthernetPacedHost

/-! The source offer proof carries through the same typed core and quad
frontend used for the sampled-ready wire session. -/
namespace Pinwheel.Hardware.StreamingReady.EthernetDeadline
open Pinwheel.Program.StreamingReady Pinwheel.Program.StreamingEthernetCore
open Pinwheel.Program.StreamingEthernetDeadline Pinwheel.Program.StreamingEthernetPacedHost
open Pinwheel.Hardware.StreamingReady.InitializedCustody

/-- Starting at the aligned reservation of a reached Ethernet session,
an independent PHY clock and permitted full-word host offers determine
the exact typed package wire trace and the ordered consumed payload. -/
theorem wire_from_offers (actual : Package.State 1) (s : Session.State 1) (trace : BitTrace)
    (reached : Reached image actual s trace) (pins : List Session.Pins)
    (runtime : Session.RuntimeTrace program false s pins) (cells : List CellInputs) (finish : Input)
    (shape : s.runtimeInputs program false pins = blocks cells ++ [finish])
    (bits : List Bool) (width : Nat → Fin 2)
    (boundary : Boundary s.core cells.length) (fullWords : ∀ chunk ∈ trace.txQueued, chunk.validBits = 32)
    (initial : s.core.txConsumed = 0#16) (size : bits.length = cells.length)
    (phy : PhyClock width cells)
    (host : ∀ i ∈ blocks cells, HostClock s.core.generation s.core.transfer i)
    (plan : RefillPlan trace.accepted.length s.core.txConsumed.toNat cells)
    (payload : trace.accepted ++ offers (blocks cells) = bits)
    (capacity : bits.length ≤ s.core.total.toNat) (terminal : Ordinary finish) (noOffer : finish.txPush = false) :
    (s.run program false pins).core.phase = .completed ∧
      PublicPins.driveTrace actual pins = bits.flatMap cellPins ++ [txPins false, idlePins] ∧
      (s.traceRun program false trace pins).consumed = bits := by
  have valid : WordTrace s.core trace := ⟨reached.custody.related, reached.custody.counts,
    reached.custody.structural, reached.custody.progress, by simp [boundary.phase, Phase.busy], fullWords⟩
  have exactWire := frame_from_offers s.core cells finish trace bits width boundary valid initial size phy
    host plan payload capacity terminal noOffer
  rw [reached.package, Session.State.run_core, Session.State.traceRun_runtimeInputs, shape]
  have wire := PublicPins.driveTrace_eq (Initialization.compiledImage image) s pins (by decide)
    (by simpa only [compiled_pending] using runtime) reached.custody.structural
  rw [compiled_pending, shape] at wire
  exact ⟨exactWire.1, wire.trans exactWire.2.1, exactWire.2.2⟩

end Pinwheel.Hardware.StreamingReady.EthernetDeadline
