import Pinwheel.UART.RxWire

namespace Pinwheel.UART.StreamLink
open Link

/-- Continuous reception reserves a rearm edge and an idle-high observation after stop.
The extra two RX ticks strengthen the existing worst-phase single-frame bound. -/
def Safe (t : Timing) (b : Latency) : Prop :=
  Link.Safe t b ∧ t.center + 9 * t.rxBit + b.spread + 3 * t.rxTick ≤ 10 * t.txBit

instance (t : Timing) (b : Latency) : Decidable (Safe t b) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Concatenated one-byte TX specifications observed on the independent RX clock. -/
def sampled (t : Timing) (bytes : List (BitVec 8)) (age : Nat → Nat) : Nat → Bool :=
  observe t (Rx.Stream.wireBody t.tx bytes) age

/-- Keep global time quanta and move the local RX origin to the last rearm edge. -/
def next (t : Timing) (rearm : Nat) : Timing :=
  {t with txStart := t.txStart + 10 * t.txBit, rxPhase := t.edge rearm}

/-- Detection windows, recomputed from physical clocks after each actual rearm. -/
def Windows (t : Timing) (b : Latency) : List Rx.Stream.FrameSpec → Prop
  | [] => True
  | frame :: rest => firstEdge t b.earliest ≤ frame.detected ∧
    frame.detected ≤ firstEdge t b.latest ∧
    Windows (next t (frame.span t.rx)) b rest

end Pinwheel.UART.StreamLink
