import Pinwheel.Hardware.Library

/-! FIFO substitution client. A client supplies a FIFO that implements the existing cycle
specification. A backend chooses its physical state relation and reset proof. -/
namespace FifoSubstitutionSketch
open Pinwheel.Hardware Stream

open BackendAPI

/-- The same expression builds a lane for either representation. -/
def lane (fifo : Fifo w d) (extra : Nat) :=
  serialCircuit fifo.circuit (Design.pipeline (increment w) extra).flatten.normalized.circuit

/-- Ordered transfer accounting at the pins of the composed lane. -/
def LaneLaw (fifo : Fifo w d) (extra : Nat) : Prop :=
  let c := lane fifo extra
  let empty : List (BitVec w) × PipelineState (BitVec w) extra := ([], pipelineEmpty extra)
  ∀ (r : Values (Joint fifo.Register (Design.pipeline (increment w) extra).flatten.Register))
    (i : Values (In w)), i reset = 1 → ∀ traffic : List (Values (In w)),
    let h := observedHistory c (c.step i r) {} traffic
    let result := runHistory (buffered (increment w).function d extra).component empty {}
      (traffic.map (fun (j : Values (In w)) => decodeInput j))
    h.inputs.map (fun x => x + 1) =
      h.outputs ++ (bufferedContract (increment w).function d extra).pending result.1

theorem lane_law (fifo : Fifo w d) (extra : Nat) : LaneLaw fifo extra :=
  buffered_transactions fifo (increment w) extra

end FifoSubstitutionSketch
