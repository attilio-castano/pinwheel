import Pinwheel.Hardware.Stream.Timing

open Pinwheel.Hardware Pinwheel.Hardware.Stream

namespace StreamExamples

/-- Swapping the arithmetic requires only a combinational expression and its
local meaning; no FIFO, handshake, composition or timing proof changes. -/
def complement (w : Nat) : Map w w where
  expression := .inv (.input .data)
  function := fun x => ~~~x
  correct := fun _ => rfl

def design (w d extra : Nat) (hd : 0 < d) := Design.buffered (complement w) d hd extra

example (w d extra : Nat) (hd : 0 < d) : Bounded (design w d extra hd).flatten (d + extra + 1) := by
  simpa only [design, Nat.add_assoc] using bounded_design (complement w) d extra hd

example (w d extra : Nat) (hd : 0 < d) : Stable (design w d extra hd).flatten.machine :=
  stable_design (complement w) d extra hd

example (w d extra : Nat) (hd : 0 < d) (inputs : List (Option (BitVec w))) :
    (noStall (design w d extra hd).flatten.machine).trace (design w d extra hd).flatten.initial inputs =
      (shiftModel (design w d extra hd).flatten.function).trace
        (List.replicate (extra + 2) none) inputs :=
  (delayDesign (complement w) d extra hd).noStall_trace inputs

example (w d extra : Nat) (hd : 0 < d) (s : (design w d extra hd).flatten.State)
    (h : (design w d extra hd).flatten.contract.Valid s) :
    flush (design w d extra hd).flatten.machine (d + (extra + 1)) s =
      (design w d extra hd).flatten.initial :=
  design_drains (complement w) d extra hd s h

end StreamExamples
