import Pinwheel.Hardware.Stream.BufferedMerge.Interface
import Pinwheel.Hardware.Stream.ElasticCircuit
import Pinwheel.Hardware.Arbitration.OneHotSelect

namespace Pinwheel.Hardware.Stream.BufferedMerge.Structural

open Physical
set_option backward.isDefEq.respectTransparency false

/-- One existing elastic cell followed by a one-hot arbitration cursor. -/
abbrev Register (n w : Nat) := Joint (CellReg w 1) (Lane 1 (n+1))

def registers (n w : Nat) : Hardware.Interface (Register n w) :=
  indexedInterface (Joint.interface (CellReg.interface w 1) (lanePorts 1 (n+1)).interface) "reg_"

def slotReg (r : CellReg w 1 b) : Register n w b := .left r
def cursorReg (k : Fin (n+1)) : Register n w 1 := .right (.at k)

def slotValue (s : State n (BitVec w)) : Option (BitVec w) := s.slot.map Delivery.payload

def encode (s : State n (BitVec w)) : Values (Register n w)
  | _, .left r => cells (slotValue s).toList r
  | _, .right (.at k) => BitVec.ofBool (k == s.cursor)

abbrev Wire (n w b : Nat) := Expr (Physical.In n w) (Register n w) b

def winner (k : Fin (n+1)) : Wire n w 1 :=
  Arbitration.OneHotSelect.winner (fun j => .reg (cursorReg j)) (fun j => .input (inValid j)) k

def anyWinner (n w : Nat) : Wire n w 1 :=
  Arbitration.OneHotSelect.anyWinner (fun j => .reg (cursorReg j)) (fun j => .input (inValid j))

def selectedPayload (n w : Nat) : Wire n w w :=
  Arbitration.OneHotSelect.gather winner (fun j => .input (inPayload j)) (List.finRange (n+1))

def slotInput (n w : Nat) : {b : Nat} → Stream.In w b → Wire n w b :=
  inputExpr (.input Physical.reset) (anyWinner n w) (.input outReady) (selectedPayload n w)

/-- Readiness comes from the actual elastic leaf, including its reset gate. -/
def slotReady (n w : Nat) : Wire n w 1 :=
  ((Elastic.circuit (Map.identity w)).output Stream.inReady).bind
    (slotInput n w) (fun r => .reg (slotReg r))

def accepted (k : Fin (n+1)) : Wire n w 1 := .band (slotReady n w) (winner k)

def cursorNext (k : Fin (n+1)) : Wire n w 1 :=
  .mux (.input Physical.reset) (.lit (BitVec.ofBool (k == 0)))
    (.mux (.band (slotReady n w) (anyWinner n w))
      (Arbitration.OneHotSelect.gather winner
        (fun j => .lit (BitVec.ofBool (k == Arbitration.RoundRobin.next j))) (List.finRange (n+1)))
      (.reg (cursorReg k)))

def circuit (n w : Nat) : Circuit (Physical.In n w) (Register n w) (Physical.Out n w) where
  next := fun {b} r => match b, r with
    | _, .left r => ((Elastic.circuit (Map.identity w)).next r).bind
        (slotInput n w) (fun r => .reg (slotReg r))
    | _, .right (.at k) => cursorNext k
  output := fun {b} p => match b, p with
    | _, .left (.at k) => accepted k
    | _, .right (.left (.at _)) => ((Elastic.circuit (Map.identity w)).output Stream.outValid).bind
        (slotInput n w) (fun r => .reg (slotReg r))
    | _, .right (.right (.at _)) => ((Elastic.circuit (Map.identity w)).output Stream.outData).bind
        (slotInput n w) (fun r => .reg (slotReg r))

end Pinwheel.Hardware.Stream.BufferedMerge.Structural
