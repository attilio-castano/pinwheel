import Pinwheel.Hardware.Switch.Certified
import Pinwheel.Hardware.Arbitration.OneHotSelect

/-! An isolated switch candidate with shared winner decoding. The register
layout, input FIFOs, requests, backpressure and reset policy are the structural
switch's existing definitions. Only value/any/cursor selection changes. -/
namespace Pinwheel.Hardware.Switch.SharedSelectionCandidate

open Physical Structural

set_option backward.isDefEq.respectTransparency false

def selection (e : DestinationEncoding (m+1)) (w depth : Nat) (o : Fin (m+1))
    (value : Fin (n+1) → Wire n m e.width w depth b) (fallback : Wire n m e.width w depth b) :
    Wire n m e.width w depth b :=
  Arbitration.OneHotSelect.selection (fun c => .reg (cursorReg o c))
    (Structural.request e w depth o) value fallback

def grantAny (e : DestinationEncoding (m+1)) (w depth : Nat) (o : Fin (m+1)) :
    Wire n m e.width w depth 1 :=
  gated e.width w depth o (Arbitration.OneHotSelect.anyWinner
    (fun c => .reg (cursorReg o c)) (Structural.request e w depth o))

def selectedPayload (e : DestinationEncoding (m+1)) (w depth : Nat) (o : Fin (m+1)) :
    Wire n m e.width w depth w :=
  gated e.width w depth o (selection e w depth o (headPayload e.width w depth) (.lit 0))

def slotInput (e : DestinationEncoding (m+1)) (w depth : Nat) (o : Fin (m+1)) :
    {b : Nat} → Stream.In w b → Wire n m e.width w depth b :=
  Stream.inputExpr (.input reset) (grantAny e w depth o) (.input (outReady o)) (selectedPayload e w depth o)

def cursorNext (e : DestinationEncoding (m+1)) (w depth : Nat) (o : Fin (m+1)) (k : Fin (n+1)) :
    Wire n m e.width w depth 1 :=
  .mux (.input reset) (.lit (BitVec.ofBool (k == 0)))
    (.mux (Structural.canLoad e.width w depth o)
      (selection e w depth o (fun winner => .lit (BitVec.ofBool (k == Arbitration.RoundRobin.next winner)))
        (.reg (cursorReg o k))) (.reg (cursorReg o k)))

def circuit (e : DestinationEncoding (m+1)) (n w depth : Nat) :
    Circuit (In n m e.width w) (Register n m e.width w depth) (Out n m w) where
  next := fun {b} r => match b, r with
    | _, .left (.at k r) => ((Stream.Fifo.circuit (e.width+w) depth).next r).bind
        (Structural.fifoInput e w depth k) (fun r => .reg (fifoReg k r))
    | _, .right (.left (.at o r)) => ((Stream.Elastic.circuit (Stream.Map.identity w)).next r).bind
        (slotInput e w depth o) (fun r => .reg (slotReg o r))
    | _, .right (.right (.at o (.at k))) => cursorNext e w depth o k
  output := fun {b} p => match b, p with
    | _, .left (.at k) => .band (admissible e w depth k)
        (((Stream.Fifo.circuit (e.width+w) depth).output Stream.inReady).bind
          (Structural.fifoInput e w depth k) (fun r => .reg (fifoReg k r)))
    | _, .right (.left (.at o)) => ((Stream.Elastic.circuit (Stream.Map.identity w)).output Stream.outValid).bind
        (slotInput e w depth o) (fun r => .reg (slotReg o r))
    | _, .right (.right (.at o)) => ((Stream.Elastic.circuit (Stream.Map.identity w)).output Stream.outData).bind
        (slotInput e w depth o) (fun r => .reg (slotReg o r))

/-- No FIFO/slot representation validity is needed for local equivalence. -/
def LegalCursors (s : Values (Register n m dw w depth)) : Prop :=
  ∀ o, ∃ position : Fin (n+1), ∀ k, s (cursorReg o k) = BitVec.ofBool (k == position)

theorem encode_legal (e : DestinationEncoding (m+1)) (s : Switch.State n (m+1) (BitVec w)) :
    LegalCursors (Structural.encode e s : Values (Register n m e.width w depth)) :=
  fun o => ⟨s.cursor o, fun _ => rfl⟩

theorem selection_eq (e : DestinationEncoding (m+1)) (i : Values (In n m e.width w))
    (s : Values (Register n m e.width w depth)) (hs : LegalCursors s) (o : Fin (m+1))
    (value : Fin (n+1) → Wire n m e.width w depth b) (fallback : Wire n m e.width w depth b) :
    (selection e w depth o value fallback).eval i s =
      (Structural.selection e w depth o value fallback).eval i s := by
  obtain ⟨position, hc⟩ := hs o
  exact Arbitration.OneHotSelect.selection_eq_masked _ _ _ _ position i s hc

theorem grantAny_eq (e : DestinationEncoding (m+1)) (i : Values (In n m e.width w))
    (s : Values (Register n m e.width w depth)) (hs : LegalCursors s) (o : Fin (m+1)) :
    (grantAny e w depth o).eval i s = (Structural.grantAny e w depth o).eval i s := by
  obtain ⟨position, hc⟩ := hs o
  simp only [grantAny, Structural.grantAny, Structural.selection, gated, Expr.eval]
  rw [Arbitration.OneHotSelect.anyWinner_eval (fun c => .reg (cursorReg o c)) (Structural.request e w depth o) position
    (fun k => (Structural.request e w depth o k).eval i s == 1) i s hc
    (fun k => (Arbitration.RoundRobinCircuit.bit_roundtrip _).symm)]
  rw [Arbitration.RoundRobinMasked.raw_selection_eval (fun c => .reg (cursorReg o c))
    (Structural.request e w depth o) _ _ position i s hc]
  cases Arbitration.RoundRobin.grant position (fun k => (Structural.request e w depth o k).eval i s == 1) <;> rfl

theorem selectedPayload_eq (e : DestinationEncoding (m+1)) (i : Values (In n m e.width w))
    (s : Values (Register n m e.width w depth)) (hs : LegalCursors s) (o : Fin (m+1)) :
    (selectedPayload e w depth o).eval i s = (Structural.selectedPayload e w depth o).eval i s := by
  simp only [selectedPayload, Structural.selectedPayload, gated, Expr.eval, selection_eq e i s hs]

theorem cursorNext_eq (e : DestinationEncoding (m+1)) (i : Values (In n m e.width w))
    (s : Values (Register n m e.width w depth)) (hs : LegalCursors s) (o : Fin (m+1)) (k : Fin (n+1)) :
    (cursorNext e w depth o k).eval i s = (Structural.cursorNext e w depth o k).eval i s := by
  simp only [cursorNext, Structural.cursorNext, Expr.eval, selection_eq e i s hs]

theorem slotInput_eq (e : DestinationEncoding (m+1)) (i : Values (In n m e.width w))
    (s : Values (Register n m e.width w depth)) (hs : LegalCursors s) (o : Fin (m+1)) :
    (fun {b} (p : Stream.In w b) => (slotInput e w depth o p).eval i s) =
      (fun {b} (p : Stream.In w b) => (Structural.slotInput e w depth o p).eval i s) := by
  funext b p
  cases p with
  | «at» p => match p with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => exact grantAny_eq e i s hs o
    | ⟨2, _⟩ => rfl
    | ⟨3, _⟩ => exact selectedPayload_eq e i s hs o
    | ⟨p+4, h⟩ => exact False.elim (by change p+4<4 at h; omega)

theorem step_eq (e : DestinationEncoding (m+1)) (i : Values (In n m e.width w))
    (s : Values (Register n m e.width w depth)) (hs : LegalCursors s) (r : Register n m e.width w depth b) :
    (circuit e n w depth).step i s r = (Structural.circuit e n w depth).step i s r := by
  cases r with
  | left r => cases r <;> rfl
  | right r => cases r with
    | left r => cases r with
      | «at» o r => simp only [Circuit.step, circuit, Structural.circuit, Expr.eval_bind, slotInput_eq e i s hs]
    | right r => cases r with
      | «at» o r => cases r with
        | «at» k => exact cursorNext_eq e i s hs o k

theorem output_eq (e : DestinationEncoding (m+1)) (i : Values (In n m e.width w))
    (s : Values (Register n m e.width w depth)) (hs : LegalCursors s) (p : Out n m w b) :
    (circuit e n w depth).observe i s p = (Structural.circuit e n w depth).observe i s p := by
  cases p with
  | left p => cases p <;> rfl
  | right p => cases p with
    | left p => cases p with
      | «at» o => simp only [Circuit.observe, circuit, Structural.circuit, Expr.eval_bind, slotInput_eq e i s hs]
    | right p => cases p with
      | «at» o => simp only [Circuit.observe, circuit, Structural.circuit, Expr.eval_bind, slotInput_eq e i s hs]

/-- Reset recovery does not assume legal cursor bits or encoded storage. -/
theorem reset_eq (e : DestinationEncoding (m+1)) (i : Values (In n m e.width w))
    (s : Values (Register n m e.width w depth)) (hr : i reset = 1) (r : Register n m e.width w depth b) :
    (circuit e n w depth).step i s r = Structural.encode e Switch.initial r := by
  cases r with
  | left r => cases r with
    | «at» k r => exact Structural.reset_eq e i s hr (fifoReg k r)
  | right r => cases r with
    | left r => cases r with
      | «at» o r => cases r <;>
        simp [Circuit.step, circuit, Expr.eval_bind, Stream.Elastic.circuit, Expr.eval, slotInput,
          Stream.inputExpr, Stream.reset, hr, Structural.encode, slotValue, Switch.initial, Stream.cells]
    | right r => cases r with
      | «at» o r => cases r with
        | «at» k => simp [Circuit.step, circuit, cursorNext, Expr.eval, hr, Structural.encode, Switch.initial]

def implementation (e : DestinationEncoding (m+1)) (n w depth : Nat) (hd : 0 < depth) :
    Implementation (circuit e n w depth) (Physical.component e depth) where
  Valid := Switch.Valid depth
  encode := Structural.encode e
  preserved := fun i s h => Switch.valid_preserved depth (decode (readPins i)) s h
  step_eq := fun i s h _ r => (step_eq e i _ (encode_legal e s) r).trans (Structural.step_eq e s h i r)
  output_eq := fun i s h _ o => (output_eq e i _ (encode_legal e s) o).trans (Structural.output_eq e s h hd i o)

def resetCertificate (e : DestinationEncoding (m+1)) (n w depth : Nat) (hd : 0 < depth) :
    (implementation e n w depth hd).Reset Physical.reset where
  initial := Switch.initial
  initial_valid := Switch.initial_valid depth
  reset_eq := fun i s h _ r => reset_eq e i s h r

theorem initialized_trace (e : DestinationEncoding (m+1)) (n w depth : Nat) (hd : 0 < depth)
    (i : Values (In n m e.width w)) (s : Values (Register n m e.width w depth))
    (h : i Physical.reset = 1) (inputs : List (Values (In n m e.width w))) :
    (circuit e n w depth).component.trace ((circuit e n w depth).step i s) inputs =
      (Physical.component e depth).trace Switch.initial inputs :=
  (resetCertificate e n w depth hd).trace_after_reset
    (implementation e n w depth hd) Physical.reset i s h inputs

end Pinwheel.Hardware.Switch.SharedSelectionCandidate
