import Pinwheel.Hardware.Stream.BufferedMerge.Circuit
import Pinwheel.Hardware.Implementation

namespace Pinwheel.Hardware.Stream.BufferedMerge.Structural

open Physical
set_option backward.isDefEq.respectTransparency false

@[simp] theorem slot_encode (s : State n (BitVec w)) (r : CellReg w 1 b) :
    encode s (slotReg r) = cells (slotValue s).toList r := rfl

@[simp] theorem cursor_encode (s : State n (BitVec w)) (k : Fin (n+1)) :
    encode s (cursorReg k) = BitVec.ofBool (k == s.cursor) := rfl

theorem decoded_request (i : Values (Physical.In n w)) (k : Fin (n+1)) :
    BufferedMerge.request (decode (readPins i)) k = (i (inValid k) == 1) := by
  simp only [BufferedMerge.request, decode, readPins]
  by_cases h : i (inValid k) = 1
  · simp only [h, if_true, Option.isSome_some, beq_self_eq_true]
  · simp only [if_neg h, Option.isSome_none, beq_eq_false_iff_ne.mpr h]

theorem winner_eval (i : Values (Physical.In n w)) (s : State n (BitVec w)) (k : Fin (n+1)) :
    (winner k).eval i (encode s) = BitVec.ofBool
      (Arbitration.RoundRobin.grant s.cursor (BufferedMerge.request (decode (readPins i))) == some k) := by
  apply Arbitration.OneHotSelect.winner_eval _ _ s.cursor _ i (encode s)
  · intro j; rfl
  · intro j
    simpa only [Expr.eval, decoded_request] using
      (Arbitration.RoundRobinCircuit.bit_roundtrip (i (inValid j))).symm

theorem anyWinner_eval (i : Values (Physical.In n w)) (s : State n (BitVec w)) :
    (anyWinner n w).eval i (encode s) = BitVec.ofBool
      (Arbitration.RoundRobin.grant s.cursor (BufferedMerge.request (decode (readPins i)))).isSome := by
  apply Arbitration.OneHotSelect.anyWinner_eval _ _ s.cursor _ i (encode s)
  · intro j; rfl
  · intro j
    simpa only [Expr.eval, decoded_request] using
      (Arbitration.RoundRobinCircuit.bit_roundtrip (i (inValid j))).symm

/-- The leaf may see a winner while it is full and blocked. Its established
elastic semantics reject that offer until ready; the merge cursor also holds. -/
def leafInput (i : BufferedMerge.Input n (BitVec w)) (s : State n (BitVec w)) : Stream.Input (BitVec w) :=
  ⟨i.reset, (Arbitration.RoundRobin.grant s.cursor (BufferedMerge.request i)).bind i.offered, i.ready 0⟩

theorem choice_offered (i : BufferedMerge.Input n α) (s : State n α) (k : Fin (n+1))
    (h : Arbitration.RoundRobin.grant s.cursor (BufferedMerge.request i) = some k) :
    ∃ value, i.offered k = some value := by
  have requested := Arbitration.RoundRobin.grant_requested h
  cases he : i.offered k <;> simp_all [BufferedMerge.request]

theorem leafInput_isSome (i : BufferedMerge.Input n (BitVec w)) (s : State n (BitVec w)) :
    (leafInput i s).offered.isSome =
      (Arbitration.RoundRobin.grant s.cursor (BufferedMerge.request i)).isSome := by
  cases hg : Arbitration.RoundRobin.grant s.cursor (BufferedMerge.request i) with
  | none => simp [leafInput, hg]
  | some k =>
    obtain ⟨v, hv⟩ := choice_offered i s k hg
    simp [leafInput, hg, hv]

theorem selectedPayload_eval (i : Values (Physical.In n w)) (s : State n (BitVec w)) :
    (selectedPayload n w).eval i (encode s) = (leafInput (decode (readPins i)) s).offered.getD 0 := by
  rw [selectedPayload, Arbitration.OneHotSelect.gather_eval _ _ _ _ _ _ (winner_eval i s)]
  cases hg : Arbitration.RoundRobin.grant s.cursor (BufferedMerge.request (decode (readPins i))) with
  | none => simp [Arbitration.OneHotSelect.chosenValue, leafInput, hg]
  | some k =>
    have requested := Arbitration.RoundRobin.grant_requested hg
    have hv : i (inValid k) = 1 := by simpa [decoded_request] using requested
    simp only [Arbitration.OneHotSelect.chosenValue, List.mem_finRange, if_true,
      leafInput, hg, Option.bind_some, Expr.eval]
    simp only [decode, readPins, hv, if_true, Option.getD_some]

theorem slotInput_eval (i : Values (Physical.In n w)) (s : State n (BitVec w)) :
    (fun {b} (p : Stream.In w b) => (slotInput n w p).eval i (encode s)) =
      @Stream.inputValues w (leafInput (decode (readPins i)) s) := by
  apply Stream.input_ext
  · exact (Arbitration.RoundRobinCircuit.bit_roundtrip (i Physical.reset)).symm
  · simpa only [slotInput, inputExpr, Stream.valid, Stream.inputValues, leafInput_isSome]
      using anyWinner_eval i s
  · exact (Arbitration.RoundRobinCircuit.bit_roundtrip (i outReady)).symm
  · exact selectedPayload_eval i s

theorem slotReady_eval (i : Values (Physical.In n w)) (s : State n (BitVec w)) :
    (slotReady n w).eval i (encode s) = BitVec.ofBool
      (!(decode (readPins i)).reset && BufferedMerge.canLoad (decode (readPins i)) s) := by
  simp only [slotReady, Expr.eval_bind, slotInput_eval, Expr.eval, slot_encode]
  rw [show ((Elastic.circuit (Map.identity w)).output Stream.inReady).eval
      (Stream.inputValues (leafInput (decode (readPins i)) s)) (cells (slotValue s).toList) = _ from
    Elastic.output_eq (Map.identity w) _ _ Stream.inReady]
  cases hr : (decode (readPins i)).reset <;> cases hs : s.slot <;>
    simp [Stream.outputValues, Stream.inReady, Machine.component, elastic, leafInput,
      slotValue, BufferedMerge.canLoad, hr, hs]

theorem accepted_eval (i : Values (Physical.In n w)) (s : State n (BitVec w)) (k : Fin (n+1)) :
    (accepted k).eval i (encode s) = BitVec.ofBool (BufferedMerge.grant (decode (readPins i)) s == some k) := by
  simp only [accepted, Expr.eval, slotReady_eval, winner_eval, BitVec.ofBool_and_ofBool]
  cases hr : (decode (readPins i)).reset <;> cases hc : BufferedMerge.canLoad (decode (readPins i)) s <;>
    simp [BufferedMerge.grant, hr, hc]

theorem leaf_step (i : BufferedMerge.Input n (BitVec w)) (s : State n (BitVec w)) :
    (elastic id).step (leafInput i s) (slotValue s) = slotValue (BufferedMerge.step i s) := by
  cases hr : i.reset <;> cases hd : i.ready 0 <;> cases hs : s.slot
  all_goals simp [leafInput, slotValue, BufferedMerge.step, elastic, BufferedMerge.slotInput,
    BufferedMerge.selected, BufferedMerge.grant, BufferedMerge.canLoad, hr, hd, hs,
    Function.comp_def, Option.map_map]

theorem cursorNext_eval (i : Values (Physical.In n w)) (s : State n (BitVec w)) (k : Fin (n+1)) :
    (cursorNext k).eval i (encode s) =
      BitVec.ofBool (k == (BufferedMerge.step (decode (readPins i)) s).cursor) := by
  simp only [cursorNext, Expr.eval, slotReady_eval, anyWinner_eval,
    BitVec.ofBool_and_ofBool, cursor_encode]
  rw [Arbitration.OneHotSelect.gather_eval _ _ _ _ _ _ (winner_eval i s)]
  cases hr : (decode (readPins i)).reset <;> cases hc : BufferedMerge.canLoad (decode (readPins i)) s <;>
    cases hg : Arbitration.RoundRobin.grant s.cursor (BufferedMerge.request (decode (readPins i))) <;>
    simp_all [Arbitration.OneHotSelect.chosenValue, BufferedMerge.step, BufferedMerge.grant,
      decode, readPins, Expr.eval]

theorem step_eq (i : Values (Physical.In n w)) (s : State n (BitVec w)) (r : Register n w b) :
    (circuit n w).step i (encode s) r = encode (BufferedMerge.step (decode (readPins i)) s) r := by
  cases r with
  | left r =>
    simp only [Circuit.step, circuit, Expr.eval_bind, slotInput_eval, Expr.eval, slot_encode]
    rw [show ((Elastic.circuit (Map.identity w)).next r).eval
        (Stream.inputValues (leafInput (decode (readPins i)) s)) (cells (slotValue s).toList) = _ from
      Elastic.step_eq (Map.identity w) _ _ r]
    rw [show (Map.identity w).function = id from rfl, leaf_step]
    rfl
  | right r => cases r with
    | «at» k => exact cursorNext_eval i s k

theorem output_eq (i : Values (Physical.In n w)) (s : State n (BitVec w)) (p : Physical.Out n w b) :
    (circuit n w).observe i (encode s) p =
      Physical.outputValues (BufferedMerge.observe (decode (readPins i)) s) p := by
  cases p with
  | left p => cases p with
    | «at» k => exact accepted_eval i s k
  | right p => cases p with
    | left p => cases p with
      | «at» k =>
        simp only [Circuit.observe, circuit, Expr.eval_bind, slotInput_eval, Expr.eval, slot_encode]
        rw [show ((Elastic.circuit (Map.identity w)).output Stream.outValid).eval
            (Stream.inputValues (leafInput (decode (readPins i)) s)) (cells (slotValue s).toList) = _ from
          Elastic.output_eq (Map.identity w) _ _ Stream.outValid]
        cases hr : (decode (readPins i)).reset <;>
          simp [Stream.outputValues, Stream.outValid, Physical.outputValues, BufferedMerge.observe,
            Machine.component, elastic, leafInput, slotValue, hr]
    | right p => cases p with
      | «at» k =>
        simp only [Circuit.observe, circuit, Expr.eval_bind, slotInput_eval, Expr.eval, slot_encode]
        rw [show ((Elastic.circuit (Map.identity w)).output Stream.outData).eval
            (Stream.inputValues (leafInput (decode (readPins i)) s)) (cells (slotValue s).toList) = _ from
          Elastic.output_eq (Map.identity w) _ _ Stream.outData]
        cases hr : (decode (readPins i)).reset <;>
          simp [Stream.outputValues, Stream.outData, Physical.outputValues, BufferedMerge.observe,
            Machine.component, elastic, leafInput, slotValue, hr]

/-- Neither source provenance nor an input queue is stored physically. -/
theorem encode_eq_of_payload_eq (s t : State n (BitVec w)) (hc : s.cursor = t.cursor)
    (hp : slotValue s = slotValue t) : @encode n w s = @encode n w t := by
  funext b r
  cases r with
  | left r => simp only [encode, hp]
  | right r => cases r; simp only [encode, hc]

theorem reset_eq (i : Values (Physical.In n w)) (s : Values (Register n w))
    (h : i Physical.reset = 1) (r : Register n w b) :
    (circuit n w).step i s r = encode (initial : State n (BitVec w)) r := by
  cases r with
  | left r => cases r <;>
      simp [Circuit.step, circuit, Expr.eval_bind, Expr.eval, Elastic.circuit, slotInput,
        inputExpr, Stream.reset, encode, slotValue, initial, cells, h]
  | right r => cases r <;>
      simp [Circuit.step, circuit, cursorNext, Expr.eval, encode, initial, h]

theorem reset_output (i : Values (Physical.In n w)) (s : Values (Register n w))
    (h : i Physical.reset = 1) (p : Physical.Out n w b) : (circuit n w).observe i s p = 0 := by
  cases p with
  | left p => cases p <;>
      simp [Circuit.observe, circuit, accepted, slotReady, Expr.eval_bind, Expr.eval,
        Elastic.circuit, slotInput, inputExpr, Stream.reset, Stream.inReady, streamOutputs, h, lanePorts]
  | right p => cases p <;> rename_i p <;> cases p <;>
      simp [Circuit.observe, circuit, Expr.eval_bind, Expr.eval, Elastic.circuit,
        slotInput, inputExpr, Stream.reset, Stream.outValid, Stream.outData, streamOutputs, h, lanePorts]

def implementation (n w : Nat) : Implementation (circuit n w) (Physical.component n w) where
  Valid := fun _ => True
  encode := encode
  preserved := fun _ _ _ => True.intro
  step_eq := fun i s _ _ r => step_eq i s r
  output_eq := fun i s _ _ p => output_eq i s p

def resetCertificate (n w : Nat) : (implementation n w).Reset Physical.reset where
  initial := initial
  initial_valid := True.intro
  reset_eq := fun i s h _ r => reset_eq i s h r

/-- Arbitrary raw pins, including invalid-port payload garbage, preserve the
physical observations of the provenance-erasing logical wrapper. -/
theorem raw_input_trace (s : State n (BitVec w)) (inputs : List (Values (Physical.In n w))) :
    (circuit n w).component.trace (encode s) inputs = (Physical.component n w).trace s inputs :=
  (implementation n w).trace_eq s True.intro inputs

/-- Reset establishes the logical relation from arbitrary raw register bits,
including malformed cursor encodings and dirty slot payloads. -/
theorem initialized_trace (i : Values (Physical.In n w)) (s : Values (Register n w))
    (h : i Physical.reset = 1) (inputs : List (Values (Physical.In n w))) :
    (circuit n w).component.trace ((circuit n w).step i s) inputs =
      (Physical.component n w).trace initial inputs :=
  (resetCertificate n w).trace_after_reset (implementation n w) Physical.reset i s h inputs

end Pinwheel.Hardware.Stream.BufferedMerge.Structural
