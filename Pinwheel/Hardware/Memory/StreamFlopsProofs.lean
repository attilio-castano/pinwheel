import Pinwheel.Hardware.Memory.StreamFlops
import Pinwheel.Hardware.Memory.CommandFlopsProofs

namespace Pinwheel.Hardware.Memory.StreamFlops

open StreamInterface

@[simp] theorem view_encode (s : StreamModel.State a w) : view (encode s) = s := by
  cases s with
  | mk memory p => cases p <;> rfl

@[simp] theorem encode_view (s : Values (Register a w)) : @encode a w (view s) = @s := by
  funext b r
  cases r with
  | left r =>
    change CommandFlops.encode (CommandFlops.view (memoryValues s)) r = memoryValues s r
    rw [CommandFlops.encode_view]
  | right r =>
    cases r
    change BitVec.ofBool (s pending == 1) = s pending
    rcases BitVec.eq_zero_or_eq_one (s pending) with h | h <;> simp [h]

/-- Binding the command memory changes only its input and register leaves. -/
theorem memory_step (i : Values (Input a w)) (s : Values (Register a w))
    (r : CommandFlops.Register a w b) :
    (circuit a w).step i s (.left r) =
      (CommandFlops.circuit a w).step (memoryPins i s) (memoryValues s) r := by
  exact Expr.eval_bind memoryInput (fun p => .reg (.left p)) ((CommandFlops.circuit a w).next r) i s

/-- The physical memory command is exactly the command admitted by the stream
model, including idle on reset, on invalid offers, and under backpressure. -/
theorem decoded_command (i : Values (Input a w)) (s : Values (Register a w)) :
    CommandInterface.decode (memoryPins i s) = StreamModel.command (decode i) (view s) := by
  rcases BitVec.eq_zero_or_eq_one (i reset) with hr | hr <;>
    rcases BitVec.eq_zero_or_eq_one (i valid) with hv | hv <;>
    rcases BitVec.eq_zero_or_eq_one (i write) with hw | hw <;>
    rcases BitVec.eq_zero_or_eq_one (i ready) with hd | hd <;>
    rcases BitVec.eq_zero_or_eq_one (s pending) with hp | hp
  all_goals simp [CommandInterface.decode, memoryPins, memoryInput, accept, canLoad,
    Expr.eval, Expr.bor, StreamModel.command, StreamModel.ready, decode, view,
    hr, hv, hw, hd, hp, StreamModel.Request.command]

theorem step_eq (i : Values (Input a w)) (s : StreamModel.State a w) (r : Register a w b) :
    (circuit a w).step i (encode s) r = encode ((StreamInterface.spec a w).step i s) r := by
  cases r with
  | left r =>
    rw [memory_step]
    change (CommandFlops.circuit a w).step (memoryPins i (encode s)) (CommandFlops.encode s.memory) r = _
    rw [CommandFlops.step_eq]
    change CommandFlops.encode (SinglePort.step s.memory (CommandInterface.decode (memoryPins i (encode s)))) r = _
    rw [decoded_command, view_encode]
    rfl
  | right r =>
    cases r
    rcases BitVec.eq_zero_or_eq_one (i reset) with hr | hr <;>
      rcases BitVec.eq_zero_or_eq_one (i valid) with hv | hv <;>
      rcases BitVec.eq_zero_or_eq_one (i write) with hw | hw <;>
      rcases BitVec.eq_zero_or_eq_one (i ready) with hd | hd <;> cases hp : s.pending
    all_goals simp [Circuit.step, circuit, canLoad, Expr.eval, Expr.bor, encode, pending,
      StreamInterface.spec, decode, StreamModel.step, StreamModel.ready,
      StreamModel.Request.isRead, hr, hv, hw, hd, hp]

theorem output_eq (i : Values (Input a w)) (s : StreamModel.State a w) (o : Output w b) :
    (circuit a w).observe i (encode s) o = (StreamInterface.spec a w).observe i s o := by
  cases o with
  | «at» k =>
    match k with
    | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ =>
      all_goals rcases BitVec.eq_zero_or_eq_one (i reset) with hr | hr <;>
        rcases BitVec.eq_zero_or_eq_one (i ready) with hd | hd <;> cases hp : s.pending
      all_goals simp [Circuit.observe, circuit, responseValid, canLoad, Expr.eval, Expr.bor,
        encode, pending, StreamInterface.spec, outputValues, decode,
        StreamModel.component, StreamModel.machine, Hardware.Stream.Machine.component,
        StreamModel.ready, StreamModel.offer, hr, hd, hp, CommandFlops.encode, CommandFlops.q]
    | ⟨k+3, h⟩ => exact False.elim (by change k+3 < 3 at h; omega)

theorem step_view (i : Values (Input a w)) (s : Values (Register a w)) :
    view ((circuit a w).step i s) = StreamModel.step (decode i) (view s) := by
  have h : (fun {b} (r : Register a w b) => (circuit a w).step i s r) =
      @encode a w ((StreamInterface.spec a w).step i (view s)) := by
    simpa only [encode_view] using (funext fun b => funext fun r => step_eq i (view s) r)
  rw [h, view_encode]
  rfl

theorem output_view (i : Values (Input a w)) (s : Values (Register a w)) (o : Output w b) :
    (circuit a w).observe i s o = (StreamInterface.spec a w).observe i (view s) o := by
  simpa only [encode_view] using output_eq i (view s) o

/-- Every physical memory and pending-bit valuation is represented exactly.
Protocol reset is needed to establish an empty epoch, not a data invariant. -/
def implementation (a w : Nat) : Implementation (circuit a w) (StreamInterface.spec a w) where
  Valid := fun _ => True
  encode := encode
  preserved _ _ _ := trivial
  step_eq i s _ {_} r := step_eq i s r
  output_eq i s _ {_} o := output_eq i s o

theorem trace_correct (s : Values (Register a w)) (inputs : List (Values (Input a w))) :
    (circuit a w).component.trace s inputs =
      (StreamInterface.spec a w).trace (view s) inputs := by
  have h := (implementation a w).trace_eq (view s) trivial inputs
  simpa only [implementation, encode_view] using h

/-- This reset certificate retains the pre-edge memory state. It intentionally
does not use the fixed-initial-state `Implementation.Reset` abstraction. -/
theorem reset_eq (i : Values (Input a w)) (s : Values (Register a w)) (hr : i reset = 1) :
    (fun {b} (r : Register a w b) => (circuit a w).step i s r) =
      @encode a w ⟨(view s).memory, false⟩ := by
  have h := encode_view ((circuit a w).step i s)
  rw [step_view, StreamModel.reset_state (decode i) (view s) (by simp [decode, hr])] at h
  exact h.symm

theorem reset_memory (i : Values (Input a w)) (s : Values (Register a w)) (hr : i reset = 1)
    (r : CommandFlops.Register a w b) : (circuit a w).step i s (.left r) = s (.left r) := by
  have h := congrFun (congrFun (reset_eq i s hr) b) (.left r)
  change (circuit a w).step i s (.left r) =
    CommandFlops.encode (CommandFlops.view (memoryValues s)) r at h
  simpa only [CommandFlops.encode_view, memoryValues] using h

theorem reset_pending (i : Values (Input a w)) (s : Values (Register a w)) (hr : i reset = 1) :
    (circuit a w).step i s pending = 0 := by
  exact congrFun (congrFun (reset_eq i s hr) 1) pending

theorem reset_outputs (i : Values (Input a w)) (s : Values (Register a w)) (hr : i reset = 1) :
    (circuit a w).observe i s inReady = 0 ∧
      (circuit a w).observe i s outValid = 0 ∧ (circuit a w).observe i s outData = 0 := by
  simp [Circuit.observe, circuit, inReady, outValid, outData, responseValid, Expr.eval, hr]

/-- Traces after reset start with the same arbitrary memory and an empty
response slot, rather than a fabricated fixed memory initialization. -/
theorem trace_after_reset (i : Values (Input a w)) (s : Values (Register a w)) (hr : i reset = 1)
    (inputs : List (Values (Input a w))) :
    (circuit a w).component.trace ((circuit a w).step i s) inputs =
      (StreamInterface.spec a w).trace ⟨(view s).memory, false⟩ inputs := by
  rw [trace_correct, step_view, StreamModel.reset_state (decode i) (view s) (by simp [decode, hr])]

end Pinwheel.Hardware.Memory.StreamFlops
