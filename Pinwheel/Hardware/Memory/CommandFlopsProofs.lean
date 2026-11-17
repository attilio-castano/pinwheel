import Pinwheel.Hardware.Memory.CommandFlops
import Pinwheel.Hardware.Implementation

namespace Pinwheel.Hardware.Memory.CommandFlops

open CommandInterface

@[simp] theorem view_encode (s : Sram.State a w) : view (encode s) = s := by
  cases s
  rfl

@[simp] theorem encode_view (s : Values (Register a w)) : @encode a w (view s) = @s := by
  funext b r
  cases r <;> rename_i r <;> cases r <;> rfl

/-- Every physical input pattern is interpreted, including disabled write mode
with arbitrary unused address and data bits. -/
theorem step_eq (i : Values (Input a w)) (s : Sram.State a w) (r : Register a w b) :
    (circuit a w).step i (encode s) r = encode ((CommandInterface.spec a w).step i s) r := by
  cases r <;> rename_i r <;> cases r
  all_goals rcases BitVec.eq_zero_or_eq_one (i .enable) with he | he <;>
    rcases BitVec.eq_zero_or_eq_one (i .write) with hw | hw
  all_goals simp [Circuit.step, circuit, Expr.eval_bind, Flops.circuit,
    Flops.update, Update.next, writeInput, readEnable, readData,
    Expr.eval, Execution.readTree_correct, encode, word, q,
    CommandInterface.spec, CommandInterface.decode,
    SinglePort.step, Sram.State.step, Contents.write, he, hw]
  rename_i address
  by_cases ha : i .address = address <;> simp [ha]

theorem output_eq (i : Values (Input a w)) (s : Sram.State a w) (p : Output w b) :
    (circuit a w).observe i (encode s) p = (CommandInterface.spec a w).observe i s p := by
  cases p
  rfl

theorem output_view (i : Values (Input a w)) (s : Values (Register a w)) (p : Output w b) :
    (circuit a w).observe i s p = (CommandInterface.spec a w).observe i (view s) p := by
  cases p
  rfl

/-- Every physical register valuation represents a logical memory state. There
is no initialization invariant, excluded bit pattern, or reset precondition. -/
theorem step_view (i : Values (Input a w)) (s : Values (Register a w)) :
    view ((circuit a w).step i s) = SinglePort.step (view s) (decode i) := by
  have h : (fun {b} (r : Register a w b) => (circuit a w).step i s r) =
      @encode a w ((CommandInterface.spec a w).step i (view s)) := by
    simpa only [encode_view] using
      (funext fun b => funext fun r => step_eq i (view s) r)
  rw [h, view_encode]
  rfl

/-- The command-level contract is discharged by this actual structural circuit,
including arbitrary initial array words and arbitrary initial Q. -/
def contract (a w : Nat) : SinglePort.Contract (Values (Register a w)) a w where
  view := view
  advance command s := (circuit a w).step (CommandInterface.encode command) s
  correct command s := by
    rw [step_view, decode_encode]

/-- Raw physical inputs refine the command specification without an invariant. -/
def implementation (a w : Nat) : Implementation (circuit a w) (CommandInterface.spec a w) where
  Valid := fun _ => True
  encode := encode
  preserved _ _ _ := trivial
  step_eq i s _ {_} r := step_eq i s r
  output_eq i s _ {_} p := output_eq i s p

/-- Trace agreement starts at any physical state, with its exact array and Q
as the logical initial state. It makes no claim about power-up values. -/
theorem trace_correct (s : Values (Register a w)) (inputs : List (Values (Input a w))) :
    (circuit a w).component.trace s inputs =
      (CommandInterface.spec a w).trace (view s) inputs := by
  have h := (implementation a w).trace_eq (view s) trivial inputs
  simpa only [implementation, encode_view] using h

end Pinwheel.Hardware.Memory.CommandFlops
