import Pinwheel.Hardware.Buffered.SramExecution
import Pinwheel.Hardware.Buffered.ReactiveProofs

set_option maxRecDepth 4096

/-! Actual digital-SRAM scalar transitions for arbitrary command edges,
including loader commands. The shared-dictionary adapter may translate a
command before applying the inherited Reactive equations; this translation is
explicit and is not replaced by an ideal source command. -/
namespace Pinwheel.Hardware.Buffered.Lifecycle
open Pinwheel.Hardware

def effectiveInputs (s : SramState.State) (i : Values Reactive.Input) : Values Reactive.Input :=
  SharedBranches.mappedInput i (SramExecution.selectedShared (s.inputs i) s.registers)

def effectiveState (s : SramState.State) (i : Values Reactive.Input) : Values Reactive.Register :=
  SramExecution.withWords s.core (SramExecution.selectedWords (s.inputs i) s.registers)

def Scalar : Reactive.Register w → Prop
  | .word _ | .written => False
  | _ => True

theorem adapted (s : SramState.State) (i : Values Reactive.Input) (e : Reactive.E w) :
    (Sram.adapt (SharedBranches.adapt e)).eval (s.inputs i) s.registers =
      e.eval (effectiveInputs s i) (effectiveState s i) := by
  rw [SramExecution.adapt_correct, SharedBranches.adapt_correct,
    SramExecution.selected_expand, SramExecution.base_inputs]
  rfl
  done

theorem scalar_step (s : SramState.State) (i : Values Reactive.Input)
    (r : Reactive.Register w) (scalar : Scalar r) :
    (s.step i).core r = Reactive.circuit.step (effectiveInputs s i) (effectiveState s i) r := by
  cases r
  case word k => exact False.elim scalar
  case written => exact False.elim scalar
  all_goals exact adapted s i _
  done

theorem scalar_current (s : SramState.State) (i : Values Reactive.Input)
    (r : Reactive.Register w) (scalar : Scalar r) : effectiveState s i r = s.core r := by
  cases r
  case word k => exact False.elim scalar
  all_goals rfl
  done

theorem observe_effective (s : SramState.State) (i : Values Reactive.Input)
    (o : Reactive.Output w) :
    s.observe i o = Reactive.circuit.observe (effectiveInputs s i) (effectiveState s i) o := by
  change (Sram.adapt (SharedBranches.output o)).eval (s.inputs i) s.registers = _
  rw [SramExecution.adapt_correct]
  change SharedBranches.circuit.observe (fun p => (s.inputs i) (.base p))
    (SramExecution.selectedShared (s.inputs i) s.registers) o = _
  rw [SharedBranches.observe_mapped, SramExecution.selected_expand, SramExecution.base_inputs]
  rfl
  done

theorem effective_runtime (s : SramState.State) (i : Values Reactive.Input)
    (runtime : SharedBranches.Runtime i) : @effectiveInputs s i = @i :=
  SharedBranches.mappedInput_runtime i _ runtime

theorem effective_cold (s : SramState.State) (i : Values Reactive.Input) :
    effectiveInputs s i .initialize = i .initialize := rfl

theorem effective_rawInputs (s : SramState.State) (i : Values Reactive.Input) :
    effectiveInputs s i .rawInputs = i .rawInputs := rfl

private theorem mapped_command_nonloader (i : Values Reactive.Input)
    (r : Values SharedBranches.Register) (target : BitVec 3)
    (one : target ≠ 1#3) (two : target ≠ 2#3) (six : target ≠ 6#3) :
    SharedBranches.mappedInput i r .command = target ↔ i .command = target := by
  by_cases h6 : i .command = 6#3
  all_goals by_cases h1 : i .command = 1#3
  all_goals by_cases h2 : i .command = 2#3
  all_goals simp [SharedBranches.mappedInput, SharedBranches.inputExpr,
    SharedBranches.cmd, SharedBranches.both, Expr.eval, h6, h1, h2]
  all_goals split <;> simp_all
  all_goals first | exact Ne.symm one | exact Ne.symm two | exact Ne.symm six | apply iff_of_false
  all_goals first | exact Ne.symm one | exact Ne.symm two | exact Ne.symm six
  done

theorem effective_command_nonloader (s : SramState.State) (i : Values Reactive.Input)
    (target : BitVec 3) (one : target ≠ 1) (two : target ≠ 2) (six : target ≠ 6) :
    effectiveInputs s i .command = target ↔ i .command = target :=
  mapped_command_nonloader i _ target one two six

theorem effective_command_flag (s : SramState.State) (i : Values Reactive.Input)
    (target : BitVec 3) (one : target ≠ 1) (two : target ≠ 2) (six : target ≠ 6) :
    (Reactive.cmd target).eval (effectiveInputs s i) (effectiveState s i) =
      (Reactive.cmd target).eval i s.core := by
  simp only [Reactive.cmd, Expr.eval,
    effective_command_nonloader s i target one two six]
  rfl
  done

theorem resetting_effective (s : SramState.State) (i : Values Reactive.Input) :
    Reactive.resetting.eval (effectiveInputs s i) (effectiveState s i) =
      Reactive.resetting.eval i s.core := by
  simp only [Reactive.resetting, Reactive.cold, Reactive.warm, Reactive.either,
    Reactive.both, Expr.eval, effective_cold]
  rw [effective_command_flag s i 7 (by decide) (by decide) (by decide)]
  done

theorem releasing_effective (s : SramState.State) (i : Values Reactive.Input) :
    Reactive.releasing.eval (effectiveInputs s i) (effectiveState s i) =
      Reactive.releasing.eval i s.core := by
  simp only [Reactive.releasing, Reactive.both, Expr.eval]
  rw [resetting_effective, effective_command_flag s i 4 (by decide) (by decide) (by decide)]
  rfl
  done

theorem starting_direct (s : SramState.State) (i : Values Reactive.Input) :
    Reactive.starting.eval (effectiveInputs s i) (effectiveState s i) =
      Reactive.starting.eval i s.core := by
  simp only [Reactive.starting, Reactive.free, Reactive.both, Expr.eval]
  rw [resetting_effective, effective_command_flag s i 3 (by decide) (by decide) (by decide)]
  rfl
  done

theorem starting_effective (s : SramState.State) (i : Values Reactive.Input) :
    Sram.starting.eval (s.inputs i) s.registers =
      Reactive.starting.eval (effectiveInputs s i) (effectiveState s i) := by
  rw [Sram.starting, SramExecution.control_correct, SharedBranches.adapt_correct,
    SramExecution.control_expand, ← SramExecution.mappedInput_same, SramExecution.base_inputs]
  change Reactive.starting.eval (effectiveInputs s i)
    (SramExecution.withWords s.core (SramExecution.controlWords (s.inputs i) s.registers)) = _
  rw [SramExecution.starting_withWords]
  exact (SramExecution.starting_withWords _ _ _).symm
  done

private theorem committing_withWords (i : Values Reactive.Input) (r : Values Reactive.Register)
    (words : Memory.Contents 6 144) :
    Reactive.committing.eval i (SramExecution.withWords r words) = Reactive.committing.eval i r := rfl

theorem committing_effective (s : SramState.State) (i : Values Reactive.Input) :
    Sram.committing.eval (s.inputs i) s.registers =
      Reactive.committing.eval (effectiveInputs s i) (effectiveState s i) := by
  rw [Sram.committing, SramExecution.control_correct, SharedBranches.committing,
    SharedBranches.adapt_correct, SramExecution.control_expand,
    ← SramExecution.mappedInput_same, SramExecution.base_inputs]
  change Reactive.committing.eval (effectiveInputs s i)
    (SramExecution.withWords s.core (SramExecution.controlWords (s.inputs i) s.registers)) = _
  rw [committing_withWords]
  exact (committing_withWords _ _ _).symm
  done

end Pinwheel.Hardware.Buffered.Lifecycle
