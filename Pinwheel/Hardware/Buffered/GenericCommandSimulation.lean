import Pinwheel.Hardware.Buffered.GenericSramSimulation
import Pinwheel.Hardware.Buffered.LifecycleSramRetained

/-! Arbitrary rejected commands interleaved with execution and retained reads.
Admission is stated against actual hardware controls at each edge. Matching
RELEASE and reset remain explicit ownership-changing session events. -/
namespace Pinwheel.Hardware.Buffered.Refinement
open Pinwheel.Hardware Pinwheel.Program

structure Administrative (actual : SramState.State) (i : Values Reactive.Input) : Prop where
  cold : i .initialize = 0
  warm : i .command ≠ 7#3
  release : Reactive.releasing.eval i actual.core = 0

theorem RelatedSram.administrative_clock {p : Program.Buffered.Program}
    {layout : GenericCertificate.Layout p} {payload : BitVec 32}
    {actual : SramState.State} {source : Program.Buffered.State}
    (related : RelatedSram p layout payload actual source) (i : Values Reactive.Input)
    (admitted : Administrative actual i) : actual.step i = actual.step (Lifecycle.quiet i) := by
  obtain ⟨rows, dictionary, resident, ready, relation⟩ := related
  rcases relation with ⟨e, instruction, pc, running⟩ | ⟨e, outcome, stopped⟩
  · have busy : Reactive.busy.eval i actual.core = 1 := by
      have control := running.control
      cases state : source.core.control
      all_goals rw [state] at control
      case stopped => exact False.elim control
      all_goals have phase : actual.core .phase = _ := control.2.1
      all_goals simp [Reactive.busy, Reactive.both, Expr.eval, phase]
    exact Lifecycle.execution_clock actual i admitted.cold admitted.warm busy running.retained
  · have phase : Lifecycle.StoppedPhase (actual.core .phase) := by
      have value : actual.core .phase = stopPhase outcome := stopped.phase
      cases outcome
      all_goals simp [Lifecycle.StoppedPhase, value, stopPhase]
    exact Lifecycle.retained_clock actual i admitted.cold admitted.warm stopped.retained phase admitted.release

theorem RelatedSram.step_administrative {p : Program.Buffered.Program}
    {layout : GenericCertificate.Layout p} {payload : BitVec 32}
    {actual : SramState.State} {source : Program.Buffered.State}
    (related : RelatedSram p layout payload actual source) (i : Values Reactive.Input)
    (admitted : Administrative actual i) :
    RelatedSram p layout payload (actual.step i)
      (Program.Buffered.advance p capacity source (i .rawInputs)) := by
  rw [related.administrative_clock i admitted]
  exact related.step (Lifecycle.quiet i) (Lifecycle.quiet_input i)

def AdministrativeHistory : SramState.State → List (Values Reactive.Input) → Prop
  | _, [] => True
  | actual, i :: rest => Administrative actual i ∧ AdministrativeHistory (actual.step i) rest

def sourceCommands (p : Program.Buffered.Program) (source : Program.Buffered.State)
    (inputs : List (Values Reactive.Input)) : Program.Buffered.State :=
  inputs.foldl (fun current i => Program.Buffered.advance p capacity current (i .rawInputs)) source

theorem RelatedSram.run_administrative {p : Program.Buffered.Program}
    {layout : GenericCertificate.Layout p} {payload : BitVec 32}
    {actual : SramState.State} {source : Program.Buffered.State}
    (related : RelatedSram p layout payload actual source) (inputs : List (Values Reactive.Input))
    (admitted : AdministrativeHistory actual inputs) :
    RelatedSram p layout payload (actual.run inputs) (sourceCommands p source inputs) := by
  induction inputs generalizing actual source
  case nil => exact related
  case cons i rest ih => exact ih (related.step_administrative i admitted.1) admitted.2

end Pinwheel.Hardware.Buffered.Refinement
