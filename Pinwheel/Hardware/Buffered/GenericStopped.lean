import Pinwheel.Hardware.Buffered.GenericRelation

/-! Retained completion, timeout and fault all freeze the source execution.
The actual sampler registers keep clocking, so they are abstracted here. -/
namespace Pinwheel.Hardware.Buffered.GenericPhase
open Pinwheel.Hardware

theorem stopped_controls (i : Values Reactive.Input) (r : Values Reactive.Register)
    (quiet : SpiCircuit.Quiet i) (phase : r .phase = 5 ∨ r .phase = 6 ∨ r .phase = 7) :
    Reactive.busy.eval i r = 0 ∧ Reactive.entering.eval i r = 0 ∧
    Reactive.stopping.eval i r = 0 ∧ Reactive.consuming.eval i r = 0 ∧
    Reactive.appending.eval i r = 0 ∧ Reactive.terminalEdge.eval i r = 0 := by
  rcases phase with phase | phase | phase
  all_goals simp [Reactive.busy, Reactive.entering, Reactive.stopping, Reactive.dispatch,
    Reactive.heldFault, Reactive.heldTimeout, Reactive.terminalEdge,
    Reactive.entryFailed, Reactive.entryComplete, Reactive.consuming,
    Reactive.appending, Reactive.runEntry, Reactive.isPhase, Reactive.both,
    Reactive.either, Expr.eval, phase, (SpiCircuit.quiet_controls i r quiet).1,
    (SpiCircuit.quiet_controls i r quiet).2.2.1]

theorem stopped_step (i : Values Reactive.Input) (r : Values Reactive.Register)
    (quiet : SpiCircuit.Quiet i) (phase : r .phase = 5 ∨ r .phase = 6 ∨ r .phase = 7) :
    @Circuit.step Reactive.Input Reactive.Register Reactive.Output Reactive.circuit i r =
      @SpiCircuit.sampleTick r (i .rawInputs) := by
  rcases SpiCircuit.quiet_controls i r quiet with ⟨reset, clear, start, commit, write, _⟩
  rcases stopped_controls i r quiet phase with ⟨busy, entering, stopping, consume, append, terminal⟩
  have phase4 : (Reactive.isPhase 4#3).eval i r = 0 := by
    rcases phase with phase | phase | phase
    all_goals simp [Reactive.isPhase, Expr.eval, phase]
  funext width reg
  cases reg
  all_goals simp [Circuit.step, Reactive.circuit, Reactive.next, SpiCircuit.sampleTick,
    Reactive.either, Reactive.both, Reactive.cold, Reactive.warm, Reactive.cmd,
    Reactive.runEntry, Reactive.exitScratch, Expr.eval, reset, clear, start, commit,
    write, busy, entering, stopping, consume, append, terminal, phase4, quiet.1, quiet.2]
  done

end Pinwheel.Hardware.Buffered.GenericPhase

namespace Pinwheel.Hardware.Buffered.Refinement
open Pinwheel.Hardware Pinwheel.Program

theorem Common.sampleTick {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {payload : BitVec 32} {r : Values Reactive.Register} {s : Program.Buffered.State}
    {e : Transfer.Execution} (h : Common p layout payload r s e) (raw : BitVec 2) :
    Common p layout payload (SpiCircuit.sampleTick r raw) s e :=
  ⟨h.count, h.span, h.idleLevels, h.idleEnabled, h.image, h.valid,
    h.data.sampleTick raw, h.owner, h.pins, h.scratch⟩

theorem Stopped.sampleTick {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {payload : BitVec 32} {r : Values Reactive.Register} {s : Program.Buffered.State}
    {e : Transfer.Execution} {outcome : Transfer.Outcome}
    (h : Stopped p layout payload r s e outcome) (raw : BitVec 2) :
    Stopped p layout payload (SpiCircuit.sampleTick r raw) s e outcome :=
  ⟨h.common.sampleTick raw, h.slot, h.control, h.phase, h.retained, h.pc, h.virtualPC,
    h.outer, h.inner, h.currentControl, h.remaining, h.waitLeft, h.cachedDuration,
    h.cachedBudget, h.cachedCheck, h.cachedWait, h.cachedTerminal, h.cachedBranch⟩

theorem Stopped.step {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {payload : BitVec 32} {r : Values Reactive.Register} {s : Program.Buffered.State}
    {e : Transfer.Execution} {outcome : Transfer.Outcome}
    (h : Stopped p layout payload r s e outcome)
    (i : Values Reactive.Input) (quiet : SpiCircuit.Quiet i) :
    Stopped p layout payload (Reactive.circuit.step i r)
      (Program.Buffered.advance p capacity s (i .rawInputs)) e outcome := by
  have phase : r .phase = 5 ∨ r .phase = 6 ∨ r .phase = 7 := by
    cases outcome <;> simp [h.phase, stopPhase]
  rw [GenericPhase.stopped_step i r quiet phase,
    SpiInterpreter.advance_stopped p capacity s (stopReason outcome) h.control]
  exact h.sampleTick (i .rawInputs)

end Pinwheel.Hardware.Buffered.Refinement
