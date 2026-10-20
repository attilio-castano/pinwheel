import Pinwheel.Hardware.Buffered.LifecycleAdmission

/-! Retained ownership survives arbitrary rejected command edges. Sampling still
occurs on every clock; only matching RELEASE or reset clears the retained data.
The stopped-phase premise is explicit rather than inferred from arbitrary bits. -/
namespace Pinwheel.Hardware.Buffered.Lifecycle
open Pinwheel.Hardware
set_option maxRecDepth 4096

def StoppedPhase (phase : BitVec 3) : Prop := phase = 5 ∨ phase = 6 ∨ phase = 7

theorem held_controls (i : Values Reactive.Input) (r : Values Reactive.Register)
    (cold : i .initialize = 0) (warm : i .command ≠ 7#3)
    (retained : r .retained = 1) (phase : StoppedPhase (r .phase))
    (release : Reactive.releasing.eval i r = 0) :
    Reactive.resetting.eval i r = 0 ∧ Reactive.clearOwner.eval i r = 0 ∧
    Reactive.starting.eval i r = 0 ∧ Reactive.committing.eval i r = 0 ∧
    Reactive.writing.eval i r = 0 ∧ Reactive.busy.eval i r = 0 ∧
    Reactive.entering.eval i r = 0 ∧ Reactive.stopping.eval i r = 0 ∧
    Reactive.consuming.eval i r = 0 ∧ Reactive.appending.eval i r = 0 ∧
    Reactive.terminalEdge.eval i r = 0 := by
  rcases phase with phase | phase | phase
  all_goals simp [Reactive.resetting, Reactive.clearOwner, Reactive.cold, Reactive.warm,
    Reactive.cmd, Reactive.free, Reactive.starting, Reactive.committing, Reactive.writing,
    Reactive.busy, Reactive.entering, Reactive.stopping, Reactive.dispatch, Reactive.heldFault,
    Reactive.heldTimeout, Reactive.terminalEdge, Reactive.entryFailed, Reactive.entryComplete,
    Reactive.consuming, Reactive.appending, Reactive.runEntry, Reactive.isPhase,
    Reactive.both, Reactive.either, Expr.eval, cold, warm, retained, phase, release]
  done

theorem held_step (i : Values Reactive.Input) (r : Values Reactive.Register)
    (cold : i .initialize = 0) (warm : i .command ≠ 7#3)
    (retained : r .retained = 1) (phase : StoppedPhase (r .phase))
    (release : Reactive.releasing.eval i r = 0) :
    @Circuit.step Reactive.Input Reactive.Register Reactive.Output Reactive.circuit i r =
      @SpiCircuit.sampleTick r (i .rawInputs) := by
  rcases held_controls i r cold warm retained phase release with
    ⟨hr, ho, hs, hc, hw, hb, he, ht, hn, ha, hx⟩
  have hp4 : (Reactive.isPhase 4#3).eval i r = 0 := by
    rcases phase with phase | phase | phase
    all_goals simp [Reactive.isPhase, Expr.eval, phase]
  funext w register
  cases register
  all_goals simp [Circuit.step, Reactive.circuit, Reactive.next, SpiCircuit.sampleTick,
    Reactive.either, Reactive.both, Reactive.cold, Reactive.warm, Reactive.cmd,
    Reactive.runEntry, Reactive.exitScratch, Expr.eval, hr, ho, hs, hc, hw, hb,
    he, ht, hn, ha, hx, hp4, cold, warm]
  done

theorem retained_scalar_step (s : SramState.State) (i : Values Reactive.Input)
    (cold : i .initialize = 0) (warm : i .command ≠ 7#3)
    (retained : s.core .retained = 1) (phase : StoppedPhase (s.core .phase))
    (release : Reactive.releasing.eval i s.core = 0)
    (register : Reactive.Register w) (scalar : Scalar register) :
    (s.step i).core register = SpiCircuit.sampleTick s.core (i .rawInputs) register := by
  have mappedWarm : effectiveInputs s i .command ≠ 7#3 := by
    intro same
    exact warm ((effective_command_nonloader s i 7 (by decide) (by decide) (by decide)).mp same)
  rw [scalar_step s i register scalar,
    held_step (effectiveInputs s i) (effectiveState s i) cold mappedWarm retained phase
      (by rw [releasing_effective]; exact release)]
  cases register
  case word k => exact False.elim scalar
  all_goals rfl
  done

theorem retained_quiet_step (s : SramState.State) (i : Values Reactive.Input)
    (quiet : SpiCircuit.Quiet i) (retained : s.core .retained = 1)
    (phase : StoppedPhase (s.core .phase))
    (register : Reactive.Register w) (scalar : Scalar register) :
    (s.step i).core register = SpiCircuit.sampleTick s.core (i .rawInputs) register := by
  apply retained_scalar_step s i quiet.1 (by simp [quiet.2]) retained phase
    (by simp [Reactive.releasing, Reactive.both, Reactive.cmd, Expr.eval, quiet.2])
    register scalar
  done

theorem retained_rejection (s : SramState.State) (i : Values Reactive.Input)
    (cold : i .initialize = 0) (warm : i .command ≠ 7#3) (nonzero : i .command ≠ 0#3)
    (retained : s.core .retained = 1) (phase : StoppedPhase (s.core .phase))
    (release : Reactive.releasing.eval i s.core = 0) : s.observe i .rejected = 1 := by
  rw [observe_effective]
  have mappedWarm : effectiveInputs s i .command ≠ 7#3 := by
    intro same
    exact warm ((effective_command_nonloader s i 7 (by decide) (by decide) (by decide)).mp same)
  have mappedZero : effectiveInputs s i .command ≠ 0#3 := by
    intro same
    exact nonzero ((effective_command_nonloader s i 0 (by decide) (by decide) (by decide)).mp same)
  have mappedRelease : Reactive.releasing.eval (effectiveInputs s i) (effectiveState s i) = 0 := by
    rw [releasing_effective]
    exact release
  rcases held_controls (effectiveInputs s i) (effectiveState s i) cold mappedWarm
    retained phase mappedRelease with ⟨hr, _, hs, hc, hw, _⟩
  simp [Circuit.observe, Reactive.circuit, Reactive.rejected, Reactive.cmd,
    Reactive.both, Reactive.either, Expr.eval, hr, hs, hc, hw, mappedRelease, mappedZero]
  done

/-- Exact matching RELEASE restores idle and clears the owner data. Program
identity and the global allocation counter remain available for the next START. -/
def releaseTick (r : Values Reactive.Register) (raw : BitVec 2) : Values Reactive.Register
  | _, .phase | _, .retained | _, .pc | _, .virtualPC | _, .currentControl
  | _, .outer | _, .inner | _, .remaining | _, .waitLeft | _, .scratch
  | _, .cachedDuration | _, .cachedBudget | _, .cachedCheck | _, .cachedWait
  | _, .cachedTerminal | _, .cachedBranch | _, .txData | _, .txLength
  | _, .txConsumed | _, .rxData | _, .rxLength | _, .rxCapacity => 0
  | _, .levels => r .idleLevels
  | _, .enabled => r .idleEnabled
  | _, .stage1 => raw
  | _, .stage2 => r .stage1
  | _, register => r register

theorem release_step (i : Values Reactive.Input) (r : Values Reactive.Register)
    (cold : i .initialize = 0) (command : i .command = 4) (retained : r .retained = 1)
    (generation : i .expectedGeneration = r .generation)
    (transfer : i .expectedTransfer = r .transfer) :
    @Circuit.step Reactive.Input Reactive.Register Reactive.Output Reactive.circuit i r =
      @releaseTick r (i .rawInputs) := by
  have release := release_exact i r cold command retained generation transfer
  have controls : Reactive.resetting.eval i r = 0 ∧ Reactive.clearOwner.eval i r = 1 ∧
      Reactive.committing.eval i r = 0 ∧ Reactive.starting.eval i r = 0 ∧
      Reactive.writing.eval i r = 0 := by
    simp [Reactive.resetting, Reactive.cold, Reactive.warm, Reactive.cmd,
      Reactive.clearOwner, Reactive.committing, Reactive.starting, Reactive.writing,
      Reactive.both, Reactive.either, Expr.eval, cold, command, release]
  rcases controls with ⟨hr, ho, hc, hs, hw⟩
  funext w register
  cases register
  all_goals simp [Circuit.step, Reactive.circuit, Reactive.next, releaseTick,
    Reactive.either, Reactive.both, Reactive.cold, Reactive.warm, Reactive.cmd,
    Expr.eval, hr, ho, hc, hs, hw, cold, command]
  done

theorem release_scalar_step (s : SramState.State) (i : Values Reactive.Input)
    (cold : i .initialize = 0) (command : i .command = 4) (retained : s.core .retained = 1)
    (generation : i .expectedGeneration = s.core .generation)
    (transfer : i .expectedTransfer = s.core .transfer)
    (register : Reactive.Register w) (scalar : Scalar register) :
    (s.step i).core register = releaseTick s.core (i .rawInputs) register := by
  rw [scalar_step s i register scalar,
    effective_runtime s i (by simp [SharedBranches.Runtime, command]),
    release_step i (effectiveState s i) cold command retained generation transfer]
  cases register
  case word k => exact False.elim scalar
  all_goals rfl
  done

end Pinwheel.Hardware.Buffered.Lifecycle
