import Pinwheel.Hardware.Buffered.LifecycleRetained

/-! Busy command deliveries still clock the engine. Rejected administrative
commands have the same post-state as a quiet clock with the same raw inputs;
their combinational rejection observation is deliberately kept separate. -/
namespace Pinwheel.Hardware.Buffered.Lifecycle
open Pinwheel.Hardware
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
set_option backward.dsimp.instances true
set_option backward.isDefEq.respectTransparency false

def quiet (i : Values Reactive.Input) : Values Reactive.Input
  | _, .initialize => 0
  | _, .command => 0
  | _, port => i port

theorem quiet_input (i : Values Reactive.Input) : SpiCircuit.Quiet (quiet i) := ⟨rfl, rfl⟩

theorem busy_controls (i : Values Reactive.Input) (r : Values Reactive.Register)
    (cold : i .initialize = 0) (warm : i .command ≠ 7#3)
    (busy : Reactive.busy.eval i r = 1) (retained : r .retained = 0) :
    Reactive.resetting.eval i r = 0 ∧ Reactive.clearOwner.eval i r = 0 ∧
    Reactive.starting.eval i r = 0 ∧ Reactive.committing.eval i r = 0 ∧
    Reactive.writing.eval i r = 0 ∧ Reactive.releasing.eval i r = 0 := by
  rcases Reactive.busy_blocks_updates i r busy with ⟨write, commit, start⟩
  simp [Reactive.resetting, Reactive.clearOwner, Reactive.releasing, Reactive.cold,
    Reactive.warm, Reactive.cmd, Reactive.both, Reactive.either, Expr.eval,
    cold, warm, retained, write, commit, start]
  done

private theorem pack_congr (n : Nat) (f g : Fin n → Reactive.E 1)
    (i j : Values Reactive.Input) (r : Values Reactive.Register)
    (each : ∀ k, (f k).eval i r = (g k).eval j r) :
    (Reactive.pack f).eval i r = (Reactive.pack g).eval j r := by
  apply (BitVec.eq_of_getLsbD_eq_iff).2
  intro k hk
  have left := Reactive.pack_selected_bit n f i r ⟨k, hk⟩
  have right := Reactive.pack_selected_bit n g j r ⟨k, hk⟩
  exact left.trans ((congrArg (fun x : BitVec 1 => x.getLsbD 0) (each ⟨k, hk⟩)).trans right.symm)
  done

structure ClockControls (i : Values Reactive.Input) (r : Values Reactive.Register) : Prop where
  cold : i .initialize = 0
  warm : Reactive.warm.eval i r = 0
  resetting : Reactive.resetting.eval i r = 0
  clearing : Reactive.clearOwner.eval i r = 0
  starting : Reactive.starting.eval i r = 0
  committing : Reactive.committing.eval i r = 0
  writing : Reactive.writing.eval i r = 0

theorem quiet_controls (i : Values Reactive.Input) (r : Values Reactive.Register) :
    ClockControls (quiet i) r := by
  rcases SpiCircuit.quiet_controls (quiet i) r (quiet_input i) with ⟨hr, ho, hs, hc, hw, _⟩
  refine ⟨rfl, ?_, hr, ho, hs, hc, hw⟩
  simp [Reactive.warm, Reactive.cold, Reactive.cmd, Reactive.both, Expr.eval, quiet]
  done

theorem execution_controls (i : Values Reactive.Input) (r : Values Reactive.Register)
    (cold : i .initialize = 0) (warm : i .command ≠ 7#3)
    (busy : Reactive.busy.eval i r = 1) (retained : r .retained = 0) : ClockControls i r := by
  rcases busy_controls i r cold warm busy retained with ⟨hr, ho, hs, hc, hw, _⟩
  refine ⟨cold, ?_, hr, ho, hs, hc, hw⟩
  simp [Reactive.warm, Reactive.cold, Reactive.cmd, Reactive.both, Expr.eval, cold, warm]
  done

theorem reactive_clock (i j : Values Reactive.Input) (r : Values Reactive.Register)
    (h : ClockControls i r) (q : ClockControls j r) (raw : i .rawInputs = j .rawInputs) :
    @Circuit.step Reactive.Input Reactive.Register Reactive.Output Reactive.circuit i r =
      @Circuit.step Reactive.Input Reactive.Register Reactive.Output Reactive.circuit j r := by
  rcases h with ⟨cold, hm, hr, ho, hs, hc, hw⟩
  rcases q with ⟨jcold, qm, qr, qo, qs, qc, qw⟩
  have entering : Reactive.entering.eval i r = Reactive.entering.eval j r := by
    simp only [Reactive.entering, Reactive.both, Reactive.either, Expr.eval, hr, hs, qr, qs]
    rfl
  have entryPC : Reactive.entryPC.eval i r = Reactive.entryPC.eval j r := by
    simp only [Reactive.entryPC, Reactive.sequentialPC, Expr.eval, hs, qs]
    rfl
  have entryOuter : Reactive.entryOuter.eval i r = Reactive.entryOuter.eval j r := by
    simp only [Reactive.entryOuter, Reactive.sequentialOuter, Expr.eval, hs, qs]
    rfl
  have entryInner : Reactive.entryInner.eval i r = Reactive.entryInner.eval j r := by
    simp only [Reactive.entryInner, Reactive.sequentialInner, Expr.eval, hs, qs]
    rfl
  have entryVirtual : Reactive.entryVirtual.eval i r = Reactive.entryVirtual.eval j r := by
    simp only [Reactive.entryVirtual, Expr.eval, hs, qs]
    rfl
  have record : Reactive.entryRecord.eval i r = Reactive.entryRecord.eval j r := by
    simp only [Reactive.entryRecord, Expr.eval, Execution.readTree_correct, entering, entryPC]
  have word : Reactive.entryWord.eval i r = Reactive.entryWord.eval j r := by
    simp only [Reactive.entryWord, Expr.eval, record]
  have control : Reactive.entryControl.eval i r = Reactive.entryControl.eval j r := by
    simp only [Reactive.entryControl, Expr.eval, record]
  have branch : Reactive.entryBranch.eval i r = Reactive.entryBranch.eval j r := by
    simp only [Reactive.entryBranch, Expr.eval, record]
  have kind : Reactive.kind.eval i r = Reactive.kind.eval j r := by
    simp only [Reactive.kind, Expr.eval, word]
  have legal : Reactive.legalEntry.eval i r = Reactive.legalEntry.eval j r := by
    simp only [Reactive.legalEntry, Reactive.inBounds, Reactive.canonical,
      Reactive.controlCanonical, Reactive.branchCanonical, Reactive.nextNormalizes,
      Reactive.captureCanonical, Reactive.endpointCanonical, Reactive.controlDepth,
      Reactive.outerStart, Reactive.outerBound, Reactive.innerStart, Reactive.innerBound,
      Reactive.outerEnd, Reactive.innerEnd, Reactive.entryCapture, Reactive.terminalCapture,
      Reactive.entryTerminal, Reactive.isKind, Reactive.both, Reactive.either, Expr.eval,
      entryPC, entryOuter, entryInner, entryVirtual, word, control, branch, kind]
    rfl
  have runEntry : Reactive.runEntry.eval i r = Reactive.runEntry.eval j r := by
    simp only [Reactive.runEntry, Reactive.entryTerminal, Reactive.isKind,
      Reactive.both, Reactive.either, Expr.eval, entering, legal, kind]
  have underflow : Reactive.underflow.eval i r = Reactive.underflow.eval j r := by
    simp only [Reactive.underflow, Reactive.isKind, Reactive.entryConsumed,
      Reactive.entryTxLength, Reactive.both, Expr.eval, runEntry, kind, hs, qs]
    rfl
  have overflow : Reactive.overflow.eval i r = Reactive.overflow.eval j r := by
    simp only [Reactive.overflow, Reactive.wantsRx, Reactive.entryRxLength,
      Reactive.entryCapacity, Reactive.both, Expr.eval, runEntry, underflow, word, hs, qs]
    rfl
  have consuming : Reactive.consuming.eval i r = Reactive.consuming.eval j r := by
    simp only [Reactive.consuming, Reactive.isKind, Reactive.both, Expr.eval, runEntry, kind, underflow]
  have appending : Reactive.appending.eval i r = Reactive.appending.eval j r := by
    simp only [Reactive.appending, Reactive.wantsRx, Reactive.both, Expr.eval,
      runEntry, underflow, word, overflow]
  have complete : Reactive.entryComplete.eval i r = Reactive.entryComplete.eval j r := by
    simp only [Reactive.entryComplete, Reactive.isKind, Reactive.both, Expr.eval, entering, legal, kind]
  have timeout : Reactive.entryTimeout.eval i r = Reactive.entryTimeout.eval j r := by
    simp only [Reactive.entryTimeout, Reactive.isKind, Reactive.both, Expr.eval, entering, legal, kind, word]
  have failed : Reactive.entryFailed.eval i r = Reactive.entryFailed.eval j r := by
    simp only [Reactive.entryFailed, Reactive.isKind, Reactive.both, Reactive.either,
      Expr.eval, entering, legal, kind, underflow, overflow]
  have stopping : Reactive.stopping.eval i r = Reactive.stopping.eval j r := by
    simp only [Reactive.stopping, Reactive.both, Reactive.either, Expr.eval, hr, qr, failed, complete]
    rfl
  have entryPhase : Reactive.entryPhase.eval i r = Reactive.entryPhase.eval j r := by
    simp only [Reactive.entryPhase, Reactive.isKind, Expr.eval, kind]
  have sampled : Reactive.sampled.eval i r = Reactive.sampled.eval j r := by
    simp only [Reactive.sampled, Expr.eval, word]
  have appended : Reactive.appended.eval i r = Reactive.appended.eval j r := by
    unfold Reactive.appended
    apply pack_congr
    intro k
    simp [Expr.eval, Reactive.entryRxLength, hs, qs, sampled]
  have shifted (base : Reactive.E 3) (same : base.eval i r = base.eval j r) :
      (Reactive.shifted base).eval i r = (Reactive.shifted base).eval j r := by
    unfold Reactive.shifted
    apply pack_congr
    intro k
    simp [Reactive.shiftValue, Reactive.entryTx, Expr.eval, word, same, hs, qs]
  have shiftLevels := shifted (.slice 3 3 (by decide) Reactive.entryWord)
    (by simp only [Expr.eval, word])
  have shiftEnabled := shifted (.slice 6 3 (by decide) Reactive.entryWord)
    (by simp only [Expr.eval, word])
  have levels : Reactive.entryLevels.eval i r = Reactive.entryLevels.eval j r := by
    simp only [Reactive.entryLevels, Reactive.isKind, Reactive.preserve, Reactive.either,
      Expr.eval, kind, word, shiftLevels]
  have enabled : Reactive.entryEnabled.eval i r = Reactive.entryEnabled.eval j r := by
    simp only [Reactive.entryEnabled, Reactive.isKind, Reactive.preserve, Reactive.either,
      Expr.eval, kind, word, shiftEnabled]
  have capture (bits : Reactive.E 6) (old : Reactive.E 16)
      (bitsEq : bits.eval i r = bits.eval j r)
      (oldEq : old.eval i r = old.eval j r) :
      (Reactive.captureBits bits old).eval i r = (Reactive.captureBits bits old).eval j r := by
    unfold Reactive.captureBits
    apply pack_congr
    intro k
    simp only [Reactive.both, Expr.eval, bitsEq, oldEq, Reactive.inputBit]
  have exit : Reactive.exitScratch.eval i r = Reactive.exitScratch.eval j r := rfl
  have entryCapture : Reactive.entryCapture.eval i r = Reactive.entryCapture.eval j r := by
    simp only [Reactive.entryCapture, Expr.eval, word]
  have captured := capture Reactive.entryCapture (.mux Reactive.starting (.lit 0) Reactive.exitScratch)
    entryCapture (by simp only [Expr.eval, hs, qs, exit])
  have scratch : Reactive.entryScratch.eval i r = Reactive.entryScratch.eval j r := by
    simp only [Reactive.entryScratch, Expr.eval, runEntry, captured, hs, qs, exit]
  have wait : Reactive.waitReady.eval i r = Reactive.waitReady.eval j r := rfl
  funext w register
  cases register
  all_goals simp [Circuit.step, Reactive.circuit, Reactive.next, Expr.eval,
    hr, ho, hs, hc, hw, qr, qo, qs, qc, qw, hm, qm,
    Reactive.cold, Reactive.either, Reactive.both, cold,
    jcold,
    stopping, consuming, appending, complete, timeout, entering, runEntry,
    entryPC, entryOuter, entryInner, entryVirtual, control, branch, entryPhase,
    Reactive.terminalCapture, Reactive.isKind, kind, word, Reactive.entryTx,
    Reactive.entryConsumed, Reactive.entryRxLength, Reactive.increment,
    Reactive.heldTimeout, Reactive.checkedReady, Reactive.busy, Reactive.isPhase,
    appended, levels, enabled, scratch, exit, wait,
    raw.symm, decide_eq_true_eq]
  all_goals with_unfolding_all simp only [decide_eq_true_eq]
  all_goals try (with_reducible rfl)
  done

theorem reactive_execution_clock (i : Values Reactive.Input) (r : Values Reactive.Register)
    (cold : i .initialize = 0) (warm : i .command ≠ 7#3)
    (busy : Reactive.busy.eval i r = 1) (retained : r .retained = 0) :
    @Circuit.step Reactive.Input Reactive.Register Reactive.Output Reactive.circuit i r =
      @Circuit.step Reactive.Input Reactive.Register Reactive.Output Reactive.circuit (quiet i) r :=
  reactive_clock i (quiet i) r (execution_controls i r cold warm busy retained) (quiet_controls i r) rfl

end Pinwheel.Hardware.Buffered.Lifecycle
