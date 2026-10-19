import Pinwheel.Hardware.Buffered.SpiExecution

/-! Packed-circuit equations used by the SPI source refinement. These statements
refer to the actual Reactive expression graph. They do not replace the circuit
with an executable surrogate or assume its observations match the source. -/
namespace Pinwheel.Hardware.Buffered.SpiCircuit
open Pinwheel.Hardware
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

def Quiet (i : Values Reactive.Input) : Prop :=
  i .initialize = 0 ∧ i .command = 0

theorem quiet_controls (i : Values Reactive.Input) (s : Values Reactive.Register)
    (h : Quiet i) :
    Reactive.resetting.eval i s = 0 ∧ Reactive.clearOwner.eval i s = 0 ∧
    Reactive.starting.eval i s = 0 ∧ Reactive.committing.eval i s = 0 ∧
    Reactive.writing.eval i s = 0 ∧ Reactive.releasing.eval i s = 0 := by
  simp [Reactive.resetting, Reactive.clearOwner, Reactive.starting,
    Reactive.committing, Reactive.writing, Reactive.releasing, Reactive.free,
    Reactive.warm, Reactive.cold, Reactive.cmd, Reactive.both, Reactive.either,
    Expr.eval, h.1, h.2]

theorem countdown_controls (i : Values Reactive.Input) (s : Values Reactive.Register)
    (h : Quiet i) (phase : s .phase = 1) (remaining : s .remaining ≠ 0) :
    Reactive.busy.eval i s = 1 ∧ Reactive.entering.eval i s = 0 ∧
    Reactive.stopping.eval i s = 0 ∧ Reactive.consuming.eval i s = 0 ∧
    Reactive.appending.eval i s = 0 ∧ Reactive.terminalEdge.eval i s = 0 := by
  have hz : decide (s Reactive.Register.remaining = 0) = false := decide_eq_false remaining
  simp [Reactive.busy, Reactive.entering, Reactive.stopping, Reactive.dispatch,
    Reactive.heldFault, Reactive.heldTimeout, Reactive.terminalEdge,
    Reactive.entryFailed, Reactive.entryComplete,
    Reactive.consuming, Reactive.appending, Reactive.runEntry, Reactive.isPhase,
    Reactive.both, Reactive.either, Expr.eval, phase,
    (quiet_controls i s h).1, (quiet_controls i s h).2.2.1]
  simp_all
  done

/-- A clock which remains inside a timed leaf changes only its duration and
the two sampler registers. All program, ownership and datapath bits are held. -/
def countdownTick (s : Values Reactive.Register) (raw : BitVec 2) :
    Values Reactive.Register
  | _, .remaining => s .remaining - 1
  | _, .stage1 => raw
  | _, .stage2 => s .stage1
  | _, r => s r

theorem countdown_step (i : Values Reactive.Input) (s : Values Reactive.Register)
    (h : Quiet i) (phase : s .phase = 1) (remaining : s .remaining ≠ 0) :
    @Circuit.step Reactive.Input Reactive.Register Reactive.Output Reactive.circuit i s =
      @countdownTick s (i .rawInputs) := by
  rcases quiet_controls i s h with ⟨hr, ho, hs, hc, hw, _⟩
  rcases countdown_controls i s h phase remaining with ⟨hb, he, ht, hn, ha, hx⟩
  funext w r
  cases r
  all_goals simp [Circuit.step, Reactive.circuit, Reactive.next, countdownTick,
    Reactive.either, Reactive.both, Reactive.cold, Reactive.warm, Reactive.cmd,
    Reactive.isPhase, Reactive.runEntry, Reactive.exitScratch, Expr.eval,
    hr, ho, hs, hc, hw, hb, he, ht, hn, ha, hx, phase, h.1, h.2]
  done

/-- Physical input sampling continues after a retained stop. The execution,
program, datapath and ownership registers remain unchanged. -/
def sampleTick (s : Values Reactive.Register) (raw : BitVec 2) :
    Values Reactive.Register
  | _, .stage1 => raw
  | _, .stage2 => s .stage1
  | _, r => s r

theorem stopped_controls (i : Values Reactive.Input) (s : Values Reactive.Register)
    (h : Quiet i) (phase : s .phase = 5 ∨ s .phase = 7) :
    Reactive.busy.eval i s = 0 ∧ Reactive.entering.eval i s = 0 ∧
    Reactive.stopping.eval i s = 0 ∧ Reactive.consuming.eval i s = 0 ∧
    Reactive.appending.eval i s = 0 ∧ Reactive.terminalEdge.eval i s = 0 := by
  rcases phase with phase | phase
  all_goals simp [Reactive.busy, Reactive.entering, Reactive.stopping, Reactive.dispatch,
    Reactive.heldFault, Reactive.heldTimeout, Reactive.terminalEdge,
    Reactive.entryFailed, Reactive.entryComplete, Reactive.consuming,
    Reactive.appending, Reactive.runEntry, Reactive.isPhase, Reactive.both,
    Reactive.either, Expr.eval, phase, (quiet_controls i s h).1,
    (quiet_controls i s h).2.2.1]

theorem stopped_step (i : Values Reactive.Input) (s : Values Reactive.Register)
    (h : Quiet i) (phase : s .phase = 5 ∨ s .phase = 7) :
    @Circuit.step Reactive.Input Reactive.Register Reactive.Output Reactive.circuit i s =
      @sampleTick s (i .rawInputs) := by
  rcases quiet_controls i s h with ⟨hr, ho, hs, hc, hw, _⟩
  rcases stopped_controls i s h phase with ⟨hb, he, ht, hn, ha, hx⟩
  have hp4 : (Reactive.isPhase 4#3).eval i s = 0 := by
    rcases phase with phase | phase
    all_goals simp [Reactive.isPhase, Expr.eval, phase]
  funext w r
  cases r
  all_goals simp [Circuit.step, Reactive.circuit, Reactive.next, sampleTick,
    Reactive.either, Reactive.both, Reactive.cold, Reactive.warm, Reactive.cmd,
    Reactive.runEntry, Reactive.exitScratch, Expr.eval,
    hr, ho, hs, hc, hw, hb, he, ht, hn, ha, hx, hp4, h.1, h.2]
  done

theorem runtime_controls (i : Values Reactive.Input) (s : Values Reactive.Register)
    (hi : SramExecution.ExecutingInput i) (release : Reactive.releasing.eval i s = 0) :
    Reactive.resetting.eval i s = 0 ∧ Reactive.clearOwner.eval i s = 0 ∧
    Reactive.committing.eval i s = 0 ∧ Reactive.writing.eval i s = 0 ∧
    Reactive.warm.eval i s = 0 := by
  have hr := SramExecution.resetting_executing i s hi
  simp [Reactive.clearOwner, Reactive.either, Reactive.committing, Reactive.writing,
    Reactive.both, Reactive.warm, Reactive.cold, Reactive.cmd, Expr.eval,
    hi.1.1, hi.1.2.1, hi.2.1, hi.2.2, hr, release]

/-- A successful nonterminal entry, expressed using the actual entry equations.
This update serves START and ordinary dispatch equally; consuming and appending
remain decisions of the circuit graph. -/
def runEntryTick (i : Values Reactive.Input) (s : Values Reactive.Register) :
    Values Reactive.Register
  | _, .transfer => if Reactive.starting.eval i s = 1 then s .transfer + 1 else s .transfer
  | _, .phase => 1
  | _, .pc => Reactive.entryPC.eval i s
  | _, .virtualPC => (Reactive.entryVirtual.eval i s).extractLsb' 0 10
  | _, .currentControl => (Reactive.entryControl.eval i s).extractLsb' 0 22
  | _, .outer => Reactive.entryOuter.eval i s
  | _, .inner => Reactive.entryInner.eval i s
  | _, .remaining => (Reactive.entryWord.eval i s).extractLsb' 9 8
  | _, .waitLeft => 0
  | _, .scratch => Reactive.entryScratch.eval i s
  | _, .cachedDuration => (Reactive.entryWord.eval i s).extractLsb' 9 8
  | _, .cachedBudget => (Reactive.entryWord.eval i s).extractLsb' 47 8
  | _, .cachedCheck => (Reactive.entryWord.eval i s).extractLsb' 41 4
  | _, .cachedWait => (Reactive.entryWord.eval i s).extractLsb' 45 2
  | _, .cachedTerminal => Reactive.terminalCapture.eval i s
  | _, .cachedBranch => (Reactive.entryBranch.eval i s).extractLsb' 0 54
  | _, .levels => Reactive.entryLevels.eval i s
  | _, .enabled => Reactive.entryEnabled.eval i s
  | _, .txData => if Reactive.consuming.eval i s = 1 then
      0#1 ++ (Reactive.entryTx.eval i s).extractLsb' 1 31 else Reactive.entryTx.eval i s
  | _, .txLength => Reactive.entryTxLength.eval i s
  | _, .txConsumed => if Reactive.consuming.eval i s = 1 then
      Reactive.entryConsumed.eval i s + 1 else Reactive.entryConsumed.eval i s
  | _, .rxData => if Reactive.appending.eval i s = 1 then Reactive.appended.eval i s
      else if Reactive.starting.eval i s = 1 then 0 else s .rxData
  | _, .rxLength => if Reactive.appending.eval i s = 1 then
      Reactive.entryRxLength.eval i s + 1 else Reactive.entryRxLength.eval i s
  | _, .rxCapacity => Reactive.entryCapacity.eval i s
  | _, .stage1 => i .rawInputs
  | _, .stage2 => s .stage1
  | _, r => s r

theorem run_entry_step (i : Values Reactive.Input) (s : Values Reactive.Register)
    (hi : SramExecution.ExecutingInput i) (release : Reactive.releasing.eval i s = 0)
    (entering : Reactive.entering.eval i s = 1) (stopping : Reactive.stopping.eval i s = 0)
    (running : Reactive.runEntry.eval i s = 1)
    (kind : Reactive.kind.eval i s = 0 ∨ Reactive.kind.eval i s = 1 ∨ Reactive.kind.eval i s = 2) :
    @Circuit.step Reactive.Input Reactive.Register Reactive.Output Reactive.circuit i s =
      @runEntryTick i s := by
  rcases runtime_controls i s hi release with ⟨hr, ho, hc, hw, hm⟩
  have kinds : (Reactive.isKind 5#3).eval i s = 0 ∧
      (Reactive.isKind 6#3).eval i s = 0 ∧ (Reactive.isKind 7#3).eval i s = 0 := by
    rcases kind with kind | kind | kind
    all_goals simp [Reactive.isKind, Expr.eval, kind]
  funext w r
  cases r
  all_goals simp [Circuit.step, Reactive.circuit, Reactive.next, runEntryTick,
    Reactive.either, Reactive.both, Reactive.cold, Reactive.entryPhase,
    Reactive.entryTx, Reactive.entryTxLength, Reactive.entryConsumed,
    Reactive.entryRxLength, Reactive.entryCapacity, Reactive.increment,
    BitVec.sub_eq_add_neg, Expr.eval, hr, ho, hc, hw, hm, hi.2.1,
    entering, stopping, running, kinds.1, kinds.2.1, kinds.2.2]
  done

/-- A non-timeout terminal entry retains all actual TX/RX updates and clears
the execution cursor and cached instruction state. -/
def stopEntryTick (i : Values Reactive.Input) (s : Values Reactive.Register) :
    Values Reactive.Register
  | _, .phase => if Reactive.entryComplete.eval i s = 1 then 5 else 7
  | _, .retained => 1
  | _, .pc => 0
  | _, .virtualPC => 0
  | _, .currentControl => 0
  | _, .outer => 0
  | _, .inner => 0
  | _, .remaining => 0
  | _, .waitLeft => 0
  | _, .cachedDuration => 0
  | _, .cachedBudget => 0
  | _, .cachedCheck => 0
  | _, .cachedWait => 0
  | _, .cachedTerminal => 0
  | _, .cachedBranch => 0
  | _, .levels => s .idleLevels
  | _, .enabled => s .idleEnabled
  | _, r => runEntryTick i s r

theorem stop_entry_step (i : Values Reactive.Input) (s : Values Reactive.Register)
    (hi : SramExecution.ExecutingInput i) (release : Reactive.releasing.eval i s = 0)
    (entering : Reactive.entering.eval i s = 1) (stopping : Reactive.stopping.eval i s = 1)
    (noTimeout : (Reactive.either Reactive.heldTimeout Reactive.entryTimeout).eval i s = 0) :
    @Circuit.step Reactive.Input Reactive.Register Reactive.Output Reactive.circuit i s =
      @stopEntryTick i s := by
  rcases runtime_controls i s hi release with ⟨hr, ho, hc, hw, hm⟩
  have ht : ~~~(~~~Reactive.heldTimeout.eval i s &&& ~~~Reactive.entryTimeout.eval i s) = 0 :=
    noTimeout
  funext w r
  cases r
  all_goals simp [Circuit.step, Reactive.circuit, Reactive.next, stopEntryTick, runEntryTick,
    Reactive.either, Reactive.both, Reactive.cold, Reactive.entryTx, Reactive.entryTxLength,
    Reactive.entryConsumed, Reactive.entryRxLength, Reactive.entryCapacity,
    Reactive.increment, BitVec.sub_eq_add_neg, Expr.eval,
    hr, ho, hc, hw, hm, hi.2.1, entering, stopping, ht]
  done

private theorem band_one : ∀ a b : BitVec 1, a &&& b = 1 ↔ a = 1 ∧ b = 1 := by
  decide +kernel

private theorem inv_one : ∀ a : BitVec 1, ~~~a = 1 ↔ a = 0 := by
  decide +kernel

private theorem ofBool_one : ∀ b : Bool, BitVec.ofBool b = 1 ↔ b = true := by
  decide +kernel

private theorem ofBool_zero : ∀ b : Bool, BitVec.ofBool b = 0 ↔ b = false := by
  decide +kernel

private theorem either_zero : ∀ a b : BitVec 1,
    ~~~(~~~a &&& ~~~b) = 0 ↔ a = 0 ∧ b = 0 := by
  decide +kernel

structure StartingFacts (i : Values Reactive.Input) (s : Values Reactive.Register) : Prop where
  cold : i .initialize = 0
  command : i .command = 3
  free : Reactive.free.eval i s = 1
  busy : Reactive.busy.eval i s = 0
  retained : s .retained = 0
  valid : s .valid = 1
  transfer : (s .transfer).toNat < 65535
  generation : i .expectedGeneration = s .generation
  txLength : (i .txLength).toNat ≤ 32
  rxCapacity : (i .rxCapacity).toNat ≤ 32

/-- Actual START acceptance derives finite transfer bounds and admission from
the graph; callers do not assume a successful source execution. -/
theorem starting_facts (i : Values Reactive.Input) (s : Values Reactive.Register)
    (starting : Reactive.starting.eval i s = 1) : StartingFacts i s := by
  simp only [Reactive.starting, Reactive.both, Expr.eval, band_one] at starting
  rcases starting with ⟨hf, hcmd, hv, ht, hg, htx, hrx⟩
  have free := hf
  simp only [Reactive.free, Reactive.both, Expr.eval, band_one, inv_one] at free
  have reset := free.1
  simp only [Reactive.resetting, Reactive.either, Expr.eval, either_zero, Reactive.cold] at reset
  have cmd : i .command = 3 :=
    of_decide_eq_true ((ofBool_one _).mp hcmd)
  have gen : i .expectedGeneration = s .generation :=
    of_decide_eq_true ((ofBool_one _).mp hg)
  have tx : (i .txLength).toNat ≤ 32 :=
    Nat.le_of_not_gt (of_decide_eq_false ((ofBool_zero _).mp ((inv_one _).mp htx)))
  have rx : (i .rxCapacity).toNat ≤ 32 :=
    Nat.le_of_not_gt (of_decide_eq_false ((ofBool_zero _).mp ((inv_one _).mp hrx)))
  have transfer_ne : s .transfer ≠ 65535 :=
    of_decide_eq_false ((ofBool_zero _).mp ((inv_one _).mp ht))
  have transfer_bound : (s .transfer).toNat < 65535 := by
    have bound := (s .transfer).isLt
    have hne : (s .transfer).toNat ≠ 65535 := by
      intro eq
      exact transfer_ne (BitVec.eq_of_toNat_eq eq)
    omega
  exact ⟨reset.1, cmd, hf, free.2.1, free.2.2, hv, transfer_bound, gen, tx, rx⟩
  done

end Pinwheel.Hardware.Buffered.SpiCircuit
