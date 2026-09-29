import Pinwheel.Hardware.Storage.PairedCoverage

/-! Running-state storage ownership for the actual paired controller.
These facts concern the current token, cached parameter and SRAM response.
They do not yet identify the clocked behavior with the E64 reference machine. -/
namespace Pinwheel.Hardware.Storage.PairedRunning
open Pinwheel.Hardware PairedController PairedUpload
set_option backward.isDefEq.respectTransparency false

def Running (s : Values Register) : Prop := s .mode ≠ 0 ∧ (s .mode).toNat < 5

def Resident (s : Values Register) (m : Memory.Sram.State 9 64) (word : BitVec 32) : Prop :=
  word = s (.boot (s .active == 1)) ∨
    ∃ (row : BitVec 8) (choice : Bool),
      word = PairedImage.select (m.contents (s .active ++ row)) choice

/-- Only running states own a usable response and parameter. Stopped states
may retain arbitrary or stale Q, as permitted by the memory contract. -/
def Ready (s : Values Register) (m : Memory.Sram.State 9 64) : Prop :=
  Running s → s .valid = 1 ∧
    s .cached = s (.parameter (s .active == 1) (PairedImage.index (s .current))) ∧
    m.q = m.contents (s .active ++ PairedImage.row (s .current)) ∧
    PairedImage.terminal (s .current) = false ∧ Resident s m (s .current)

theorem busy_wire (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s) :
    busy.eval g s = busyExpr.eval g s := by
  simpa only [busy, Expr.eval, BitVec.extractLsb'_append_eq_right] using
    congrArg (fun v : BitVec 64 => v.extractLsb' 0 1)
      (h .busy (.concat (.lit (0 : BitVec 63)) busyExpr) (by simp [bindings]))

theorem resetting_wire (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s) :
    resetting.eval g s = resettingExpr.eval g s := by
  simpa only [resetting, Expr.eval, BitVec.extractLsb'_append_eq_right] using
    congrArg (fun v : BitVec 64 => v.extractLsb' 0 1)
      (h .resetting (.concat (.lit (0 : BitVec 63)) resettingExpr) (by simp [bindings]))

theorem start_wire (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s) :
    start.eval g s = startExpr.eval g s := by
  simpa only [start, Expr.eval, BitVec.extractLsb'_append_eq_right] using
    congrArg (fun v : BitVec 64 => v.extractLsb' 0 1)
      (h .start (.concat (.lit (0 : BitVec 63)) startExpr) (by simp [bindings]))

theorem selected_wire (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s) :
    selected.eval g s = selectedExpr.eval g s := by
  simpa only [selected, Expr.eval, BitVec.extractLsb'_append_eq_right] using
    congrArg (fun v : BitVec 64 => v.extractLsb' 0 1)
      (h .selected (.concat (.lit (0 : BitVec 63)) selectedExpr) (by simp [bindings]))

theorem nextMode_wire (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s) :
    nextMode.eval g s = nextModeExpr.eval g s := by
  simpa only [nextMode, Expr.eval, BitVec.extractLsb'_append_eq_right] using
    congrArg (fun v : BitVec 64 => v.extractLsb' 0 3)
      (h .nextMode (.concat (.lit (0 : BitVec 61)) nextModeExpr) (by simp [bindings]))

theorem nextBusy_wire (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s) :
    nextBusy.eval g s = nextBusyExpr.eval g s := by
  simpa only [nextBusy, Expr.eval, BitVec.extractLsb'_append_eq_right] using
    congrArg (fun v : BitVec 64 => v.extractLsb' 0 1)
      (h .nextBusy (.concat (.lit (0 : BitVec 63)) nextBusyExpr) (by simp [bindings]))

theorem nextWord_wire (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s) :
    nextWord.eval g s = nextWordExpr.eval g s := by
  simpa only [nextWord, Expr.eval, BitVec.extractLsb'_append_eq_right] using
    congrArg (fun v : BitVec 64 => v.extractLsb' 0 32)
      (h .nextWord (.concat (.lit (0 : BitVec 32)) nextWordExpr) (by simp [bindings]))

theorem entering_wire (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s) :
    entering.eval g s = enteringExpr.eval g s := by
  simpa only [entering, Expr.eval, BitVec.extractLsb'_append_eq_right] using
    congrArg (fun v : BitVec 64 => v.extractLsb' 0 1)
      (h .entering (.concat (.lit (0 : BitVec 63)) enteringExpr) (by simp [bindings]))

theorem enteringRun_wire (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s) :
    enteringRun.eval g s = enteringRunExpr.eval g s := by
  simpa only [enteringRun, Expr.eval, BitVec.extractLsb'_append_eq_right] using
    congrArg (fun v : BitVec 64 => v.extractLsb' 0 1)
      (h .enteringRun (.concat (.lit (0 : BitVec 63)) enteringRunExpr) (by simp [bindings]))

theorem dispatch_wire (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s) :
    dispatch.eval g s = dispatchExpr.eval g s := by
  simpa only [dispatch, Expr.eval, BitVec.extractLsb'_append_eq_right] using
    congrArg (fun v : BitVec 64 => v.extractLsb' 0 1)
      (h .dispatch (.concat (.lit (0 : BitVec 63)) dispatchExpr) (by simp [bindings]))

theorem writing_wire (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s) :
    writing.eval g s = writingExpr.eval g s := by
  simpa only [writing, Expr.eval, BitVec.extractLsb'_append_eq_right] using
    congrArg (fun v : BitVec 64 => v.extractLsb' 0 1)
      (h .writing (.concat (.lit (0 : BitVec 63)) writingExpr) (by simp [bindings]))

theorem entered_wire (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s) :
    entered.eval g s = enteredExpr.eval g s := by
  simpa only [entered, Expr.eval, BitVec.extractLsb'_append_eq_right] using
    congrArg (fun v : BitVec 64 => v.extractLsb' 0 32)
      (h .entered (.concat (.lit (0 : BitVec 32)) enteredExpr) (by simp [bindings]))

theorem bootWord_wire (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s) :
    bootWord.eval g s = bootWordExpr.eval g s := by
  simpa only [bootWord, Expr.eval, BitVec.extractLsb'_append_eq_right] using
    congrArg (fun v : BitVec 64 => v.extractLsb' 0 32)
      (h .bootWord (.concat (.lit (0 : BitVec 32)) bootWordExpr) (by simp [bindings]))

theorem successor_wire (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s) :
    successor.eval g s = successorExpr.eval g s := by
  simpa only [successor, Expr.eval, BitVec.extractLsb'_append_eq_right] using
    congrArg (fun v : BitVec 64 => v.extractLsb' 0 32)
      (h .successor (.concat (.lit (0 : BitVec 32)) successorExpr) (by simp [bindings]))

theorem busy_iff (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s) : busy.eval g s = 1 ↔ Running s := by
  simp [busy_wire g s h, busyExpr, both, Expr.eval, Running]
  done

theorem nextBusy_iff (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s) :
    nextBusy.eval g s = 1 ↔ Running (body.step g s) := by
  simp [nextBusy_wire g s h, nextBusyExpr, both, Expr.eval,
    Running, Circuit.step, body, PairedController.next]
  done

theorem running_cases (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s) (hn : Running (body.step g s)) :
    resetting.eval g s = 0 ∧ commit.eval g s = 0 ∧ ending.eval g s = 0 ∧
      (enteringRun.eval g s = 1 ∨ (entering.eval g s = 0 ∧ Running s)) := by
  simp only [Running, Circuit.step, body, PairedController.next, nextMode_wire g s h,
    nextModeExpr, either, isKind, kind, Expr.eval] at hn
  rcases bit_cases (resetting.eval g s) with hr | hr <;> simp_all
  all_goals rcases bit_cases (commit.eval g s) with hc | hc <;> simp_all
  all_goals rcases bit_cases (ending.eval g s) with he | he <;> simp_all
  case inl.inl.inr => split at hn <;> simp_all
  rcases bit_cases (entering.eval g s) with hi | hi <;> simp_all [Running]
  by_cases hk : (entered.eval g s).extractLsb' 0 3 = 4 <;>
    simp_all [enteringRun_wire g s h, enteringRunExpr, terminal, either, both, isKind, kind, Expr.eval]
  by_cases hk7 : (entered.eval g s).extractLsb' 0 3 = 7 <;> simp_all
  done

private theorem bit_not_one (a : BitVec 1) : ~~~a = 1 ↔ a = 0 := by
  rcases bit_cases a with h | h <;> simp_all

private theorem bit_or_one (a b : BitVec 1) :
    ~~~(~~~a &&& ~~~b) = 1 ↔ a = 1 ∨ b = 1 := by
  rcases bit_cases a with ha | ha <;> rcases bit_cases b with hb | hb <;> simp_all

theorem start_conditions (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s) :
    start.eval g s = 1 ↔ accepting.eval g s = 1 ∧ g (.base .command) = 5 ∧ s .valid = 1 := by
  simp only [start_wire g s h, startExpr, both, cmd, Expr.eval,
    bit_and_one, Reactive.bool_one, decide_eq_true_eq]

theorem entering_source (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s) (he : entering.eval g s = 1) :
    resetting.eval g s = 0 ∧ (start.eval g s = 1 ∨ Running s) := by
  simp only [entering_wire g s h, enteringExpr, both, either, Expr.eval,
    bit_and_one, bit_or_one] at he
  refine ⟨(bit_not_one _).mp he.1, he.2.imp id (fun hd => ?_)⟩
  exact (busy_iff g s h).mp
    ((bit_and_one _ _).mp ((dispatch_wire g s h).symm.trans hd)).1
  done

theorem no_upload (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s)
    (hb : Running s ∨ g (.base .command) = 5) :
    validating.eval g s = 0 ∧ push.eval g s = 0 := by
  rcases hb with hb | hc
  · simp [(PairedSemantics.upstream_equations g s h).validating, validatingExpr,
      both, cmd, Expr.eval, accepting_value g s h, push_value g s h,
      PairedLoader.push, Loader.enabled, PairedUpload.inputs, (busy_iff g s h).mpr hb]
  · simp [(PairedSemantics.upstream_equations g s h).validating, validatingExpr,
      both, cmd, Expr.eval, push_value g s h, PairedLoader.push, PairedUpload.inputs, hc]
  all_goals done

theorem running_source (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s) (hn : Running (body.step g s)) :
    Running s ∨ start.eval g s = 1 := by
  exact (running_cases g s h hn).2.2.2.elim
    (fun he => (entering_source g s h
      ((bit_and_one _ _).mp ((enteringRun_wire g s h).symm.trans he)).1).2.symm)
    (fun he => Or.inl he.2)

theorem running_no_upload (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s) (hn : Running (body.step g s)) :
    validating.eval g s = 0 ∧ push.eval g s = 0 := by
  exact no_upload g s h ((running_source g s h hn).imp_right
    (fun hs => ((start_conditions g s h).mp hs).2.1))

private theorem bit_or_zero (a b : BitVec 1) :
    ~~~(~~~a &&& ~~~b) = 0 ↔ a = 0 ∧ b = 0 := by
  rcases bit_cases a with ha | ha <;> rcases bit_cases b with hb | hb <;> simp_all

theorem resetting_zero (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s) :
    resetting.eval g s = 0 ↔ init.eval g s = 0 ∧ reset.eval g s = 0 := by
  simp only [resetting_wire g s h, resettingExpr, either, Expr.eval, bit_or_zero]

theorem entry_parameter (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s) (hv : validating.eval g s = 0) :
    parameter0.eval g s =
      s (.parameter (s .active == 1) (PairedImage.index (entered.eval g s))) := by
  simp [(PairedSemantics.upstream_equations g s h).parameter0, parameter0Expr,
    lookup, (PairedSemantics.upstream_equations g s h).bank, parameterBankExpr,
    (PairedSemantics.upstream_equations g s h).index0, parameterIndex0Expr,
    index, PairedImage.index, hv, Execution.readTree_correct, Expr.eval]
  by_cases ha : s .active = 1 <;> simp_all [Bool.beq_eq_decide_eq]
  done

theorem running_control (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s) (hn : Running (body.step g s)) :
    body.step g s .active = s .active ∧ body.step g s .valid = s .valid := by
  simp [Circuit.step, body, PairedController.next, Expr.eval, selected_wire g s h,
    selectedExpr, either, (running_cases g s h hn).2.1,
    ((resetting_zero g s h).mp (running_cases g s h hn).1).1]
  rcases bit_cases (s .valid) with hv | hv <;> simp_all
  done

theorem running_read (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s) (hn : Running (body.step g s)) :
    (request .read).eval g s = 1 := by
  simp [request, both, Expr.eval, writing_wire g s h, writingExpr,
    (running_no_upload g s h hn).2, (nextBusy_iff g s h).mpr hn]

theorem running_parameter (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s) (hn : Running (body.step g s))
    (b : Bool) (k : BitVec 5) :
    body.step g s (.parameter b k) = s (.parameter b k) := by
  simp [Circuit.step, body, PairedController.next, both, Expr.eval,
    (running_no_upload g s h hn).2]

theorem running_memory (g : Values GraphInput) (s : Values Register)
    (m : Memory.Sram.State 9 64) (h : PairedSemantics.Equations bindings g s)
    (hn : Running (body.step g s)) :
    (memoryNext g s m).contents = m.contents ∧
      (memoryNext g s m).q =
        m.contents (s .active ++ PairedImage.row (body.step g s .current)) := by
  have hw : writing.eval g s = 0 :=
    PairedSemantics.request_exclusive g s (running_read g s h hn)
  simp only [memoryNext, PairedClosed.command, Circuit.observe, body,
    (show (request .write).eval g s = 0 from hw), running_read g s h hn,
    BitVec.reduceEq, Bool.false_eq_true, if_false, if_true,
    Memory.SinglePort.step, Memory.Sram.State.step]
  simp [request, row, Expr.eval, hw,
    PairedImage.row, Circuit.step, PairedController.next]
  done

theorem running_boot (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s) (hn : Running (body.step g s)) (b : Bool) :
    body.step g s (.boot b) = s (.boot b) := by
  simp [Circuit.step, body, PairedController.next, both, Expr.eval,
    (running_no_upload g s h hn).2]

theorem terminal_value (g : Values GraphInput) (s : Values Register) (word : E 32) :
    (terminal word).eval g s = BitVec.ofBool (PairedImage.terminal (word.eval g s)) := by
  simp [terminal, either, isKind, kind, PairedImage.terminal, Expr.eval, Bool.beq_eq_decide_eq]
  done

theorem entry_nonterminal (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s) (he : enteringRun.eval g s = 1) :
    PairedImage.terminal (entered.eval g s) = false := by
  have ht := (bit_not_one _).mp
    ((bit_and_one _ _).mp ((enteringRun_wire g s h).symm.trans he)).2
  cases hp : PairedImage.terminal (entered.eval g s) <;> simp_all [terminal_value]
  done

theorem resident_preserved (g : Values GraphInput) (s : Values Register)
    (m : Memory.Sram.State 9 64) (h : PairedSemantics.Equations bindings g s)
    (hn : Running (body.step g s)) (word : BitVec 32) :
    Resident (body.step g s) (memoryNext g s m) word ↔ Resident s m word := by
  simp only [Resident, running_boot g s h hn, (running_control g s h hn).1,
    (running_memory g s m h hn).1]

theorem successor_value (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s) :
    successor.eval g s = PairedImage.select (g (.q false)) (branch.eval g s == 1) := by
  simp only [successor_wire g s h, successorExpr, Expr.eval, PairedImage.select, beq_iff_eq]

theorem bootWord_value (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s) :
    bootWord.eval g s = s (.boot (s .active == 1)) := by
  by_cases ha : s .active = 1 <;>
    simp_all [bootWord_wire g s h, bootWordExpr, Expr.eval, Bool.beq_eq_decide_eq]

theorem current_next (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s) :
    body.step g s .current = if entering.eval g s = 1 then entered.eval g s else s .current := by
  simp only [Circuit.step, body, PairedController.next, nextWord_wire g s h, nextWordExpr, Expr.eval]

theorem ready_next (g : Values GraphInput) (s : Values Register)
    (m : Memory.Sram.State 9 64) (h : PairedSemantics.Equations bindings g s)
    (hq : g (.q false) = m.q)
    (hr : Ready s m) : Ready (body.step g s) (memoryNext g s m) := by
  intro hn
  refine ⟨(running_control g s h hn).2.trans
    ((running_source g s h hn).elim (fun hb => (hr hb).1)
      (fun hs => ((start_conditions g s h).mp hs).2.2)), ?_, ?_, ?_, ?_⟩
  · change body.step g s .cached = body.step g s
      (.parameter (body.step g s .active == 1) (PairedImage.index (body.step g s .current)))
    rw [running_parameter g s h hn, (running_control g s h hn).1]
    rcases (running_cases g s h hn).2.2.2 with he | he
    · simpa [Circuit.step, body, PairedController.next, Expr.eval, he,
        nextWord_wire g s h, nextWordExpr,
        ((bit_and_one _ _).mp ((enteringRun_wire g s h).symm.trans he)).1] using
        entry_parameter g s h (running_no_upload g s h hn).1
    · simpa [Circuit.step, body, PairedController.next, Expr.eval,
        nextWord_wire g s h, nextWordExpr, enteringRun_wire g s h, enteringRunExpr,
        both, he.1] using (hr he.2).2.1
  · simpa only [(running_memory g s m h hn).1, (running_control g s h hn).1] using
      (running_memory g s m h hn).2
  · rcases (running_cases g s h hn).2.2.2 with he | he
    · simpa [Circuit.step, body, PairedController.next, nextWord_wire g s h,
        nextWordExpr, Expr.eval,
        ((bit_and_one _ _).mp ((enteringRun_wire g s h).symm.trans he)).1] using
        entry_nonterminal g s h he
    · simpa [Circuit.step, body, PairedController.next, nextWord_wire g s h,
        nextWordExpr, Expr.eval, he.1] using (hr he.2).2.2.2.1
  · apply (resident_preserved g s m h hn _).mpr
    rcases (running_cases g s h hn).2.2.2 with he | he
    · simp only [Circuit.step, body, PairedController.next, nextWord_wire g s h,
        nextWordExpr, Expr.eval,
        ((bit_and_one _ _).mp ((enteringRun_wire g s h).symm.trans he)).1, if_true,
        entered_wire g s h, enteredExpr]
      split
      next hb => exact Or.inr ⟨PairedImage.row (s .current), branch.eval g s == 1,
        (successor_value g s h).trans
          (congrArg (fun q => PairedImage.select q (branch.eval g s == 1))
            (hq.trans (hr ((busy_iff g s h).mp hb)).2.2.1))⟩
      next => exact Or.inl (bootWord_value g s h)
    · simpa only [current_next g s h, he.1, BitVec.reduceEq, if_false] using
        (hr he.2).2.2.2.2
  done

theorem not_running_initialize (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s) (hi : init.eval g s = 1) :
    ¬Running (body.step g s) := by
  exact fun hn => (by decide : (1 : BitVec 1) ≠ 0)
    (hi.symm.trans ((resetting_zero g s h).mp (running_cases g s h hn).1).1)

theorem ready_initialize (g : Values GraphInput) (s : Values Register)
    (m : Memory.Sram.State 9 64) (h : PairedSemantics.Equations bindings g s)
    (hi : init.eval g s = 1) : Ready (body.step g s) (memoryNext g s m) := by
  exact fun hn => False.elim (not_running_initialize g s h hi hn)

/-- The selected OLD memory response supplies the actual entering token. -/
theorem dispatch_current (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s) (hb : Running s)
    (he : entering.eval g s = 1) :
    body.step g s .current = PairedImage.select (g (.q false)) (branch.eval g s == 1) := by
  simp only [current_next g s h, he, if_true, entered_wire g s h, enteredExpr, Expr.eval,
    (busy_iff g s h).mpr hb, successor_value g s h]

end Pinwheel.Hardware.Storage.PairedRunning
