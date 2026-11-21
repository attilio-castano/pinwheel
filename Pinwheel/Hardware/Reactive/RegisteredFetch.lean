import Pinwheel.Hardware.Reactive.Emit

/-! An alternate fetch schedule for the programmable Reactive core. A
    designated checked-instruction terminal edge requests its successor and
    holds the scheduler. On the next edge the scheduler consumes the stored
    word. All other instructions use the existing combinational fetch. -/
namespace Pinwheel.Hardware.Reactive.RegisteredFetch

open Pinwheel.Hardware

abbrev Base := Core.Register Execution.DirectReg

inductive Register : Nat → Type where
  | base : Base w → Register w
  | savedWord : Register 64
  | response : Register 1

inductive Output : Nat → Type where
  | base : Reactive.Output w → Output w
  | fetchWait : Output 1

abbrev E := Expr Core.Input Register

def lift (expr : Core.E Execution.DirectReg w) : E w :=
  expr.bind (fun p => .input p) (fun r => .reg (.base r))

def project (s : Values Register) : Values Base := fun r => s (.base r)

private def core (r : Reactive.Register w) : E w := .reg (.base (.core r))

/-- The covered instruction still has its current pins and captures on the
    fetch-request edge. RESET always bypasses the delay. -/
def fetchWait (cut : BitVec 8) : E 1 :=
  .band (.inv (.input .reset))
    (.band (.inv (.reg .response))
      (.band (.equal (core .mode) (.lit 3))
        (.band (.equal (core .pc) (.lit cut)) (.zero (core .remaining)))))

def requestedWord : E 64 :=
  lift (Core.schedulerInputs Core.direct .successor)

def schedulerInputs : {w : Nat} → Reactive.Input w → E w
  | _, .successor => .mux (.reg .response) (.reg .savedWord) requestedWord
  | _, p => lift (Core.baseInputs Core.direct p)

def circuit (cut : BitVec 8) : Circuit Core.Input Register Output where
  next := fun r => match r with
    | .response => fetchWait cut
    | .savedWord => .mux (fetchWait cut) requestedWord (.reg .savedWord)
    | .base (.core r) => .mux (fetchWait cut) (core r)
        ((Reactive.circuit.next r).bind schedulerInputs core)
    | .base r => lift ((Core.circuit Core.direct).next r)
  output := fun o => match o with
    | .base p => lift ((Core.circuit Core.direct).output p)
    | .fetchWait => fetchWait cut

def moduleText (name : String) (cut : BitVec 8) : Except String String :=
  Core.moduleTextScheduled name Core.direct Execution.directRegisters Execution.directRegisterLabel
    fun fetched => do
      let registerName : {w : Nat} → Register w → String
        | _, .base r => "%r_" ++ Core.registerLabel Execution.directRegisterLabel r
        | _, .savedWord => "%r_saved_successor"
        | _, .response => "%r_fetch_response"
      let request ← Emit.expression (fun i => "%" ++ Core.inputLabel i) registerName (fetchWait cut)
      let next ← Emit.expression (fun p => if p then request else fetched) registerName
        (.mux (.input true) (.input false) (.reg .savedWord) : Expr (fun _ => Bool) Register 64)
      let selected ← Emit.expression (fun _ => fetched) registerName
        (.mux (.reg .response) (.reg .savedWord) (.input ()) : Expr (fun _ => Unit) Register 64)
      return ⟨selected, some request,
        #[s!"    %r_saved_successor = seq.compreg {next}, %clock : i64",
          s!"    %r_fetch_response = seq.compreg {request}, %clock : i1"], some request⟩

theorem lift_eval (expr : Core.E Execution.DirectReg w) (i : Values Core.Input) (s : Values Register) :
    (lift expr).eval i s = expr.eval i (project s) := by
  rw [lift, Expr.eval_bind]
  rfl

theorem fetchWait_eq_one (cut : BitVec 8) (i : Values Core.Input) (s : Values Register) :
    (fetchWait cut).eval i s = 1 ↔ i .reset = 0 ∧ s .response = 0 ∧
      (project s) (.core .mode) = 3 ∧ (project s) (.core .pc) = cut ∧
      (project s) (.core .remaining) = 0 := by
  have andOne : ∀ x y : BitVec 1, x &&& y = 1 ↔ x = 1 ∧ y = 1 := by decide +kernel
  have notOne : ∀ x : BitVec 1, ~~~x = 1 ↔ x = 0 := by decide +kernel
  simp only [fetchWait, core, project, Expr.eval, andOne, notOne]
  simp
  intro _ _
  constructor
  · rintro ⟨mode, pc, time⟩
    exact ⟨of_decide_eq_true mode, of_decide_eq_true pc, of_decide_eq_true time⟩
  · rintro ⟨mode, pc, time⟩
    exact ⟨decide_eq_true mode, decide_eq_true pc, decide_eq_true time⟩

theorem no_wait_of_response (cut : BitVec 8) (i : Values Core.Input) (s : Values Register)
    (ready : s .response = 1) : (fetchWait cut).eval i s = 0 := by
  simp [fetchWait, Expr.eval, ready]

theorem observe_matches (cut : BitVec 8) (i : Values Core.Input) (s : Values Register)
    (p : Reactive.Output w) :
    (circuit cut).observe i s (.base p) = (Core.circuit Core.direct).observe i (project s) p :=
  lift_eval _ _ _

theorem request_saved (cut : BitVec 8) (i : Values Core.Input) (s : Values Register)
    (waiting : (fetchWait cut).eval i s = 1) :
    ((circuit cut).step i s) .response = 1 ∧
      ((circuit cut).step i s) .savedWord = requestedWord.eval i s := by
  simp [Circuit.step, circuit, Expr.eval, waiting]

theorem no_response (cut : BitVec 8) (i : Values Core.Input) (s : Values Register)
    (moving : (fetchWait cut).eval i s = 0) :
    ((circuit cut).step i s) .response = 0 := moving

theorem hold_scheduler (cut : BitVec 8) (i : Values Core.Input) (s : Values Register)
    (waiting : (fetchWait cut).eval i s = 1) (r : Reactive.Register w) :
    (project ((circuit cut).step i s)) (.core r) = (project s) (.core r) := by
  simp [project, Circuit.step, circuit, core, Expr.eval, waiting]

/-- A fetch request leaves the complete original state unchanged. The
    existing write protection already holds the loaded image while busy. -/
theorem hold_project (cut : BitVec 8) (i : Values Core.Input) (s : Values Register)
    (waiting : (fetchWait cut).eval i s = 1) :
    @project ((circuit cut).step i s) = @project s := by
  have mode := ((fetchWait_eq_one cut i s).mp waiting).2.2.1
  have busy : (Core.busy (M := Execution.DirectReg)).eval i (project s) = 1 := by
    simp [Core.busy, Expr.eval_bind, Reactive.running, Core.coreReg, Expr.eval, mode]
  have writesBlocked : (Core.blocked (M := Execution.DirectReg)).eval i (project s) = 1 := by
    simp [Core.blocked, Expr.eval, busy]
  funext b r
  cases r with
  | core r => exact hold_scheduler cut i s waiting r
  | memory r =>
    cases r
    change (lift ((Core.circuit Core.direct).next (.memory (.word _)))).eval i s = _
    simp [lift_eval, Core.circuit, Core.direct, Execution.directCircuit, Execution.writeWord,
      Execution.accept, Expr.eval_bind, Expr.eval, Core.memoryInputs, writesBlocked, Core.memoryReg]
  | _ =>
    change (lift ((Core.circuit Core.direct).next _)).eval i s = _
    simp [lift_eval, Core.circuit, Core.metadataWrite, Expr.eval, writesBlocked]

theorem step_matches (cut : BitVec 8) (i : Values Core.Input) (s : Values Register)
    (moving : (fetchWait cut).eval i s = 0)
    (ready : s .response = 0 ∨ s .savedWord = requestedWord.eval i s) :
    @project ((circuit cut).step i s) =
      ((Core.circuit Core.direct).step i (project s) : Values Base) := by
  have inputs : @((fun {b} (p : Reactive.Input b) => (schedulerInputs p).eval i s) : Values Reactive.Input) =
      (fun {b} p => (Core.schedulerInputs Core.direct (w := b) p).eval i (project s)) := by
    funext b p
    cases p <;> try exact lift_eval _ _ _
    change (if s .response = 1 then s .savedWord else requestedWord.eval i s) = _
    rw [← lift_eval]
    rcases ready with h | h <;> simp [requestedWord, h]
  funext b r
  cases r with
  | core r =>
    simp only [project, Circuit.step, circuit, Core.circuit, Expr.eval, moving,
      if_neg (by decide : (0 : BitVec 1) ≠ 1), Expr.eval_bind, inputs, core, Core.coreReg]
  | _ => exact lift_eval _ _ _

/-- A checked instruction with its branch bit already captured chooses the
    same successor for every raw input on the held and resumed edge. -/
theorem requestedWord_captureless (p : Program) (state : Reactive.State)
    (s : Values Register) (first resumed : Core.Inputs)
    (represented : @project s = @Core.values Execution.DirectReg state
      (Execution.directValues (Execution.imageWords p)) p.idle (BitVec.ofFin p.last))
    (checked : Engine.Reactive.Checked 255 15) (word : p.fetch state.pc.toFin = .checked checked)
    (captured : checked.terminalCapture = none) :
    requestedWord.eval first.values s = requestedWord.eval resumed.values s := by
  have terminal :
      Execution.getCapture (Execution.unpack (Execution.encode (.checked checked))).terminal = none := by
    cases finish : checked.finish <;>
      simp [Execution.encode, Execution.unpack_pack, Execution.fields, Execution.actionFields,
        Execution.finishFields, Execution.capture_roundtrip, finish, captured]
  simp only [requestedWord, lift_eval, represented, Core.inputs_correct _ _ _ (Core.direct_represents p)]
  simp only [Reactive.Inputs.values, feed, targetValue, sequentialValue, terminalValues,
    word, terminal, Engine.Reactive.capture]

/-- The request and response occupy two physical edges. The projected
    operation is the original scheduler step on the resumed edge. -/
theorem request_then_resume (cut : BitVec 8) (first resumed : Values Core.Input) (s : Values Register)
    (waiting : (fetchWait cut).eval first s = 1)
    (same : requestedWord.eval first s = requestedWord.eval resumed s) :
    @project ((circuit cut).step resumed ((circuit cut).step first s)) =
      ((Core.circuit Core.direct).step resumed (project s) : Values Base) := by
  have saved := request_saved cut first s waiting
  have hold := hold_project cut first s waiting
  have word : requestedWord.eval resumed ((circuit cut).step first s) = requestedWord.eval resumed s := by
    simp only [requestedWord, lift_eval, hold]
  rw [step_matches cut resumed _ (no_wait_of_response cut resumed _ saved.1)
    (Or.inr (saved.2.trans (same.trans word.symm))), hold]

end Pinwheel.Hardware.Reactive.RegisteredFetch
