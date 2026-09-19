import Pinwheel.Hardware.Storage.Prefetch

/-! What the scheduler decides on an edge, separated from the decode of the word
it enters.

Whether an edge dispatches (`advancing`, `dispatching`) and where to (`Reactive.targetValue`)
are known before the validity, halt and range checks of the entered word. Every
fetch organization that reads ahead builds on these facts: the candidates of the
next edge follow from the decision (`candidate`, `candidate_correct`), an edge
without a dispatch does not consult the successor (`step_successor_irrelevant`),
and only a branching `checked` record has two distinct candidates
(`candidate_nonbranching`). The decision and the candidates also exist as
scheduler expressions for netlists. -/
namespace Pinwheel.Hardware.Storage.Dispatch
open Loader

/-- The scheduler enters a successor on this edge, before validity, halt and the
range check are known: the cases of `advanceValue` that reach `dispatchValue`,
or a start from rest. -/
def advancing (i : Reactive.Inputs) (s : Reactive.State) : Bool :=
  let kind := (Execution.unpack i.current).kind
  if s.mode = 1 then s.remaining = 0
  else if s.mode = 2 then kind == 1 && Reactive.readyValue i
  else if s.mode = 3 then kind == 2 && Reactive.guardValue i && s.remaining = 0
  else kind == 3 && Reactive.guardValue i && s.remaining = 0

def dispatching (i : Reactive.Inputs) (s : Reactive.State) : Bool :=
  !i.reset && (if Reactive.runningValue s then advancing i s else i.start)

/-- The candidates of the next edge, from this edge's decision: after a dispatch
the successors of the word being entered at the target; otherwise those of the
current word at the current address. Meaningful only when the machine keeps
running. -/
def candidate (i : Reactive.Inputs) (s : Reactive.State) (b : Bool) : BitVec 8 :=
  if dispatching i s then
    let d := Execution.unpack i.successor
    if d.kind != 2 || d.finish == 0 then Reactive.targetValue i s - 255
    else if d.finish = 1 then d.yes else if b then d.yes else d.no
  else
    let d := Execution.unpack i.current
    if s.mode != 3 || d.finish == 0 then s.pc - 255
    else if d.finish = 1 then d.yes else if b then d.yes else d.no

/-- The candidates after a dispatch: the successors of the word being entered. -/
def entered (i : Reactive.Inputs) (s : Reactive.State) (b : Bool) : BitVec 8 :=
  let d := Execution.unpack i.successor
  if d.kind != 2 || d.finish == 0 then Reactive.targetValue i s - 255
  else if d.finish = 1 then d.yes else if b then d.yes else d.no

/-- The candidates without a dispatch: the successors of the current word. -/
def held (i : Reactive.Inputs) (s : Reactive.State) (b : Bool) : BitVec 8 :=
  let d := Execution.unpack i.current
  if s.mode != 3 || d.finish == 0 then s.pc - 255
  else if d.finish = 1 then d.yes else if b then d.yes else d.no

theorem candidate_split (i : Reactive.Inputs) (s : Reactive.State) (b : Bool) :
    candidate i s b = if dispatching i s then entered i s b else held i s b := rfl

/-! ### What the scheduler does on an edge it keeps running -/

theorem modeOf_three (k : BitVec 3) :
    ((if k = 0#3 then (1#3) else if k = 1#3 then 2#3 else if k = 2#3 then 3#3 else 4#3) = 3#3) ↔ k = 2#3 := by
  by_cases h0 : k = 0#3 <;> by_cases h1 : k = 1#3 <;> by_cases h2 : k = 2#3 <;> simp [h0, h1, h2]

/-- Entering a word that keeps the machine running sets the target as the
address and a mode of 3 exactly for a `checked` word. -/
theorem entry_structure (i : Reactive.Inputs) (s : Reactive.State)
    (h : Reactive.runningValue (Reactive.entryValue i s) = true) :
    (Reactive.entryValue i s).pc = Reactive.targetValue i s ∧
      ((Reactive.entryValue i s).mode = 3 ↔ (Execution.unpack i.successor).kind = 2) := by
  simp only [Reactive.entryValue, Reactive.enterValue] at h ⊢
  by_cases hv : Execution.validValue i.successor = true
  · by_cases hk : (Execution.unpack i.successor).kind = 4
    · simp [hv, hk, Reactive.stopValue, Reactive.runningValue] at h
    · rw [if_pos hv, if_neg hk]
      exact ⟨rfl, modeOf_three _⟩
  · simp [hv, Reactive.stopValue, Reactive.runningValue] at h

theorem dispatch_structure (i : Reactive.Inputs) (s : Reactive.State)
    (h : Reactive.runningValue (Reactive.dispatchValue i s) = true) :
    Reactive.dispatchValue i s = Reactive.entryValue i s := by
  simp only [Reactive.dispatchValue] at h ⊢
  by_cases hr : Reactive.rangeValue i s = true
  · simp [hr]
  · simp [hr, Reactive.stopValue, Reactive.runningValue] at h

/-- On an edge that keeps the machine running, `advanceValue` dispatches exactly
when `advancing` says so, and otherwise keeps the address and the mode. -/
theorem advance_structure (i : Reactive.Inputs) (s : Reactive.State)
    (h : Reactive.runningValue (Reactive.advanceValue i s) = true) :
    (advancing i s = true → Reactive.advanceValue i s = Reactive.dispatchValue i s) ∧
    (advancing i s = false → (Reactive.advanceValue i s).pc = s.pc ∧ (Reactive.advanceValue i s).mode = s.mode) := by
  simp only [Reactive.advanceValue, Reactive.currentKindValue, advancing] at h ⊢
  by_cases m1 : s.mode = 1
  · by_cases hr : s.remaining = 0 <;> simp_all [Reactive.decrementValue]
  by_cases m2 : s.mode = 2
  · by_cases hv : Execution.validValue i.current = true <;>
      by_cases hk : (Execution.unpack i.current).kind = 1 <;>
      by_cases hready : Reactive.readyValue i = true <;>
      by_cases hr : s.remaining = 0 <;>
      simp_all [Reactive.decrementValue, Reactive.stopValue, Reactive.runningValue]
  by_cases m3 : s.mode = 3
  · by_cases hv : Execution.validValue i.current = true <;>
      by_cases hk : (Execution.unpack i.current).kind = 2 <;>
      by_cases hg : Reactive.guardValue i = true <;>
      by_cases hr : s.remaining = 0 <;>
      simp_all [Reactive.decrementValue, Reactive.stopValue, Reactive.runningValue]
  · by_cases hv : Execution.validValue i.current = true <;>
      by_cases hk : (Execution.unpack i.current).kind = 3 <;>
      by_cases hg : Reactive.guardValue i = true <;>
      by_cases hr : s.remaining = 0 <;>
      by_cases hw : s.waitLeft = 0 <;>
      simp_all [Reactive.progressValue, Reactive.retryValue, Reactive.stopValue, Reactive.runningValue]

/-- The crux: on an edge that keeps the machine running, a dispatch enters the
successor at the target with the mode its kind determines, and no dispatch keeps
the address, the mode and the current word. -/
theorem step_structure (i : Reactive.Inputs) (s : Reactive.State)
    (h : Reactive.runningValue (Reactive.stepValue i s) = true) :
    (dispatching i s = true →
      (Reactive.stepValue i s).pc = Reactive.targetValue i s ∧
      ((Reactive.stepValue i s).mode = 3 ↔ (Execution.unpack i.successor).kind = 2)) ∧
    (dispatching i s = false →
      (Reactive.stepValue i s).pc = s.pc ∧ (Reactive.stepValue i s).mode = s.mode ∧
      Reactive.runningValue s = true) := by
  have hr : i.reset = false := Cache.running_reset i s h
  simp only [Reactive.stepValue, hr, Bool.false_eq_true, if_false] at h ⊢
  by_cases hb : Reactive.runningValue s = true
  · simp only [hb, if_true] at h ⊢
    obtain ⟨hd, hs⟩ := advance_structure i s h
    simp only [dispatching, hr, hb, Bool.not_false, Bool.true_and, if_true]
    refine ⟨fun ha => ?_, fun ha => ⟨(hs ha).1, (hs ha).2, by first | trivial | exact hb⟩⟩
    rw [hd ha] at h ⊢
    have hd' := dispatch_structure i s h
    rw [hd'] at h ⊢
    exact entry_structure i s h
  · have hb' : Reactive.runningValue s = false := by simpa using hb
    simp only [hb', Bool.false_eq_true, if_false] at h ⊢
    simp only [dispatching, hr, hb', Bool.not_false, Bool.true_and]
    by_cases hs : i.start = true
    · simp only [hs, if_true] at h ⊢
      exact ⟨fun _ => entry_structure i s h, fun h' => by simp at h'⟩
    · simp only [hs, Bool.false_eq_true, if_false] at h
      exact absurd h (by simpa using hb)

/-- Hence the decoupled candidates are the canonical ones of the next state
whenever the machine keeps running. -/
theorem candidate_correct (i : Reactive.Inputs) (s : Reactive.State) (b : Bool)
    (h : Reactive.runningValue (Reactive.stepValue i s) = true) :
    candidate i s b = Storage.Prefetch.candidate (Reactive.stepValue i s)
      (if dispatching i s || !Reactive.runningValue s then i.successor else i.current) b := by
  obtain ⟨hd, hs⟩ := step_structure i s h
  by_cases hdis : dispatching i s = true
  · obtain ⟨hpc, hmode⟩ := hd hdis
    simp only [candidate, Storage.Prefetch.candidate, hdis, if_true, Bool.true_or, h, hpc]
    by_cases hk : (Execution.unpack i.successor).kind = 2#3
    · have hm3 : (Reactive.stepValue i s).mode = 3#3 := hmode.mpr hk
      simp [hk, hm3]
    · have hm3 : ¬ (Reactive.stepValue i s).mode = 3#3 := fun h3 => hk (hmode.mp h3)
      simp [hk, hm3]
  · have hdis' : dispatching i s = false := by simpa using hdis
    obtain ⟨hpc, hmode, hrun⟩ := hs hdis'
    simp only [candidate, Storage.Prefetch.candidate, hdis', Bool.false_or, hrun, Bool.not_true,
      Bool.false_eq_true, if_false, h, if_true, hpc, hmode]

/-! ### Edges without a dispatch, and what a dispatch enters -/

/-- Without a dispatch, the successor input is not consulted. -/
theorem step_successor_irrelevant (i : Reactive.Inputs) (s : Reactive.State) (x : BitVec 64)
    (h : dispatching i s = false) :
    Reactive.stepValue {i with successor := x} s = Reactive.stepValue i s := by
  simp only [dispatching, Bool.and_eq_false_iff, Bool.not_eq_false'] at h
  cases hr : i.reset
  · simp only [hr, Bool.false_eq_true, false_or] at h
    cases hb : Reactive.runningValue s
    · simp only [hb, Bool.false_eq_true, if_false] at h
      simp [Reactive.stepValue, hr, hb, h]
    · simp only [hb, if_true] at h
      simp only [Reactive.stepValue, hr, hb, Bool.false_eq_true, if_false, if_true]
      simp only [Reactive.advanceValue, Reactive.currentKindValue, advancing] at h ⊢
      by_cases m1 : s.mode = 1
      · by_cases hrem : s.remaining = 0 <;> simp_all [Reactive.decrementValue]
      by_cases m2 : s.mode = 2
      · by_cases hk : (Execution.unpack i.current).kind = 1 <;>
          by_cases hready : Reactive.readyValue i = true <;>
          by_cases hrem : s.remaining = 0 <;>
          simp_all [Reactive.decrementValue, Reactive.stopValue, Reactive.readyValue]
      by_cases m3 : s.mode = 3
      · by_cases hk : (Execution.unpack i.current).kind = 2 <;>
          by_cases hg : Reactive.guardValue i = true <;>
          by_cases hrem : s.remaining = 0 <;>
          simp_all [Reactive.decrementValue, Reactive.stopValue, Reactive.guardValue]
      · by_cases hk : (Execution.unpack i.current).kind = 3 <;>
          by_cases hg : Reactive.guardValue i = true <;>
          by_cases hrem : s.remaining = 0 <;>
          by_cases hw : s.waitLeft = 0 <;>
          simp_all [Reactive.progressValue, Reactive.retryValue, Reactive.stopValue, Reactive.guardValue]
  · simp [Reactive.stepValue, hr, Reactive.stopValue]

/-- A dispatch that keeps the machine running entered a valid word, with the
word's duration as the remaining count. -/
theorem dispatch_entered (i : Reactive.Inputs) (s : Reactive.State)
    (h : Reactive.runningValue (Reactive.stepValue i s) = true)
    (hd : dispatching i s = true) :
    (Reactive.stepValue i s).remaining = (Execution.unpack i.successor).duration ∧
      Execution.validValue i.successor = true := by
  have hr : i.reset = false := Cache.running_reset i s h
  have entered : Reactive.stepValue i s = Reactive.entryValue i s := by
    simp only [Reactive.stepValue, hr, Bool.false_eq_true, if_false] at h ⊢
    simp only [dispatching, hr, Bool.not_false, Bool.true_and] at hd
    by_cases hb : Reactive.runningValue s = true
    · simp only [hb, if_true] at h hd ⊢
      have hA := (advance_structure i s h).1 hd
      rw [hA] at h ⊢
      exact dispatch_structure i s h
    · have hb' : Reactive.runningValue s = false := by simpa using hb
      simp only [hb', Bool.false_eq_true, if_false] at h hd ⊢
      simp [hd]
  rw [entered] at h ⊢
  simp only [Reactive.entryValue, Reactive.enterValue] at h ⊢
  by_cases hv : Execution.validValue i.successor = true
  · by_cases hk : (Execution.unpack i.successor).kind = 4
    · simp [hv, hk, Reactive.stopValue, Reactive.runningValue] at h
    · rw [if_pos hv, if_neg hk]
      exact ⟨rfl, hv⟩
  · simp [hv, Reactive.stopValue, Reactive.runningValue] at h

/-- A valid `checked` record's finish field is a sequential, jump or branch tag. -/
theorem valid_finish (w : BitVec 64) (hv : Execution.validValue w = true)
    (hk : (Execution.unpack w).kind = 2) : (Execution.unpack w).finish ≠ 3 := by
  intro hf
  simp [Execution.validValue, hk, hf] at hv

/-! ### Branching words -/


/-- The two candidates of the current word can differ only here. -/
def branching (core : Reactive.State) (word : BitVec 64) : Bool :=
  let d := Execution.unpack word
  core.mode == 3 && !(d.finish == 0) && !(d.finish == 1)

theorem candidate_nonbranching (core : Reactive.State) (word : BitVec 64)
    (h : branching core word = false) :
    Storage.Prefetch.candidate core word true = Storage.Prefetch.candidate core word false := by
  by_cases m3 : core.mode = 3#3 <;> by_cases f0 : (Execution.unpack word).finish = 0#2 <;>
    by_cases f1 : (Execution.unpack word).finish = 1#2 <;>
    simp_all [branching, Storage.Prefetch.candidate]

/-- A dispatch out of a branching word needs its remaining count at zero. -/
theorem branching_dispatch (i : Reactive.Inputs) (s : Reactive.State)
    (ha : advancing i s = true) (hb : branching s i.current = true) :
    s.remaining = 0 := by
  simp only [branching, Bool.and_eq_true, beq_iff_eq] at hb
  have ha' := ha
  simp [advancing, hb.1.1] at ha'
  exact ha'.2

/-- The canonical candidates depend on the core only through its mode and address. -/
theorem candidate_congr (core core' : Reactive.State) (word : BitVec 64) (b : Bool)
    (hmode : core'.mode = core.mode) (hpc : core'.pc = core.pc) :
    Storage.Prefetch.candidate core' word b = Storage.Prefetch.candidate core word b := by
  have hrun : Reactive.runningValue core' = Reactive.runningValue core := by
    simp [Reactive.runningValue, hmode]
  simp only [Storage.Prefetch.candidate, hrun, hmode, hpc]

/-! ### The decision and the candidates as scheduler expressions

Structural forms over the scheduler's own inputs and registers, for the
netlist: the word being entered is the `successor` input. -/

def kindIs (k : BitVec 3) : Reactive.E 1 := .equal (Reactive.current .kind) (.lit k)

def advancingExpr : Reactive.E 1 :=
  .mux (Reactive.isMode 1) (.zero (.reg .remaining))
    (.mux (Reactive.isMode 2) (.band (kindIs 1) Reactive.ready)
      (.mux (Reactive.isMode 3) (.band (kindIs 2) (.band Reactive.guarded (.zero (.reg .remaining))))
        (.band (kindIs 3) (.band Reactive.guarded (.zero (.reg .remaining))))))

def dispatchingExpr : Reactive.E 1 :=
  .band (.inv (.input .reset)) (.mux Reactive.running advancingExpr (.input .start))

/-- The candidates of the word being entered, at the target. -/
def enteredExpr (b : Bool) : Reactive.E 8 :=
  .mux (Execution.bor (.inv (.equal (Reactive.successor .kind) (.lit 2))) (.zero (Reactive.successor .finish)))
    (.sub Reactive.target (.lit 255))
    (.mux (.equal (Reactive.successor .finish) (.lit 1)) (Reactive.successor .yes)
      (if b then Reactive.successor .yes else Reactive.successor .no))

/-- The candidates of the current word, at the current address. -/
def heldExpr (b : Bool) : Reactive.E 8 :=
  .mux (Execution.bor (.inv (Reactive.isMode 3)) (.zero (Reactive.current .finish)))
    (.sub (.reg .pc) (.lit 255))
    (.mux (.equal (Reactive.current .finish) (.lit 1)) (Reactive.current .yes)
      (if b then Reactive.current .yes else Reactive.current .no))

def candidateExpr (b : Bool) : Reactive.E 8 :=
  .mux dispatchingExpr (enteredExpr b) (heldExpr b)

/-- A word with two distinct candidates, from the mode and the current word. -/
def branchingExpr : Reactive.E 1 :=
  .band (Reactive.isMode 3)
    (.band (.inv (.zero (Reactive.current .finish))) (.inv (.equal (Reactive.current .finish) (.lit 1))))

theorem kindIs_correct (k : BitVec 3) (i : Reactive.Inputs) (s : Reactive.State) :
    (kindIs k).eval i.values s.values = BitVec.ofBool ((Execution.unpack i.current).kind == k) := by
  simp [kindIs, Expr.eval, Reactive.current_correct, Execution.value, Execution.fieldValue,
    Bool.beq_eq_decide_eq]

private theorem one_and (x : BitVec 1) : 1#1 &&& x = x := by
  revert x
  decide

theorem advancing_correct (i : Reactive.Inputs) (s : Reactive.State) :
    advancingExpr.eval i.values s.values = BitVec.ofBool (advancing i s) := by
  simp only [advancingExpr, Expr.eval, Reactive.isMode, Reactive.State.values, kindIs_correct,
    Reactive.ready_correct, Reactive.guard_correct, advancing, BitVec.ofBool_and_ofBool,
    Reactive.bool_one, Bool.and_assoc]
  by_cases m1 : s.mode = 1 <;> by_cases m2 : s.mode = 2 <;> by_cases m3 : s.mode = 3 <;>
    (simp only [m1, m2, m3, decide_true, decide_false, ↓reduceIte, Bool.false_eq_true]; try rfl)

theorem dispatching_correct (i : Reactive.Inputs) (s : Reactive.State) :
    dispatchingExpr.eval i.values s.values = BitVec.ofBool (dispatching i s) := by
  simp only [dispatchingExpr, Expr.eval, Reactive.running_correct, advancing_correct,
    Reactive.Inputs.values, dispatching]
  cases hr : i.reset <;> cases hb : Reactive.runningValue s <;> simp [one_and]

private theorem and_one (x : BitVec 1) : x &&& 1#1 = x := by
  revert x
  decide

set_option linter.unusedSimpArgs false in
theorem enteredExpr_correct (i : Reactive.Inputs) (s : Reactive.State) (b : Bool) :
    (enteredExpr b).eval i.values s.values = entered i s b := by
  simp only [enteredExpr, Expr.eval, Execution.bor, Reactive.successor_correct, Reactive.target_correct,
    Execution.value, Execution.fieldValue, entered]
  by_cases k2 : (Execution.unpack i.successor).kind = 2#3 <;>
    by_cases f0 : (Execution.unpack i.successor).finish = 0#2 <;>
    by_cases f1 : (Execution.unpack i.successor).finish = 1#2 <;> cases b <;>
    simp [k2, f0, f1, one_and, and_one, Reactive.successor_correct, Execution.value, Execution.fieldValue]

set_option linter.unusedSimpArgs false in
theorem heldExpr_correct (i : Reactive.Inputs) (s : Reactive.State) (b : Bool) :
    (heldExpr b).eval i.values s.values = held i s b := by
  simp only [heldExpr, Expr.eval, Execution.bor, Reactive.current_correct, Reactive.isMode,
    Reactive.State.values, Execution.value, Execution.fieldValue, held]
  by_cases m3 : s.mode = 3#3 <;> by_cases f0 : (Execution.unpack i.current).finish = 0#2 <;>
    by_cases f1 : (Execution.unpack i.current).finish = 1#2 <;> cases b <;>
    simp [m3, f0, f1, one_and, and_one, Reactive.current_correct, Execution.value, Execution.fieldValue]

theorem candidateExpr_correct (i : Reactive.Inputs) (s : Reactive.State) (b : Bool) :
    (candidateExpr b).eval i.values s.values = candidate i s b := by
  simp only [candidateExpr, Expr.eval, dispatching_correct, enteredExpr_correct, heldExpr_correct,
    candidate_split]
  cases dispatching i s <;> simp

private theorem branching_bits (m : Bool) (f : BitVec 2) :
    BitVec.ofBool m &&& (~~~BitVec.ofBool (decide (f = 0)) &&& ~~~BitVec.ofBool (decide (f = 1))) =
      BitVec.ofBool (m && !(f == 0) && !(f == 1)) := by
  revert m f
  decide

theorem branchingExpr_correct (i : Reactive.Inputs) (s : Reactive.State) :
    branchingExpr.eval i.values s.values = BitVec.ofBool (branching s i.current) := by
  simp only [branchingExpr, Expr.eval, Reactive.isMode, Reactive.State.values, Reactive.current_correct,
    Execution.value, Execution.fieldValue, branching]
  have hm : decide (s.mode = (3 : BitVec 3)) = (s.mode == (3 : BitVec 3)) :=
    (Bool.beq_eq_decide_eq _ _).symm
  exact (branching_bits (decide (s.mode = 3)) _).trans (by rw [hm])

end Pinwheel.Hardware.Storage.Dispatch
