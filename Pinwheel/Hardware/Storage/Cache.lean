import Pinwheel.Hardware.Loader.Contract

namespace Pinwheel.Hardware.Storage.Cache
open Loader

structure State where
  machine : Machine.State
  current : BitVec 64

def Valid (s : State) : Prop :=
  Reactive.Fetch.CurrentValid s.machine.core s.current
    (Loader.Store.read (s.machine.memory s.machine.control.active))

def base (i : Machine.Inputs) (s : State) : Reactive.Inputs :=
  {Machine.baseInput i s.machine with current := s.current}

def feed (i : Machine.Inputs) (s : State) : Reactive.Inputs :=
  Reactive.Fetch.resolve (base i s) s.machine.core
    (Loader.Store.read (s.machine.memory (Machine.selected i s.machine)))

def next (i : Machine.Inputs) (s : State) : State :=
  let core := Reactive.stepValue (feed i s) s.machine.core
  {machine := {Machine.next i s.machine with core := core}
   current := if !Reactive.runningValue s.machine.core || core.pc != s.machine.core.pc
     then (feed i s).successor else s.current}

theorem idle_target (i : Reactive.Inputs) (s : Reactive.State)
    (h : Reactive.runningValue s = false) (word : BitVec 64) :
    Reactive.targetValue {i with current := word} s = Reactive.targetValue i s := by
  simp [Reactive.targetValue, h]
  done

theorem idle_step (i : Reactive.Inputs) (s : Reactive.State)
    (h : Reactive.runningValue s = false) (word : BitVec 64) :
    Reactive.stepValue {i with current := word} s = Reactive.stepValue i s := by
  simp [Reactive.stepValue, Reactive.entryValue, Reactive.targetValue, Reactive.entryValues,
    Reactive.stopValue, Reactive.enterValue, h]
  done

theorem busy_selection (i : Machine.Inputs) (s : Machine.State)
    (h : Reactive.runningValue s.core = true) : Machine.selected i s = s.control.active := by
  simp [Machine.selected, Machine.committing, Loader.commit, Loader.enabled, Machine.controlInput, h]
  done

theorem feed_correct (i : Machine.Inputs) (s : State) (h : Valid s) :
    feed i s = {Machine.schedulerInput i s.machine with current := s.current} := by
  by_cases hb : Reactive.runningValue s.machine.core = true
  · have hw := h hb
    simp [feed, base, Machine.schedulerInput, Machine.baseInput, busy_selection i s.machine hb, hw]
  · simp [feed, base, Machine.schedulerInput, idle_target _ _ (by simpa using hb)]
  done

theorem machine_next (i : Machine.Inputs) (s : State) (h : Valid s) :
    (next i s).machine = Machine.next i s.machine := by
  have hf := feed_correct i s h
  simp only [next, hf]
  congr 1
  by_cases hb : Reactive.runningValue s.machine.core = true
  · have hw := h hb
    simp [Machine.schedulerInput, Machine.baseInput,
      busy_selection i s.machine hb, hw]
  · exact idle_step _ _ (by simpa using hb) _
  done

theorem enter_pc (i : Reactive.Inputs) (word : BitVec 64) (pc : BitVec 8) (slots : Reactive.Samples)
    (h : Reactive.runningValue (Reactive.enterValue word pc slots i) = true) :
    (Reactive.enterValue word pc slots i).pc = pc := by
  simp only [Reactive.enterValue] at h ⊢
  split <;> simp_all [Reactive.stopValue, Reactive.runningValue]
  split <;> simp_all
  done

set_option maxHeartbeats 2000000 in
theorem step_pc (i : Reactive.Inputs) (s : Reactive.State)
    (h : Reactive.runningValue (Reactive.stepValue i s) = true) :
    (Reactive.stepValue i s).pc = Reactive.targetValue i s ∨
      (Reactive.runningValue s = true ∧ (Reactive.stepValue i s).pc = s.pc) := by
  simp only [Reactive.stepValue, Reactive.advanceValue, Reactive.dispatchValue,
    Reactive.entryValue, Reactive.decrementValue, Reactive.progressValue, Reactive.retryValue] at h ⊢
  repeat' first | (solve | simp_all [Reactive.stopValue, Reactive.runningValue]) |
    (solve | exact Or.inl (enter_pc _ _ _ _ h)) | (split <;> simp_all only [if_true, if_false])
  done

theorem running_reset (i : Reactive.Inputs) (s : Reactive.State)
    (h : Reactive.runningValue (Reactive.stepValue i s) = true) : i.reset = false := by
  cases hr : i.reset <;> simp_all [Reactive.stepValue, Reactive.stopValue, Reactive.runningValue]
  done

theorem running_selection (i : Machine.Inputs) (s : Machine.State)
    (h : Reactive.runningValue (Machine.next i s).core = true) :
    (Machine.next i s).control.active = s.control.active ∧ Machine.selected i s = s.control.active := by
  have hr := running_reset (Machine.schedulerInput i s) s.core h
  simp only [Machine.schedulerInput, Machine.baseInput, Bool.or_eq_false_iff,
    Bool.not_eq_false'] at hr
  exact ⟨(Loader.no_commit_preserves_selection (Machine.controlInput i s) s.control hr.1.1.1 hr.2).1,
    by simp [Machine.selected, hr.2]⟩
  done

end Pinwheel.Hardware.Storage.Cache
