import Pinwheel.Hardware.Loader.Upload
import Pinwheel.Hardware.Reactive.Refinement

/-! From a loaded image to a running program.

`Holds p m`: the bank `m` reads as the program `p` at every address, with `p`'s
idle pins and last address. While the selected bank holds `p`, the machine's
scheduler is fed exactly as by the fixed program `p` (`scheduler_holds`), so
each machine edge is one edge of the instruction-level engine on `p`
(`core_next_holds`, through `Reactive.step_refines`), and so is every history
without an `init` or a commit (`runs_program`): uploads to the other bank,
aborts, rejected commands and starts included. -/
namespace Pinwheel.Hardware.Loader.Machine

/-- The bank reads as the program. -/
structure Holds (p : Reactive.Program) (m : Store.Image) : Prop where
  read : ∀ a : BitVec 8, Store.read m a = Execution.encode (p.fetch a.toFin)
  idle : (⟨(m .idle).extractLsb' 0 3, (m .idle).extractLsb' 3 3⟩ : Engine.Reactive.Pins) = p.idle
  last : m .last = BitVec.ofFin p.last

/-- With the selected bank holding `p`, the scheduler is fed as by the fixed program. -/
theorem scheduler_holds (p : Reactive.Program) (i : Inputs) (s : State)
    (h : Holds p (s.memory (selected i s))) (hu : usable i s = true) :
    schedulerInput i s =
      Reactive.feed p s.core (baseInput i s).reset (baseInput i s).start i.incoming := by
  simp only [schedulerInput, baseInput, Reactive.feed, Reactive.Fetch.resolve,
    Reactive.Fetch.Request.address, hu, if_true, h.read, h.idle, h.last]

/-- One machine edge is one engine edge of the held program. -/
theorem core_next_holds (p : Reactive.Program) (i : Inputs) (s : State) (m : Reactive.Model)
    (h : Holds p (s.memory (selected i s))) (hu : usable i s = true) (hm : s.core = Reactive.embed m) :
    (next i s).core =
      Reactive.embed (Engine.Reactive.step p m (baseInput i s).reset (baseInput i s).start i.incoming) := by
  show Reactive.stepValue (schedulerInput i s) s.core = _
  rw [scheduler_holds p i s h hu, hm, Reactive.step_refines]

/-- What an input asks of the engine, given a committed image: `reset` stops it,
and command 5 starts it when it is stopped. -/
def engineStep (p : Reactive.Program) (i : Inputs) (m : Reactive.Model) : Reactive.Model :=
  Engine.Reactive.step p m i.reset (!i.reset && !Engine.Reactive.busy m && i.command == 5) i.incoming

def engineRun (p : Reactive.Program) (m : Reactive.Model) : List Inputs → Reactive.Model
  | [] => m
  | i :: rest => engineRun p (engineStep p i m) rest

/-- A machine with a committed image that holds `p`, its engine at the model state `m`. -/
structure Running (p : Reactive.Program) (m : Reactive.Model) (s : State) : Prop where
  valid : s.control.valid = true
  holds : Holds p (s.memory s.control.active)
  core : s.core = Reactive.embed m

/-- An edge with no `init` and no commit is one engine edge of the held program. -/
theorem running_next (p : Reactive.Program) (m : Reactive.Model) (i : Inputs) (s : State)
    (h : Running p m s) (hi : i.init = false) (h3 : (i.command == 3) = false) :
    Running p (engineStep p i m) (next i s) := by
  have hcommit : committing i s = false := by
    show (Loader.enabled (controlInput i s) && (i.command == 3) && s.control.pending &&
      (s.control.cursor == 322)) = false
    rw [h3]
    simp
  have hselected : selected i s = s.control.active := by simp [selected, hcommit]
  have husable : usable i s = true := by simp [usable, hi, h.valid]
  have hkeep : ∀ {w : Nat} (r : Store.Register w), (next i s).control.valid = s.control.valid ∧
      (next i s).memory (next i s).control.active r = s.memory s.control.active r :=
    fun r => interrupted_upload_preserves_program i s hi hcommit r
  refine ⟨(hkeep (Store.Register.idle)).1 ▸ h.valid, ?_, ?_⟩
  · refine ⟨fun a => ?_, ?_, ?_⟩
    · have hr := h.holds.read a
      simp only [Store.read] at hr ⊢
      rw [(hkeep (.index a)).2, (hkeep (.word _)).2]
      exact hr
    · rw [(hkeep .idle).2]
      exact h.holds.idle
    · rw [(hkeep .last).2]
      exact h.holds.last
  · rw [core_next_holds p i s m (hselected ▸ h.holds) husable h.core]
    have hreset : (baseInput i s).reset = i.reset := by
      simp [baseInput, hi, h.valid, hcommit]
    have hstart : (baseInput i s).start = (!i.reset && !Engine.Reactive.busy m && i.command == 5) := by
      show (Loader.enabled (controlInput i s) && (i.command == 5) && s.control.valid) = _
      rw [h.valid, Bool.and_true]
      show ((!i.init && !i.reset && !Reactive.runningValue s.core) && (i.command == 5)) = _
      rw [hi, h.core, Reactive.running_embed]
      rfl
    rw [hreset, hstart]
    rfl

/-- **The held program is the one that runs**: over any history without an `init`
or a commit, the machine's engine registers are the instruction-level engine's
state on `p`, edge for edge. -/
theorem runs_program (p : Reactive.Program) (inputs : List Inputs) (m : Reactive.Model) (s : State)
    (h : Running p m s) (hno : ∀ i ∈ inputs, i.init = false ∧ (i.command == 3) = false) :
    Running p (engineRun p m inputs) (run s inputs) := by
  induction inputs generalizing m s with
  | nil => exact h
  | cons i rest ih =>
    obtain ⟨hi, h3⟩ := hno i (List.mem_cons_self ..)
    exact ih _ _ (running_next p m i s h hi h3) (fun j hj => hno j (List.mem_cons_of_mem i hj))

/-! The same behind an admission check on pushes: a refused push becomes a
rejection, which the engine never sees. -/

theorem admitted_is (A : BitVec 9 → BitVec 64 → Bool) (i : Inputs) (s : State) (c : BitVec 3)
    (h2 : ((2 : BitVec 3) == c) = false) (h6 : ((6 : BitVec 3) == c) = false) :
    ((admitted A i s).command == c) = (i.command == c) := by
  cases hp : (i.command == 2)
  · rw [admitted_of_command A i s hp]
  · have hcmd : i.command = 2 := by simpa using hp
    cases hA : A s.control.cursor i.data
    · have hrej : (admitted A i s).command = 6 := by
        show (if (i.command == 2 && !A s.control.cursor i.data) = true then (6 : BitVec 3)
          else i.command) = 6
        rw [hp, hA]
        rfl
      rw [hrej, h6, hcmd, h2]
    · rw [admitted_of_accept A i s hA]

theorem engineStep_admitted (A : BitVec 9 → BitVec 64 → Bool) (p : Reactive.Program) (i : Inputs)
    (s : State) (m : Reactive.Model) : engineStep p (admitted A i s) m = engineStep p i m := by
  unfold engineStep
  rw [admitted_is A i s 5 (by decide) (by decide)]
  rfl

/-- The held program runs behind any admission check, edge for edge. -/
theorem runs_program_with (A : BitVec 9 → BitVec 64 → Bool) (p : Reactive.Program)
    (inputs : List Inputs) (m : Reactive.Model) (s : State) (h : Running p m s)
    (hno : ∀ i ∈ inputs, i.init = false ∧ (i.command == 3) = false) :
    Running p (engineRun p m inputs) (runWith A s inputs) := by
  induction inputs generalizing m s with
  | nil => exact h
  | cons i rest ih =>
    obtain ⟨hi, h3⟩ := hno i (List.mem_cons_self ..)
    have hstep : Running p (engineStep p i m) (stepWith A i s) := by
      rw [← engineStep_admitted A p i s m]
      exact running_next p m (admitted A i s) s h hi
        (by rw [admitted_is A i s 3 (by decide) (by decide)]; exact h3)
    exact ih _ _ hstep (fun j hj => hno j (List.mem_cons_of_mem i hj))

/-- A loaded image that holds `p` leaves the engine reset on `p`, ready to start. -/
theorem Loaded.running {ws : List (BitVec 64)} {bank : Bool} {old : Store.Image} {s : State}
    (h : Loaded ws bank old s) (p : Reactive.Program) (hp : Holds p (imageOf ws)) :
    Running p (Engine.Reactive.reset p) s := by
  refine ⟨by rw [h.control], ?_, ?_⟩
  · have hactive : s.control.active = !bank := by rw [h.control]
    rw [hactive]
    refine ⟨fun a => ?_, ?_, ?_⟩
    · have hr := hp.read a
      simp only [Store.read] at hr ⊢
      rw [h.image, h.image]
      exact hr
    · rw [h.image]
      exact hp.idle
    · rw [h.image]
      exact hp.last
  · rw [h.core, hp.idle]
    rfl

end Pinwheel.Hardware.Loader.Machine
