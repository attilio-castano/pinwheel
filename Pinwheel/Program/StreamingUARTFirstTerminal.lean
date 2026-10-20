import Pinwheel.Program.StreamingUARTFrameStarted

/-! Earliest terminal edges use absorption, not an assumed progress trace.
Under quiet host inputs a nonbusy source cannot become busy. An independently
derived busy predecessor therefore excludes every earlier terminal prefix. -/
namespace Pinwheel.Program.StreamingUART.FirstTerminal
open Pinwheel.Program.StreamingReady
open QuietTiming FrameSamples FramePrelude FrameControl FrameCell FrameData Frame

theorem quiet_nonbusy_phase (p : Program) (s : State a) (i : Input) (quiet : Quiet i)
    (nonbusy : s.phase.busy = false) : (step p i s).phase = s.phase := by
  rw [quiet_clock p s i quiet]
  cases phase : s.phase <;> simp [phase,Phase.busy] at nonbusy
  all_goals simp [clock,engine,phase]

theorem quiet_nonbusy_run_phase (p : Program) (s : State a) (inputs : List Input)
    (quiet : ∀ i ∈ inputs, Quiet i) (nonbusy : s.phase.busy = false) :
    (run p s inputs).phase = s.phase := by
  induction inputs generalizing s with
  | nil => rfl
  | cons i rest induction =>
    have first := quiet_nonbusy_phase p s i (quiet i (by simp)) nonbusy
    change (run p (step p i s) rest).phase = s.phase
    rw [induction (step p i s) (by intro j member; exact quiet j (by simp [member]))
      (by rw [first]; exact nonbusy),first]

theorem busy_before_append (p : Program) (s : State a) (before after : List Input)
    (quiet : ∀ i ∈ after, Quiet i) (busy : (run p s (before ++ after)).phase.busy = true) :
    (run p s before).phase.busy = true := by
  by_cases beforeBusy : (run p s before).phase.busy = true
  · exact beforeBusy
  · have nonbusy : (run p s before).phase.busy = false := Bool.eq_false_iff.mpr beforeBusy
    have same := quiet_nonbusy_run_phase p (run p s before) after quiet nonbusy
    rw [run_append,same,nonbusy] at busy
    contradiction

theorem busy_before (p : Program) (s : State a) (incoming : Nat → Input)
    (quiet : ∀ n, Quiet (incoming n)) (final earlier : Nat) (within : earlier ≤ final)
    (busy : (run p s (clocks incoming 0 final)).phase.busy = true) :
    (run p s (clocks incoming 0 earlier)).phase.busy = true := by
  have split : clocks incoming 0 final =
      clocks incoming 0 earlier ++ clocks incoming earlier (final-earlier) := by
    have sum : earlier + (final-earlier) = final := by omega
    simpa only [sum,Nat.zero_add] using clocks_add incoming 0 earlier (final-earlier)
  rw [split] at busy
  exact busy_before_append p s _ _ (clocks_quiet incoming quiet _ _) busy

theorem good_busy_before (p : Profile) (generation transfer : BitVec 16)
    (payload : BitVec 8) (incoming : Nat → Input) (quiet : ∀ n, Quiet (incoming n))
    (falling : (incoming 0).rawInputs[p.rxInput.val] = false)
    (startLow : (incoming (2*p.Q)).rawInputs[p.rxInput.val] = false)
    (samples : DataSamples p incoming payload)
    (stopHigh : (incoming (38*p.Q)).rawInputs[p.rxInput.val] = true)
    (earlier : Nat) (before : earlier < 38*p.Q+4) :
    (run (image p).program (Arm.armed (a := a) p generation transfer)
      (clocks incoming 0 earlier)).phase.busy = true := by
  apply busy_before (image p).program (Arm.armed p generation transfer) incoming quiet
    (38*p.Q+3) earlier (by omega)
  rw [stop_good p generation transfer payload incoming quiet falling startLow samples stopHigh,
    sampleInputs_phase]
  rfl

theorem stop_check_waiting (p : Profile) (generation transfer : BitVec 16)
    (payload : BitVec 8) (incoming : Nat → Input) (quiet : ∀ n, Quiet (incoming n))
    (falling : (incoming 0).rawInputs[p.rxInput.val] = false)
    (startLow : (incoming (2*p.Q)).rawInputs[p.rxInput.val] = false)
    (samples : DataSamples p incoming payload) :
    (run (image p).program (Arm.armed (a := a) p generation transfer)
      (clocks incoming 0 (38*p.Q+2))).phase = .waiting := by
  have split : 38*p.Q+2 = (38*p.Q+1)+1 := by omega
  rw [split,clocks_add,run_append,tail_run p generation transfer payload incoming quiet falling startLow samples]
  simp only [Nat.zero_add,clocks_one]
  change (step (image p).program (incoming (38*p.Q+1))
    (sampleInputs (afterTail p generation transfer payload) (clocks incoming 0 (38*p.Q+1)))).phase = .waiting
  rw [fetch_wait _ _ _ ⟨0,0⟩ (checkStop p) ((quiet _).runtime _) (quiet _).tx (quiet _).rx
    (by simp [sampleInputs_pair,afterTail,pulseFinish])
    (by rw [sampleInputs_pc]; change (image p).program.fetch 7 = _; rw [source_fetch p 7 (by decide)]; rfl)]

theorem bad_stop_busy_before (p : Profile) (generation transfer : BitVec 16)
    (payload : BitVec 8) (incoming : Nat → Input) (quiet : ∀ n, Quiet (incoming n))
    (falling : (incoming 0).rawInputs[p.rxInput.val] = false)
    (startLow : (incoming (2*p.Q)).rawInputs[p.rxInput.val] = false)
    (samples : DataSamples p incoming payload)
    (earlier : Nat) (before : earlier < 38*p.Q+3) :
    (run (image p).program (Arm.armed (a := a) p generation transfer)
      (clocks incoming 0 earlier)).phase.busy = true := by
  apply busy_before (image p).program (Arm.armed p generation transfer) incoming quiet
    (38*p.Q+2) earlier (by omega)
  rw [stop_check_waiting p generation transfer payload incoming quiet falling startLow samples]
  rfl

theorem start_check_waiting (p : Profile) (generation transfer : BitVec 16)
    (incoming : Nat → Input) (quiet : ∀ n, Quiet (incoming n))
    (falling : (incoming 0).rawInputs[p.rxInput.val] = false) :
    (run (image p).program (Arm.armed (a := a) p generation transfer)
      (clocks incoming 0 (2*p.Q+2))).phase = .waiting := by
  have split : 2*p.Q+2 = (2*p.Q+1)+1 := by omega
  rw [split,clocks_add,run_append,prefixA p generation transfer incoming quiet falling]
  simp only [Nat.zero_add,clocks_one]
  change (step (image p).program (incoming (2*p.Q+1))
    (sampleInputs (afterA p generation transfer) (clocks incoming 0 (2*p.Q+1)))).phase = .waiting
  rw [fetch_wait _ _ _ ⟨0,0⟩ (checkStart p) ((quiet _).runtime _) (quiet _).tx (quiet _).rx
    (by simp [sampleInputs_pair,afterA,pulseFinish])
    (by rw [sampleInputs_pc]; change (image p).program.fetch 3 = _; rw [source_fetch p 3 (by decide)]; rfl)]

theorem false_start_busy_before (p : Profile) (generation transfer : BitVec 16)
    (incoming : Nat → Input) (quiet : ∀ n, Quiet (incoming n))
    (falling : (incoming 0).rawInputs[p.rxInput.val] = false)
    (earlier : Nat) (before : earlier < 2*p.Q+3) :
    (run (image p).program (Arm.armed (a := a) p generation transfer)
      (clocks incoming 0 earlier)).phase.busy = true := by
  apply busy_before (image p).program (Arm.armed p generation transfer) incoming quiet
    (2*p.Q+2) earlier (by omega)
  rw [start_check_waiting p generation transfer incoming quiet falling]
  rfl

/-- Terminal at this edge, with every strictly earlier processed prefix busy.
The first input is the falling-edge raw sample; `edges` counts processed inputs. -/
def FirstAt (program : Program) (initial : State a) (incoming : Nat → Input) (edges : Nat) : Prop :=
  (run program initial (clocks incoming 0 edges)).phase.retained = true ∧
    ∀ earlier, earlier < edges → (run program initial (clocks incoming 0 earlier)).phase.busy = true

theorem good_frame_first (p : Profile) (generation transfer : BitVec 16)
    (payload : BitVec 8) (incoming : Nat → Input) (quiet : ∀ n, Quiet (incoming n))
    (falling : (incoming 0).rawInputs[p.rxInput.val] = false)
    (startLow : (incoming (2*p.Q)).rawInputs[p.rxInput.val] = false)
    (samples : DataSamples p incoming payload)
    (stopHigh : (incoming (38*p.Q)).rawInputs[p.rxInput.val] = true) :
    FirstAt (image p).program (Arm.armed (a := a) p generation transfer) incoming (38*p.Q+4) := by
  refine ⟨?_,good_busy_before p generation transfer payload incoming quiet falling startLow samples stopHigh⟩
  rw [(good_frame_result p generation transfer payload incoming quiet falling startLow samples stopHigh).1]
  rfl

theorem bad_stop_first (p : Profile) (generation transfer : BitVec 16)
    (payload : BitVec 8) (incoming : Nat → Input) (quiet : ∀ n, Quiet (incoming n))
    (falling : (incoming 0).rawInputs[p.rxInput.val] = false)
    (startLow : (incoming (2*p.Q)).rawInputs[p.rxInput.val] = false)
    (samples : DataSamples p incoming payload)
    (stopLow : (incoming (38*p.Q)).rawInputs[p.rxInput.val] = false) :
    FirstAt (image p).program (Arm.armed (a := a) p generation transfer) incoming (38*p.Q+3) := by
  refine ⟨?_,bad_stop_busy_before p generation transfer payload incoming quiet falling startLow samples⟩
  rw [(bad_stop_result p generation transfer payload incoming quiet falling startLow samples stopLow).1]
  rfl

theorem false_start_first (p : Profile) (generation transfer : BitVec 16)
    (incoming : Nat → Input) (quiet : ∀ n, Quiet (incoming n))
    (falling : (incoming 0).rawInputs[p.rxInput.val] = false)
    (startHigh : (incoming (2*p.Q)).rawInputs[p.rxInput.val] = true) :
    FirstAt (image p).program (Arm.armed (a := a) p generation transfer) incoming (2*p.Q+3) := by
  refine ⟨?_,false_start_busy_before p generation transfer incoming quiet falling⟩
  rw [(false_start_result p generation transfer incoming quiet falling startHigh).1]
  rfl

theorem stable_frame_first (p : Profile) (generation transfer : BitVec 16)
    (payload : BitVec 8) (incoming : Nat → Input) (quiet : ∀ n, Quiet (incoming n))
    (frame : StableFrame p incoming payload) :
    FirstAt (image p).program (Arm.armed (a := a) p generation transfer) incoming (38*p.Q+4) := by
  have positive := p.Q_ge4
  exact good_frame_first p generation transfer payload incoming quiet
    (frame.start 0 (by omega)) (frame.start (2*p.Q) (by omega)) (frame.samples p incoming payload)
    (frame.stop (38*p.Q) (by omega) (by omega))

theorem admitted_good_frame_first (p : Profile) (s : State a) (start : Input) (marks : List Input)
    (payload : BitVec 8) (incoming : Nat → Input)
    (runtime : start.Runtime) (admitted : (start.command == 3 && s.canStart start) = true)
    (count : start.startCount = 8)
    (markQuiet : ∀ i ∈ marks, Quiet i) (markRaw : ∀ i ∈ marks, i.rawInputs = 3) (long : 6 ≤ marks.length)
    (quiet : ∀ n, Quiet (incoming n))
    (falling : (incoming 0).rawInputs[p.rxInput.val] = false)
    (startLow : (incoming (2*p.Q)).rawInputs[p.rxInput.val] = false)
    (samples : DataSamples p incoming payload)
    (stopHigh : (incoming (38*p.Q)).rawInputs[p.rxInput.val] = true) :
    FirstAt (image p).program (run (image p).program s (start :: marks)) incoming (38*p.Q+4) := by
  change FirstAt (image p).program (run (image p).program (step (image p).program start s) marks) incoming _
  rw [Arm.admitted_marks p s start marks runtime admitted count markQuiet markRaw long]
  exact good_frame_first p s.generation (s.transfer+1) payload incoming quiet falling startLow samples stopHigh

theorem admitted_bad_stop_first (p : Profile) (s : State a) (start : Input) (marks : List Input)
    (payload : BitVec 8) (incoming : Nat → Input)
    (runtime : start.Runtime) (admitted : (start.command == 3 && s.canStart start) = true)
    (count : start.startCount = 8)
    (markQuiet : ∀ i ∈ marks, Quiet i) (markRaw : ∀ i ∈ marks, i.rawInputs = 3) (long : 6 ≤ marks.length)
    (quiet : ∀ n, Quiet (incoming n))
    (falling : (incoming 0).rawInputs[p.rxInput.val] = false)
    (startLow : (incoming (2*p.Q)).rawInputs[p.rxInput.val] = false)
    (samples : DataSamples p incoming payload)
    (stopLow : (incoming (38*p.Q)).rawInputs[p.rxInput.val] = false) :
    FirstAt (image p).program (run (image p).program s (start :: marks)) incoming (38*p.Q+3) := by
  change FirstAt (image p).program (run (image p).program (step (image p).program start s) marks) incoming _
  rw [Arm.admitted_marks p s start marks runtime admitted count markQuiet markRaw long]
  exact bad_stop_first p s.generation (s.transfer+1) payload incoming quiet falling startLow samples stopLow

theorem admitted_false_start_first (p : Profile) (s : State a) (start : Input) (marks : List Input)
    (incoming : Nat → Input)
    (runtime : start.Runtime) (admitted : (start.command == 3 && s.canStart start) = true)
    (count : start.startCount = 8)
    (markQuiet : ∀ i ∈ marks, Quiet i) (markRaw : ∀ i ∈ marks, i.rawInputs = 3) (long : 6 ≤ marks.length)
    (quiet : ∀ n, Quiet (incoming n))
    (falling : (incoming 0).rawInputs[p.rxInput.val] = false)
    (startHigh : (incoming (2*p.Q)).rawInputs[p.rxInput.val] = true) :
    FirstAt (image p).program (run (image p).program s (start :: marks)) incoming (2*p.Q+3) := by
  change FirstAt (image p).program (run (image p).program (step (image p).program start s) marks) incoming _
  rw [Arm.admitted_marks p s start marks runtime admitted count markQuiet markRaw long]
  exact false_start_first p s.generation (s.transfer+1) incoming quiet falling startHigh

end Pinwheel.Program.StreamingUART.FirstTerminal
