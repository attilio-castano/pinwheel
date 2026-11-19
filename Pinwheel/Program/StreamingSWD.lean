import Pinwheel.Program.StreamingReadyCompile
import Pinwheel.Program.StreamingUARTQuiet

/-! The fixed DPIDR read uses pulses around one receive-only stream. The
concrete four-cycle image is checked against the clock and pad-drive trace
for a quiet host and arbitrary raw samples. -/
namespace Pinwheel.Program.StreamingSWD
open StreamingReady
open StreamingUART.QuietTiming

set_option maxRecDepth 10000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

/-- Chronological request bits for a DP read of address zero. -/
def requestBits : List Bool := [true,false,true,false,false,true,false,true]

/-- SWCLK is output zero. SWDIO drives output one and is sensed at raw input one. -/
def pads (clock : Bool) (data : Option Bool) : Pins :=
  ⟨(if clock then 1 else 0) + (if data.getD false then 2 else 0), if data.isSome then 3 else 1⟩

def idlePins : Pins := pads false none

def pulse (d : Fin 256) (data : Option Bool) : Instruction :=
  .pulse {lowDuration := d, highDuration := d, lowPins := pads false data, highPins := pads true data}

def receive (d : Fin 256) : Instruction :=
  .stream {
    lowDuration := d, highDuration := d, lowPins := pads false none,
    highPins := pads true none, receive := true, rxInput := 1} none

def source (d : Fin 256) : List Instruction :=
  (requestBits.map (fun bit => pulse d (some bit))) ++
  [pulse d none,receive d,pulse d none] ++ List.replicate 8 (pulse d (some false)) ++ [.halt]

theorem supported (d : Fin 256) : Supported (source d) := by
  simp [Supported,source,requestBits,pulse,receive,supportedFrom,List.replicate_succ,
    List.countP_cons,Instruction.isStream,Instruction.Canonical,Streaming.Cell.PulseCanonical]

def image (d : Fin 256) : Compiled (source d) idlePins :=
  ⟨(source d).map encode,supported d,rfl⟩

abbrev program : Program := (image 3).program

def clockCount : Nat := 506

structure Pose where
  pins : Pins
  capture : Bool
  rxPort : Nat
  phase : Phase
  deriving DecidableEq, Repr

def pose (s : State a) : Pose := ⟨s.pins,s.captures,s.current.cell.rxInput.val,s.phase⟩

/-- Snapshots include both the initial cut and the final cut. Capture is a
    property of the pre-edge snapshot. -/
def poses (s : State a) : List Input → List Pose
  | [] => [pose s]
  | i :: rest => pose s :: poses (step program i s) rest

def referenceStart : State 1 := ({} : State 1).start program {startCount := 36}

def reference : List Pose := poses referenceStart (List.replicate clockCount {})

private def eraseQueue (q : Queue a) : Queue a :=
  {q with memory := Vector.replicate (Streaming.queueDepth a) {}}

/-- Remove sampled data and ownership IDs. Queue control, including the
    receive count, remains in this projection of the actual engine. -/
private def erase (s : State a) : State a :=
  {s with
    rx := eraseQueue s.rx, rxPartial := 0, samplerFirst := 0,
    samplerSecond := 0, generation := 0, transfer := 0}

private theorem captures_erase (s : State a) (ordinary : s.phase ≠ .waiting) :
    (erase s).captures = s.captures := by
  have waiting : (s.phase == .waiting) = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    exact ordinary (beq_iff_eq.mp h)
  simp [State.captures,erase,waiting]

private theorem pose_erase (s : State a) (ordinary : s.phase ≠ .waiting) :
    pose (erase s) = pose s := by
  unfold pose
  rw [captures_erase s ordinary]
  rfl

private theorem engine_erase (p : Program) (s : State a) (ordinary : s.phase ≠ .waiting) :
    erase (engine p s) = erase (engine p (erase s)) := by
  cases phase : s.phase
  case fetch =>
    have f : (erase s).pc = s.pc := rfl
    have phaseE : (erase s).phase = .fetch := phase
    simp only [engine,phase,phaseE,f]
    cases row : p.fetch s.pc.toNat with
    | none => rfl
    | some instruction =>
      cases instruction <;> try rfl
      by_cases empty : s.remaining = 0#16 <;> simp [erase,eraseQueue,empty]
  case boundary =>
    have ephase : (erase s).phase = .boundary := phase
    have credit : (erase s).canReserve = s.canReserve := rfl
    cases room : s.canReserve <;> simp only [engine,phase,ephase,credit,room,if_true,
      if_false,Bool.false_eq_true]
    all_goals rfl
  case low =>
    have ephase : (erase s).phase = .low := phase
    have left : (erase s).countdown = s.countdown := rfl
    have guard : (erase s).current.hasHighGuard = s.current.hasHighGuard := rfl
    have emit : (erase s).emittingCapture = s.emittingCapture := by
      simp only [State.emittingCapture,captures_erase s ordinary]
      rfl
    simp only [engine,phase,ephase,left,guard]
    by_cases zero : s.countdown = 0#8
    · cases guarded : s.current.hasHighGuard <;>
        simp only [zero,beq_self_eq_true,guarded,if_true,if_false,Bool.false_eq_true]
      · simp only [State.enterHigh,State.captureData,captures_erase s ordinary,emit]
        rfl
      · rfl
    · simp only [beq_iff_eq,if_neg (show s.countdown ≠ (0 : BitVec 8) from zero)]
      rfl
  case high =>
    have ephase : (erase s).phase = .high := phase
    have left : (erase s).countdown = s.countdown := rfl
    simp only [engine,phase,ephase,left]
    split <;> rfl
  case waiting => contradiction
  case free =>
    have ephase : (erase s).phase = .free := phase
    simp only [engine,phase,ephase]
    rfl
  case completed =>
    have ephase : (erase s).phase = .completed := phase
    simp only [engine,phase,ephase]
    rfl
  case fault =>
    have ephase : (erase s).phase = .fault := phase
    simp only [engine,phase,ephase]
    rfl

private theorem push_shape (s : State a) (ordinary : s.phase ≠ .waiting) :
    s.enginePush.isSome = (erase s).enginePush.isSome := by
  have waiting : (s.phase == .waiting) = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    exact ordinary (beq_iff_eq.mp h)
  have one : s.timedOut = false := by simp [State.timedOut,waiting]
  have two : (erase s).timedOut = false := by
    have phase : ((erase s).phase == .waiting) = false := waiting
    simp [State.timedOut,phase]
  have emit : (erase s).emittingCapture = s.emittingCapture := by
    simp only [State.emittingCapture,captures_erase s ordinary]
    rfl
  cases capture : s.emittingCapture <;> simp [State.enginePush,one,two,emit,capture]

private theorem erase_tick (q : Queue a) (x y : Option Chunk) (same : x.isSome = y.isSome) :
    eraseQueue (q.tick x false) = eraseQueue ((eraseQueue q).tick y false) := by
  cases x <;> cases y <;> first | rfl | contradiction

private theorem step_erase (p : Program) (s : State a) (i : Input)
    (quiet : Quiet i) (ordinary : s.phase ≠ .waiting) :
    erase (step p i s) = erase (step p {} (erase s)) := by
  have zero : Quiet ({} : Input) := ⟨rfl,rfl,rfl,rfl⟩
  rw [quiet_clock p s i quiet,quiet_clock p (erase s) {} zero]
  have tx : (erase s).enginePop = s.enginePop := rfl
  have receive := erase_tick s.rx s.enginePush (erase s).enginePush (push_shape s ordinary)
  have noPush (q : State a) : q.hostPush i = none := by simp [State.hostPush,quiet.tx]
  have noPop (q : State a) : q.hostPop i = false := by simp [State.hostPop,quiet.rx]
  have noPush0 (q : State a) : q.hostPush {} = none := by simp [State.hostPush]
  have noPop0 (q : State a) : q.hostPop {} = false := by simp [State.hostPop]
  simp only [clock,noPush,noPop,noPush0,noPop0,Streaming.Queue.willPush,Streaming.Queue.willPop,
    Option.isSome_none,Bool.false_and,Bool.false_eq_true,if_false,BitVec.add_zero,tx]
  change {erase (engine p s) with
      tx := s.tx.tick none s.enginePop
      rx := eraseQueue (s.rx.tick s.enginePush false)
      txAccepted := s.txAccepted + 0
      rxPopped := s.rxPopped + 0} =
    {erase (engine p (erase s)) with
      tx := s.tx.tick none s.enginePop
      rx := eraseQueue ((eraseQueue s.rx).tick (erase s).enginePush false)
      txAccepted := s.txAccepted + 0
      rxPopped := s.rxPopped + 0}
  rw [engine_erase p s ordinary,receive]

private theorem poses_equal (s t : State a) (inputs : List Input) (same : erase s = erase t)
    (quiet : ∀ i ∈ inputs, Quiet i)
    (never : ∀ observation ∈ poses t (List.replicate inputs.length {}), observation.phase ≠ .waiting) :
    poses s inputs = poses t (List.replicate inputs.length {}) := by
  induction inputs generalizing s t with
  | nil =>
    have tReady : t.phase ≠ .waiting := never (pose t) (by simp [poses])
    have sReady : s.phase ≠ .waiting := congrArg State.phase same ▸ tReady
    have first := (pose_erase s sReady).symm.trans ((congrArg pose same).trans (pose_erase t tReady))
    exact congrArg (fun p => [p]) first
  | cons i rest tail =>
    have tReady : t.phase ≠ .waiting := never (pose t) (by simp [poses,List.replicate_succ])
    have sReady : s.phase ≠ .waiting := congrArg State.phase same ▸ tReady
    have first := (pose_erase s sReady).symm.trans ((congrArg pose same).trans (pose_erase t tReady))
    have zero : Quiet ({} : Input) := ⟨rfl,rfl,rfl,rfl⟩
    have next := (step_erase program s i (quiet i List.mem_cons_self) sReady).trans
      ((congrArg (fun q => erase (step program {} q)) same).trans
        (step_erase program t {} zero tReady).symm)
    have tailQuiet : ∀ j ∈ rest, Quiet j := fun j member => quiet j (List.mem_cons_of_mem i member)
    have tailReady : ∀ obs ∈ poses (step program {} t) (List.replicate rest.length {}), obs.phase ≠ .waiting :=
      fun obs member => never obs (List.mem_cons_of_mem (pose t) member)
    change pose s :: poses (step program i s) rest =
      pose t :: poses (step program {} t) (List.replicate rest.length {})
    rw [first,tail _ _ next tailQuiet tailReady]

private theorem reference_no_wait : (reference.map Pose.phase).contains .waiting = false := by
  decide +kernel

/-- Raw pin values cannot change the 506-clock schedule or consume receive
    credit at a different cut, even when every raw sample differs. -/
theorem quiet_poses (before : State 1) (start : Input) (inputs : List Input)
    (count : start.startCount = 36#16) (ordinary : ∀ i ∈ inputs, Quiet i)
    (length : inputs.length = clockCount) :
    poses (before.start program start) inputs = reference := by
  have same : erase (before.start program start) = erase referenceStart := by
    simp [erase,State.start,referenceStart,count]
  unfold reference
  rw [← length]
  apply poses_equal _ _ _ same ordinary
  intro obs member
  intro blocked
  have waitIn : Phase.waiting ∈ reference.map Pose.phase := by
    rw [← blocked]
    apply List.mem_map_of_mem
    simpa only [reference,← length] using member
  have forbidden := List.contains_iff_mem.mpr waitIn
  rw [reference_no_wait] at forbidden
  contradiction

theorem poses_pins (s : State a) (inputs : List Input) :
    (poses s inputs).map Pose.pins = pinTrace program s inputs := by
  induction inputs generalizing s with
  | nil => rfl
  | cons i rest ih => simp [poses,pose,pinTrace,ih]

theorem poses_last (s : State a) (inputs : List Input) :
    (poses s inputs).getLast? = some (pose (run program s inputs)) := by
  induction inputs generalizing s with
  | nil => rfl
  | cons i rest ih =>
    cases rest with
    | nil => rfl
    | cons j tail =>
      change (poses (step program i s) (j :: tail)).getLast? = _
      exact ih _

theorem refCompleted : reference.getLast?.map Pose.phase = some .completed := by
  decide +kernel

/-- Report each rising SWCLK edge and its controller drive (if any) on SWDIO. -/
def rises : List Pins → List (Option Bool)
  | before :: after :: rest =>
    (if !before.levels[0] && after.levels[0] then
      [if after.enabled[1] then some after.levels[1] else none] else []) ++ rises (after :: rest)
  | _ => []

theorem reference_rises : rises (reference.map Pose.pins) =
    requestBits.map some ++ List.replicate 38 none ++ List.replicate 8 (some false) := by
  decide +kernel

theorem quiet_completed (before : State 1) (start : Input) (inputs : List Input)
    (count : start.startCount = 36#16) (ordinary : ∀ i ∈ inputs, Quiet i)
    (length : inputs.length = clockCount) :
    (run program (before.start program start) inputs).phase = .completed := by
  have observation := refCompleted
  rw [← quiet_poses before start inputs count ordinary length,poses_last] at observation
  exact Option.some.inj observation

end Pinwheel.Program.StreamingSWD
