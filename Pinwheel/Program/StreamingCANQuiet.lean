import Pinwheel.Program.StreamingUARTQuiet
import Pinwheel.Program.StreamingReadyBitTrace

/-! Once a receive program leaves its sampled start guard, timing depends on
queue occupancy and instruction state. The quiet schedule erases samples and
receive words while retaining these control fields. -/
namespace Pinwheel.Program.StreamingCANQuiet
open StreamingReady StreamingUART.QuietTiming

set_option linter.unusedSimpArgs false

structure Pose where
  pins : Pins
  capture : Bool
  rxPort : Nat
  phase : Phase
  deriving DecidableEq, Repr

def pose (s : State a) : Pose := ⟨s.pins,s.captures,s.current.cell.rxInput.val,s.phase⟩

/-- Snapshots include both the initial cut and the final cut. Capture is a
    property of the pre-edge snapshot. -/
def poses (p : Program) (s : State a) : List Input → List Pose
  | [] => [pose s]
  | i :: rest => pose s :: poses p (step p i s) rest

private def eraseQueue (q : Queue a) : Queue a :=
  {q with memory := Vector.replicate (Streaming.queueDepth a) {}}

/-- Remove sampled data and ownership IDs. Queue control, including the
    receive count, remains in this projection of the actual engine. -/
def erase (s : State a) : State a :=
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

theorem poses_equal (p : Program) (s t : State a) (inputs : List Input) (same : erase s = erase t)
    (quiet : ∀ i ∈ inputs, Quiet i)
    (never : ∀ observation ∈ poses p t (List.replicate inputs.length {}), observation.phase ≠ .waiting) :
    poses p s inputs = poses p t (List.replicate inputs.length {}) := by
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
    have next := (step_erase p s i (quiet i List.mem_cons_self) sReady).trans
      ((congrArg (fun q => erase (step p {} q)) same).trans
        (step_erase p t {} zero tReady).symm)
    have tailQuiet : ∀ j ∈ rest, Quiet j := fun j member => quiet j (List.mem_cons_of_mem i member)
    have tailReady : ∀ obs ∈ poses p (step p {} t) (List.replicate rest.length {}), obs.phase ≠ .waiting :=
      fun obs member => never obs (List.mem_cons_of_mem (pose t) member)
    change pose s :: poses p (step p i s) rest =
      pose t :: poses p (step p {} t) (List.replicate rest.length {})
    rw [first,tail _ _ next tailQuiet tailReady]

theorem poses_pins (p : Program) (s : State a) (inputs : List Input) :
    (poses p s inputs).map Pose.pins = pinTrace p s inputs := by
  induction inputs generalizing s with
  | nil => rfl
  | cons i rest ih => simp [poses,pose,pinTrace,ih]

theorem poses_last (p : Program) (s : State a) (inputs : List Input) :
    (poses p s inputs).getLast? = some (pose (run p s inputs)) := by
  induction inputs generalizing s with
  | nil => rfl
  | cons i rest ih =>
    cases rest with
    | nil => rfl
    | cons j tail =>
      change (poses p (step p i s) (j :: tail)).getLast? = _
      exact ih _

/-- Each cut names the pre-edge index and the port read by the capture. -/
def cutsFrom (k : Nat) : List Pose → List (Nat × Nat)
  | before :: after :: rest =>
    (if before.capture then [(k, before.rxPort)] else []) ++ cutsFrom (k + 1) (after :: rest)
  | _ => []

theorem cuts_cons (p : Program) (k : Nat) (s : State a) (i : Input) (rest : List Input) :
    cutsFrom k (poses p s (i :: rest)) =
      (if s.captures then [(k, s.current.cell.rxInput.val)] else []) ++
        cutsFrom (k + 1) (poses p (step p i s) rest) := by
  cases rest <;> rfl

theorem cuts_append (p : Program) (k : Nat) (s : State a) (first rest : List Input) :
    cutsFrom k (poses p s (first ++ rest)) = cutsFrom k (poses p s first) ++
      cutsFrom (k + first.length) (poses p (run p s first) rest) := by
  induction first generalizing k s with
  | nil => rfl
  | cons i tail ih =>
    rw [List.cons_append, cuts_cons, cuts_cons, ih, List.length_cons, List.append_assoc]
    rw [show k + 1 + tail.length = k + (tail.length + 1) by omega]
    rfl

theorem cuts_shift (snapshots : List Pose) (k n : Nat) :
    cutsFrom (n + k) snapshots = (cutsFrom k snapshots).map (fun cut => (n + cut.1, cut.2)) := by
  induction snapshots generalizing k with
  | nil => rfl
  | cons before rest ih =>
    cases rest with
    | nil => rfl
    | cons after tail =>
      simp only [cutsFrom, List.map_append, Nat.add_assoc, ih]
      cases before.capture <;> rfl

def apertureTape (s : State a) (inputs : List Input) : List (BitVec 2) :=
  s.samplerSecond :: s.samplerFirst :: inputs.map (·.rawInputs)

def posedSamples (snapshots : List Pose) (apertures : List (BitVec 2)) : List Bool :=
  (cutsFrom 0 snapshots).map (fun cut => (apertures[cut.1]?.getD 0).getLsbD cut.2)

private theorem advance_tape (p : Program) (s : State a) (i : Input) (rest : List Input) (quiet : Quiet i) :
    (apertureTape s (i :: rest)).tail = apertureTape (step p i s) rest := by
  have samplers := step_samples p s i (quiet.runtime i)
  simp only [apertureTape, List.map_cons, List.tail_cons, samplers.1, samplers.2]

private theorem samples_cons (p : Program) (s : State a) (i : Input) (rest : List Input) (quiet : Quiet i) :
    posedSamples (poses p s (i :: rest)) (apertureTape s (i :: rest)) =
      s.rxEvent ++ posedSamples (poses p (step p i s) rest) (apertureTape (step p i s) rest) := by
  have shift := cuts_shift (poses p (step p i s) rest) 0 1
  simp only [Nat.add_zero] at shift
  rw [posedSamples, cuts_cons, Nat.zero_add, shift, List.map_append, List.map_map, ← advance_tape p s i rest quiet]
  cases cap : s.captures <;> simp [cap, State.rxEvent, posedSamples, apertureTape, Function.comp_def, Nat.add_comm]
  rfl

theorem capture_poses (p : Program) (s : State a) (inputs : List Input) (trace : BitTrace)
    (quiet : ∀ i ∈ inputs, Quiet i) :
    (traceRun p s trace inputs).captured =
      trace.captured ++ posedSamples (poses p s inputs) (apertureTape s inputs) := by
  induction inputs generalizing s trace with
  | nil => simp [traceRun, poses, posedSamples, cutsFrom]
  | cons i rest ih =>
    have first := quiet i List.mem_cons_self
    rw [traceRun, ih _ _ (fun j member => quiet j (List.mem_cons_of_mem _ member)), samples_cons p s i rest first]
    simp [BitTrace.step, first.cold, first.command, BitTrace.clock, List.append_assoc]

end Pinwheel.Program.StreamingCANQuiet
