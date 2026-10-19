import Pinwheel.Program.StreamingUART
import Pinwheel.Program.StreamingReadyTiming

/-! Full-state timing macros. Quiet means no delivered action; unused operands
remain arbitrary, exactly as in an idle actual frontend. Raw inputs may change
on every edge, and the samplers advance on every edge. -/
namespace Pinwheel.Program.StreamingUART.QuietTiming
open Pinwheel.Program.StreamingReady
set_option linter.unusedSimpArgs false

structure Quiet (i : Input) : Prop where
  cold : i.initialize = false
  command : i.command = 0
  tx : i.txPush = false
  rx : i.rxPop = false

theorem Quiet.runtime (i : Input) (quiet : Quiet i) : i.Runtime := by
  exact ⟨quiet.cold,by rw [quiet.command]; decide⟩

def sampleInputs (s : State a) (inputs : List Input) : State a :=
  inputs.foldl (fun s i => s.sample i.rawInputs) s

private theorem queue_idle (q : Streaming.Queue a) : q.tick none false = q := by
  cases q
  simp [Streaming.Queue.tick,Streaming.Queue.willPush,Streaming.Queue.willPop]

theorem quiet_clock (p : Program) (s : State a) (i : Input) (quiet : Quiet i) :
    step p i s = clock p i s := by
  simp [step,quiet.cold,quiet.command]

theorem timed_step (p : Program) (s : State a) (i : Input) (quiet : Quiet i)
    (phase : s.phase = .low ∨ s.phase = .high) (nonzero : s.countdown ≠ 0#8) :
    step p i s = {s.sample i.rawInputs with countdown := s.countdown-1#8} := by
  rcases phase with phase | phase
  all_goals simp [quiet_clock p s i quiet,clock,engine,phase,nonzero,Bool.beq_eq_decide_eq,
    State.hostPush,State.hostPop,quiet.tx,quiet.rx,State.enginePop,State.enginePush,
    State.emittingCapture,State.captures,State.timedOut,State.sample,queue_idle,
    Streaming.Queue.willPush,Streaming.Queue.willPop]

theorem sampleInputs_countdown (s : State a) (inputs : List Input) (countdown : BitVec 8) :
    sampleInputs {s with countdown := countdown} inputs = {sampleInputs s inputs with countdown := countdown} := by
  induction inputs generalizing s with
  | nil => rfl
  | cons i rest induction =>
    change sampleInputs {(s.sample i.rawInputs) with countdown := countdown} rest = _
    rw [induction]
    rfl

theorem timed_prefix (p : Program) (s : State a) (inputs : List Input)
    (phase : s.phase = .low ∨ s.phase = .high)
    (quiet : ∀ i ∈ inputs, Quiet i) (within : inputs.length ≤ s.countdown.toNat) :
    run p s inputs =
      {sampleInputs s inputs with countdown := BitVec.ofNat 8 (s.countdown.toNat-inputs.length)} := by
  induction inputs generalizing s with
  | nil => simp [run,sampleInputs]
  | cons i rest induction =>
    have positive : 0 < s.countdown.toNat := by simp only [List.length_cons] at within; omega
    have nonzero : s.countdown ≠ 0#8 := by
      intro zero
      simp [zero] at positive
    have next := timed_step p s i (quiet i (by simp)) phase nonzero
    have subtraction : (s.countdown-1#8).toNat = s.countdown.toNat-1 :=
      BitVec.toNat_sub_of_le (by change 1 ≤ s.countdown.toNat; omega)
    change run p (step p i s) rest = _
    rw [next]
    have later := induction ({s.sample i.rawInputs with countdown := s.countdown-1#8})
      (by simpa only [State.sample] using phase)
      (fun j member => quiet j (by simp [member])) (by
        simp only [subtraction]
        simp only [List.length_cons] at within
        omega)
    rw [later,sampleInputs_countdown]
    simp only [subtraction,List.length_cons,Nat.sub_sub,Nat.add_comm]
    rfl

theorem sampleInputs_eq (s : State a) (inputs : List Input) :
    sampleInputs s inputs =
      {s with
        samplerFirst := (sampleInputs s inputs).samplerFirst
        samplerSecond := (sampleInputs s inputs).samplerSecond} := by
  induction inputs generalizing s with
  | nil => rfl
  | cons i rest induction =>
    change sampleInputs (s.sample i.rawInputs) rest = _
    conv => lhs; rw [induction]
    rfl

@[simp] theorem sampleInputs_phase (s : State a) (inputs : List Input) :
    (sampleInputs s inputs).phase = s.phase := by rw [sampleInputs_eq]

@[simp] theorem sampleInputs_current (s : State a) (inputs : List Input) :
    (sampleInputs s inputs).current = s.current := by rw [sampleInputs_eq]

theorem run_append (p : Program) (s : State a) (before after : List Input) :
    run p s (before ++ after) = run p (run p s before) after := List.foldl_append

def highExit (s : State a) : State a :=
  {s with
    phase := if s.current.isStream && s.remaining.toNat > 1 then .boundary else .fetch
    pc := if s.current.isStream && s.remaining.toNat > 1 then s.pc else s.pc+1
    remaining := s.remaining-(if s.current.isStream then 1 else 0)
    pins := s.current.cell.basePins false s.lastCell}

def lowExit (s : State a) : State a :=
  {s.enterHigh with rx := s.rx.tick s.enginePush false,pins := s.highPins}

theorem high_step (p : Program) (s : State a) (i : Input) (quiet : Quiet i)
    (phase : s.phase = .high) (zero : s.countdown = 0#8) :
    step p i s = (highExit s).sample i.rawInputs := by
  simp [quiet_clock p s i quiet,clock,engine,phase,zero,highExit,
    State.hostPush,State.hostPop,quiet.tx,quiet.rx,State.enginePop,State.enginePush,
    State.emittingCapture,State.captures,State.timedOut,State.sample,queue_idle,
    Streaming.Queue.willPush,Streaming.Queue.willPop,Bool.beq_eq_decide_eq]

theorem low_step (p : Program) (s : State a) (i : Input) (quiet : Quiet i)
    (phase : s.phase = .low) (zero : s.countdown = 0#8) (unguarded : s.current.hasHighGuard = false) :
    step p i s = (lowExit s).sample i.rawInputs := by
  simp [quiet_clock p s i quiet,clock,engine,phase,zero,unguarded,lowExit,
    State.hostPush,State.hostPop,quiet.tx,quiet.rx,State.enginePop,State.sample,queue_idle,
    Streaming.Queue.willPush,Streaming.Queue.willPop,Bool.beq_eq_decide_eq,
    State.enterHigh,State.captureData]

theorem high_finish (p : Program) (s : State a) (inputs : List Input) (last : Input)
    (phase : s.phase = .high) (quiet : ∀ i ∈ inputs, Quiet i) (lastQuiet : Quiet last)
    (length : inputs.length = s.countdown.toNat) :
    run p s (inputs ++ [last]) =
      (highExit {sampleInputs s inputs with countdown := 0}).sample last.rawInputs := by
  rw [run_append,timed_prefix p s inputs (Or.inr phase) quiet (Nat.le_of_eq length)]
  simp only [length,Nat.sub_self]
  exact high_step p _ last lastQuiet (by simpa using phase) rfl

theorem low_finish (p : Program) (s : State a) (inputs : List Input) (last : Input)
    (phase : s.phase = .low) (quiet : ∀ i ∈ inputs, Quiet i) (lastQuiet : Quiet last)
    (length : inputs.length = s.countdown.toNat) (unguarded : s.current.hasHighGuard = false) :
    run p s (inputs ++ [last]) =
      (lowExit {sampleInputs s inputs with countdown := 0}).sample last.rawInputs := by
  rw [run_append,timed_prefix p s inputs (Or.inl phase) quiet (Nat.le_of_eq length)]
  simp only [length,Nat.sub_self]
  exact low_step p _ last lastQuiet (by simpa using phase) rfl (by simpa using unguarded)

theorem boundary_reserve (p : Program) (s : State a) (i : Input) (c : Cell)
    (quiet : Quiet i) (phase : s.phase = .boundary) (current : s.current = .stream c none)
    (transmit : c.transmit = false) (receive : c.receive = true) (room : s.rx.writable = true) :
    step p i s =
      {s.sample i.rawInputs with
        phase := .low
        countdown := BitVec.ofNat 8 c.lowDuration.val
        cellBit := false
        pins := c.dataPins false (s.remaining == 1) false} := by
  simp [quiet_clock p s i quiet,clock,engine,phase,current,State.canReserve,State.txReady,
    State.rxReady,transmit,receive,room,Instruction.isStream,Instruction.cell,State.lastCell,
    State.hostPush,State.hostPop,quiet.tx,quiet.rx,State.enginePop,State.enginePush,
    State.emittingCapture,State.captures,State.timedOut,State.sample,queue_idle,
    Streaming.Queue.willPush,Streaming.Queue.willPop,Bool.beq_eq_decide_eq]

def pulseFetch (s : State a) (c : Cell) : State a :=
  {s with phase := .boundary,current := .pulse c,pins := c.lowPins}

def pulseReserve (s : State a) (c : Cell) : State a :=
  {s with
    phase := .low
    countdown := BitVec.ofNat 8 c.lowDuration.val
    cellBit := false
    pins := c.lowPins}

def pulseFinish (s : State a) (c : Cell) : State a :=
  {s with
    phase := .fetch
    pc := s.pc+1
    current := .pulse c
    countdown := 0
    cellBit := false
    pins := c.lowPins}

theorem pulse_fetch (p : Program) (s : State a) (c : Cell) (i : Input) (quiet : Quiet i)
    (phase : s.phase = .fetch) (fetch : p.fetch s.pc.toNat = some (.pulse c)) :
    step p i s = (pulseFetch s c).sample i.rawInputs := by
  simp [quiet_clock p s i quiet,clock,engine,phase,fetch,pulseFetch,
    State.hostPush,State.hostPop,quiet.tx,quiet.rx,State.enginePop,State.enginePush,
    State.emittingCapture,State.captures,State.timedOut,State.sample,queue_idle,
    Streaming.Queue.willPush,Streaming.Queue.willPop,Bool.beq_eq_decide_eq]

theorem pulse_reserve (p : Program) (s : State a) (c : Cell) (i : Input) (quiet : Quiet i)
    (phase : s.phase = .boundary) (current : s.current = .pulse c) :
    step p i s = (pulseReserve s c).sample i.rawInputs := by
  simp [quiet_clock p s i quiet,clock,engine,phase,current,pulseReserve,State.canReserve,
    Instruction.isStream,Instruction.cell,State.hostPush,State.hostPop,quiet.tx,quiet.rx,
    State.enginePop,State.enginePush,State.emittingCapture,State.captures,State.timedOut,
    State.sample,queue_idle,Streaming.Queue.willPush,Streaming.Queue.willPop,Bool.beq_eq_decide_eq]

theorem sampleInputs_commute (f : State a → State a)
    (commute : ∀ s raw, (f s).sample raw = f (s.sample raw)) (s : State a) (inputs : List Input) :
    sampleInputs (f s) inputs = f (sampleInputs s inputs) := by
  induction inputs generalizing s with
  | nil => rfl
  | cons i rest induction =>
    change sampleInputs ((f s).sample i.rawInputs) rest = _
    rw [commute,induction]
    rfl

def pulseHigh (s : State a) (c : Cell) : State a :=
  {s with phase := .high,countdown := BitVec.ofNat 8 c.highDuration.val,pins := c.highPins}

theorem pulse_low_exit (s : State a) (c : Cell)
    (phase : s.phase = .low) (current : s.current = .pulse c) : lowExit s = pulseHigh s c := by
  simp [lowExit,pulseHigh,State.enterHigh,State.captureData,phase,current,Instruction.isStream,
    State.enginePush,State.emittingCapture,State.captures,State.timedOut,State.highPins,Instruction.cell,queue_idle]

@[simp] theorem sampleInputs_pulseFetch (s : State a) (c : Cell) (inputs : List Input) :
    sampleInputs (pulseFetch s c) inputs = pulseFetch (sampleInputs s inputs) c :=
  sampleInputs_commute (fun t => pulseFetch t c) (by intros; rfl) s inputs

@[simp] theorem sampleInputs_pulseReserve (s : State a) (c : Cell) (inputs : List Input) :
    sampleInputs (pulseReserve s c) inputs = pulseReserve (sampleInputs s inputs) c :=
  sampleInputs_commute (fun t => pulseReserve t c) (by intros; rfl) s inputs

@[simp] theorem sampleInputs_pulseHigh (s : State a) (c : Cell) (inputs : List Input) :
    sampleInputs (pulseHigh s c) inputs = pulseHigh (sampleInputs s inputs) c :=
  sampleInputs_commute (fun t => pulseHigh t c) (by intros; rfl) s inputs

@[simp] theorem sample_pulseFetch (s : State a) (c : Cell) (raw : BitVec 2) :
    (pulseFetch s c).sample raw = pulseFetch (s.sample raw) c := rfl
@[simp] theorem sample_pulseReserve (s : State a) (c : Cell) (raw : BitVec 2) :
    (pulseReserve s c).sample raw = pulseReserve (s.sample raw) c := rfl
@[simp] theorem sample_pulseHigh (s : State a) (c : Cell) (raw : BitVec 2) :
    (pulseHigh s c).sample raw = pulseHigh (s.sample raw) c := rfl
@[simp] theorem pulseHigh_countdown (s : State a) (c : Cell) (countdown : BitVec 8) :
    pulseHigh {s with countdown := countdown} c = pulseHigh s c := rfl

theorem pulse_run_segments (p : Program) (s : State a) (c : Cell)
    (first reserve : Input) (lowInputs : List Input) (lowLast : Input)
    (highInputs : List Input) (highLast : Input)
    (phase : s.phase = .fetch) (fetch : p.fetch s.pc.toNat = some (.pulse c))
    (quiet : ∀ i ∈ [first,reserve] ++ ((lowInputs ++ [lowLast]) ++ (highInputs ++ [highLast])), Quiet i)
    (lowLength : lowInputs.length = c.lowDuration.val)
    (highLength : highInputs.length = c.highDuration.val) :
    run p s ([first,reserve] ++ ((lowInputs ++ [lowLast]) ++ (highInputs ++ [highLast]))) =
      pulseFinish (sampleInputs s ([first,reserve] ++ ((lowInputs ++ [lowLast]) ++ (highInputs ++ [highLast])))) c := by
  have qfirst := quiet first (by simp)
  have qreserve := quiet reserve (by simp)
  have qlow := quiet lowLast (by simp)
  have qhigh := quiet highLast (by simp)
  change run p (step p reserve (step p first s)) ((lowInputs ++ [lowLast]) ++ (highInputs ++ [highLast])) = _
  rw [pulse_fetch p s c first qfirst phase fetch,pulse_reserve p _ c reserve qreserve rfl rfl]
  let beforeLow := (pulseReserve ((pulseFetch s c).sample first.rawInputs) c).sample reserve.rawInputs
  change run p beforeLow ((lowInputs ++ [lowLast]) ++ (highInputs ++ [highLast])) = _
  rw [run_append,low_finish p beforeLow lowInputs lowLast rfl
    (fun i member => quiet i (by simp [member])) qlow
    (by simp [beforeLow,pulseReserve,State.sample,lowLength,BitVec.toNat_ofNat,Nat.mod_eq_of_lt c.lowDuration.isLt]) rfl]
  rw [pulse_low_exit _ c (by simp [beforeLow,pulseReserve,State.sample])
    (by simp [beforeLow,pulseReserve,pulseFetch,State.sample])]
  rw [high_finish p _ highInputs highLast rfl
    (fun i member => quiet i (by simp [member])) qhigh
    (by simp [pulseHigh,State.sample,highLength,BitVec.toNat_ofNat,Nat.mod_eq_of_lt c.highDuration.isLt])]
  simp only [beforeLow,sample_pulseHigh,sample_pulseReserve,sample_pulseFetch,
    sampleInputs_pulseHigh,sampleInputs_countdown,sampleInputs_pulseReserve,sampleInputs_pulseFetch,pulseHigh_countdown]
  simp [beforeLow,highExit,pulseHigh,pulseReserve,pulseFetch,pulseFinish,
    State.sample,State.lastCell,Instruction.isStream,Instruction.cell,Streaming.Cell.basePins,
    sampleInputs,List.foldl_append]

private theorem split_at (inputs : List Input) (n : Nat) (within : n < inputs.length) :
    ∃ before last after, inputs = before ++ last :: after ∧ before.length = n := by
  induction n generalizing inputs with
  | zero =>
    cases inputs with
    | nil => simp at within
    | cons first rest => exact ⟨[],first,rest,rfl,rfl⟩
  | succ n induction =>
    cases inputs with
    | nil => simp at within
    | cons first rest =>
      obtain ⟨before,last,after,parts,length⟩ := induction rest (by simp only [List.length_cons] at within; omega)
      exact ⟨first::before,last,after,by simp [parts],by simp [length]⟩

theorem pulse_run (p : Program) (s : State a) (c : Cell) (inputs : List Input)
    (phase : s.phase = .fetch) (fetch : p.fetch s.pc.toNat = some (.pulse c))
    (quiet : ∀ i ∈ inputs, Quiet i)
    (length : inputs.length = c.lowDuration.val+c.highDuration.val+4) :
    run p s inputs = pulseFinish (sampleInputs s inputs) c := by
  cases inputs with
  | nil => simp at length
  | cons first rest =>
    cases rest with
    | nil => simp at length
    | cons reserve rest =>
      have remaining : rest.length = c.lowDuration.val+c.highDuration.val+2 := by
        simp only [List.length_cons] at length
        omega
      obtain ⟨lowInputs,lowLast,tail,parts,lowLength⟩ := split_at rest c.lowDuration.val (by omega)
      have tailLength : tail.length = c.highDuration.val+1 := by
        rw [parts] at remaining
        simp only [List.length_append,List.length_cons,lowLength] at remaining
        omega
      obtain ⟨highInputs,highLast,after,highParts,highLength⟩ := split_at tail c.highDuration.val (by omega)
      have empty : after = [] := by
        rw [highParts] at tailLength
        simp only [List.length_append,List.length_cons,highLength] at tailLength
        cases after with
        | nil => rfl
        | cons i rest => simp only [List.length_cons] at tailLength; omega
      subst after
      rw [highParts] at parts
      rw [parts] at quiet ⊢
      simpa only [List.cons_append,List.nil_append,List.append_assoc,List.singleton_append] using
        pulse_run_segments p s c first reserve lowInputs lowLast highInputs highLast phase fetch
        (by simpa only [List.cons_append,List.nil_append,List.append_assoc] using quiet)
        lowLength highLength

end Pinwheel.Program.StreamingUART.QuietTiming
