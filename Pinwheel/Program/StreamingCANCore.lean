import Pinwheel.Program.StreamingCANQuiet
import Pinwheel.Program.StreamingCANPeer
import Pinwheel.Program.StreamingReadyCompile

/-! The passive CAN image waits for a dominant SOF, then samples 64 equally
spaced data slots without using the host link during reception. -/
namespace Pinwheel.Program.StreamingCANCore
open StreamingReady StreamingUART.QuietTiming StreamingCANQuiet

set_option maxRecDepth 12000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

def idlePins : Pins := {}

def waitRow : Instruction := .driveWait idlePins {mask := 1}

def streamRow : Instruction := .stream {lowDuration := 13, highDuration := 16, receive := true} none

def source : List Instruction := [waitRow, streamRow, .halt]

theorem supported : Supported source := by decide +kernel

def image : Compiled source idlePins := ⟨source.map encode, supported, rfl⟩

abbrev program : Program := image.program

def captureCuts (s : State 1) (inputs : List Input) : List Nat :=
  (cutsFrom 0 (poses program s inputs)).map Prod.fst

private def waitingReference : State 1 :=
  {phase := .waiting, current := waitRow, total := 64, remaining := 64, pins := idlePins}

private def receiveReference : State 1 :=
  {waitingReference with phase := .fetch, pc := 1}

private def receiveCycles : Nat := 2050

private def reference : List Pose := poses program receiveReference (List.replicate receiveCycles {})

private theorem reference_no_wait : (reference.map Pose.phase).contains .waiting = false := by
  decide +kernel

private theorem reference_pins : (reference.map Pose.pins).all (· == idlePins) = true := by
  decide +kernel

private theorem reference_completed : reference.getLast?.map Pose.phase = some .completed := by
  decide +kernel

private theorem reference_cuts : cutsFrom 0 reference = (List.range 64).map (fun k => (15 + 32 * k, 0)) := by
  decide +kernel

private theorem fetch_wait : program.fetch 0 = some waitRow := image.program_fetch 0 (by decide +kernel)

private theorem idle_queue (q : Queue a) : q.tick none false = q := by
  cases q
  simp [Streaming.Queue.tick, Streaming.Queue.willPop, Streaming.Queue.willPush]

private theorem fetch_wait_erased (before : State 1) (command i : Input)
    (count : command.startCount = 64#16) (quiet : Quiet i) :
    erase (step program i (before.start program command)) = waitingReference := by
  rw [quiet_clock program _ i quiet]
  let seed := before.start program command
  have fetched : program.fetch seed.pc.toNat = some waitRow := fetch_wait
  have isFetch : seed.phase = .fetch := rfl
  have noTx : seed.enginePop = false := rfl
  have noRx : seed.enginePush = none := rfl
  change erase (clock program i seed) = _
  simp only [clock, engine, isFetch, fetched, waitRow, State.hostPush, State.hostPop, quiet.tx,
    quiet.rx, noTx, noRx, Streaming.Queue.willPush, Streaming.Queue.willPop, Bool.and_false,
    Bool.false_and, Bool.false_eq_true, if_false, Option.isSome_none, BitVec.add_zero,
    WaitLimit.initialCountdown]
  simp [seed, State.start, count, erase, waitingReference, waitRow, idle_queue]
  rfl

private theorem wait_guard (raw : BitVec 2) : waitRow.guard.matches raw = !raw[0] := by
  decide +revert +kernel

private theorem waiting_phase (s : State 1) (waiting : erase s = waitingReference) :
    s.phase = .waiting := congrArg State.phase waiting

private theorem waiting_row (s : State 1) (waiting : erase s = waitingReference) :
    s.current = waitRow := congrArg State.current waiting

private theorem waiting_pins (s : State 1) (waiting : erase s = waitingReference) :
    s.pins = idlePins := congrArg State.pins waiting

private theorem waiting_no_capture (s : State 1) (waiting : erase s = waitingReference) :
    s.captures = false := by
  simp [State.captures, waiting_row s waiting, waitRow, Instruction.isStream]

private theorem wait_step (s : State 1) (i : Input) (ordinary : Quiet i)
    (waiting : erase s = waitingReference) :
    erase (step program i s) = if s.samplerSecond[0] then waitingReference else receiveReference := by
  have phase := waiting_phase s waiting
  have row := waiting_row s waiting
  have ready : s.waitReady = !s.samplerSecond[0] := by
    rw [State.waitReady, row, wait_guard]
  have stream : s.current.isStream = false := by rw [row]; rfl
  have unlimited : s.current.guard.limit = .unbounded := by rw [row]; rfl
  have noTx : s.enginePop = false := by simp [State.enginePop, stream]
  have noRx : s.enginePush = none := by
    simp [State.enginePush, State.timedOut, unlimited, WaitLimit.expires,
      State.emittingCapture, waiting_no_capture s waiting]
  cases level : s.samplerSecond[0] <;>
    simp [quiet_clock program s i ordinary, clock, engine, phase, ready, level, unlimited, stream,
      State.hostPush, State.hostPop, ordinary.tx, ordinary.rx, noTx, noRx, idle_queue,
      Streaming.Queue.willPush, Streaming.Queue.willPop, WaitLimit.expires, WaitLimit.poll]
  · change {erase s with phase := .fetch, pc := s.pc + 1, countdown := 0} = receiveReference
    rw [← show (erase s).pc = s.pc from rfl, waiting]
    rfl
  · change {erase s with phase := .waiting} = waitingReference
    rw [waiting]
    rfl

private theorem sampler_at (initial : State 1) (inputs : List Input) (f : Nat)
    (ordinary : ∀ i ∈ inputs, Quiet i) (within : f + 2 ≤ inputs.length) :
    (run program initial (inputs.take (f + 2))).samplerSecond = (inputs[f]?.getD {}).rawInputs := by
  have first : f < inputs.length := by omega
  have second : f + 1 < inputs.length := by omega
  have pieces : inputs.take (f + 2) = inputs.take f ++ [inputs[f], inputs[f+1]] := by
    calc
      inputs.take (f+2) = inputs.take (f+1) ++ [inputs[f+1]] := List.take_succ_eq_append_getElem second
      _ = _ := by rw [List.take_succ_eq_append_getElem first, List.append_assoc]; rfl
  rw [pieces, (run_two_samples program initial _ _ _ ((ordinary _ (List.getElem_mem first)).runtime _)
      ((ordinary _ (List.getElem_mem second)).runtime _)).2, List.getElem?_eq_getElem first]
  rfl

private theorem released_append (s : State 1) (first rest : List Input)
    (earlier : ∀ pad ∈ pinTrace program s first, pad.enabled = 0)
    (later : ∀ pad ∈ pinTrace program (run program s first) rest, pad.enabled = 0) :
    ∀ pad ∈ pinTrace program s (first ++ rest), pad.enabled = 0 := by
  induction first generalizing s with
  | nil => exact later
  | cons i tail ih =>
    simp only [List.cons_append, pinTrace, List.mem_cons]
    intro pad member
    rcases member with rfl | inTail
    · exact earlier _ (by simp [pinTrace])
    · exact ih (step program i s) (fun p m => earlier p (by simp [pinTrace,m])) later pad inTail

private theorem input_bit (inputs : List Input) (k : Nat) (inside : k < inputs.length) :
    ((inputs[k]?.getD {}).rawInputs)[0] = rawBit (inputs.map (·.rawInputs)) k := by
  unfold rawBit
  rw [List.getElem?_map, List.getElem?_eq_getElem inside]
  rfl

private theorem wait_prefix (before : State 1) (command : Input) (inputs : List Input) (f n : Nat)
    (count : command.startCount = 64#16) (quiet : ∀ i ∈ inputs, Quiet i)
    (startHigh : command.rawInputs[0] = true)
    (idleBefore : ∀ k < f, rawBit (inputs.map (·.rawInputs)) k = true)
    (positive : 1 ≤ n) (beforeFall : n ≤ f+2) (within : n ≤ inputs.length) :
    let seed := before.start program command
    let early := inputs.take n
    erase (run program seed early) = waitingReference ∧
    cutsFrom 0 (poses program seed early) = [] ∧
    (∀ pad ∈ pinTrace program seed early, pad.enabled = 0) := by
  dsimp only
  induction n with
  | zero => omega
  | succ k ih =>
    have inside : k < inputs.length := by omega
    let seed := before.start program command
    let i := inputs[k]
    have iq : Quiet i := quiet _ (List.getElem_mem inside)
    rw [List.take_succ_eq_append_getElem inside]
    by_cases first : k = 0
    · subst k
      change erase (step program i seed) = waitingReference ∧
        cutsFrom 0 (poses program seed [i]) = [] ∧
        (∀ pad ∈ pinTrace program seed [i], pad.enabled = 0)
      have armed := fetch_wait_erased before command i count iq
      refine ⟨armed, rfl, ?_⟩
      have released := waiting_pins _ armed
      have initial : seed.pins = idlePins := rfl
      change ∀ pad ∈ [seed.pins, (step program i seed).pins], pad.enabled = 0
      rw [initial, released]
      simp [idlePins]
    · have old := ih (by omega) (by omega) (by omega)
      let s := run program seed (inputs.take k)
      have high : s.samplerSecond[0] = true := by
        by_cases second : k = 1
        · have headIn : 0 < inputs.length := by omega
          have head : inputs.take 1 = [inputs[0]] := List.take_succ_eq_append_getElem headIn
          change (run program seed (inputs.take k)).samplerSecond[0] = true
          rw [second, head]
          change (step program inputs[0] seed).samplerSecond[0] = true
          rw [(step_samples program seed _ ((quiet _ (List.getElem_mem headIn)).runtime _)).2]
          exact startHigh
        · have index : k = (k-2) + 2 := by omega
          have sample := sampler_at seed inputs (k-2) quiet (by omega)
          rw [← index] at sample
          change (run program seed (inputs.take k)).samplerSecond[0] = true
          rw [sample, input_bit inputs _ (by omega)]
          exact idleBefore _ (by omega)
      have next := wait_step s i iq old.1
      rw [high] at next
      refine ⟨?_, ?_, released_append seed _ _ old.2.2 ?_⟩
      · rw [run_append]
        exact next
      · rw [cuts_append, old.2.1, List.nil_append, cuts_cons, waiting_no_capture _ old.1]
        rfl
      · have prior := waiting_pins s old.1
        have after := waiting_pins _ next
        change ∀ pad ∈ [s.pins, (step program i s).pins], pad.enabled = 0
        rw [prior, after]
        simp [idlePins]

/-- The dominant SOF sample arms fixed-rate receive. The only 64 RX events
    read the pre-edge synchronizer exactly two clocks after their raw apertures. -/
theorem run_frame (before : State 1) (command : Input) (inputs : List Input) (f : Nat)
    (count : command.startCount = 64#16) (quiet : ∀ i ∈ inputs, Quiet i)
    (startHigh : command.rawInputs[0] = true)
    (idleBefore : ∀ k < f, rawBit (inputs.map (·.rawInputs)) k = true)
    (dominant : rawBit (inputs.map (·.rawInputs)) f = false)
    (length : inputs.length = f + 2053) :
    let seed := before.start program command
    (run program seed inputs).phase = .completed ∧
    (traceRun program seed {} inputs).captured = (apertures f).map (rawBit (inputs.map (·.rawInputs))) ∧
    (∀ pad ∈ pinTrace program seed inputs, pad.enabled = 0) ∧
    captureCuts seed inputs = (apertures f).map (· + 2) := by
  intro seed
  have inside : f + 2 < inputs.length := by omega
  let early := inputs.take (f+2)
  let trigger := inputs[f+2]
  let head := inputs.take (f+3)
  let tail := inputs.drop (f+3)
  let waiting := run program seed early
  let active := run program seed head
  have splitHead : head = early ++ [trigger] := List.take_succ_eq_append_getElem inside
  have whole : head ++ tail = inputs := List.take_append_drop _ _
  have headLength : head.length = f+3 := by
    simp only [head, List.length_take, Nat.min_eq_left (show f+3 ≤ inputs.length by omega)]
  have tailLength : tail.length = receiveCycles := by simp [tail, length, receiveCycles]
  have idle := wait_prefix before command inputs f (f+2) count quiet startHigh idleBefore
    (by omega) (by omega) (by omega)
  have activeStep : active = step program trigger waiting := by
    change run program seed head = _
    rw [splitHead, run_append]
    rfl
  have triggerLow : waiting.samplerSecond[0] = false := by
    change (run program seed (inputs.take (f+2))).samplerSecond[0] = false
    rw [sampler_at seed inputs f quiet (by omega), input_bit inputs f (by omega)]
    exact dominant
  have armed : erase active = receiveReference := by
    rw [activeStep]
    have armed := wait_step waiting trigger (quiet _ (List.getElem_mem inside)) idle.1
    rw [triggerLow] at armed
    exact armed
  have headCuts : cutsFrom 0 (poses program seed head) = [] := by
    rw [splitHead, cuts_append, idle.2.1, List.nil_append, cuts_cons, waiting_no_capture _ idle.1]
    rfl
  have headPins : ∀ pad ∈ pinTrace program seed head, pad.enabled = 0 := by
    rw [splitHead]
    apply released_append seed _ _ idle.2.2
    have first : waiting.pins = idlePins := waiting_pins _ idle.1
    have final : (step program trigger waiting).pins = idlePins := by
      rw [← activeStep]
      exact congrArg State.pins armed
    change ∀ pad ∈ [waiting.pins, (step program trigger waiting).pins], pad.enabled = 0
    rw [first, final]
    simp [idlePins]
  have tailPoses : poses program active tail = reference := by
    unfold reference
    rw [← tailLength]
    apply poses_equal program active receiveReference tail armed
      (fun j member => quiet j (List.mem_of_mem_drop member))
    intro obs member equ
    have waitIn : Phase.waiting ∈ reference.map Pose.phase := by
      rw [← equ]
      apply List.mem_map_of_mem
      simpa only [reference, ← tailLength] using member
    have forbidden := List.contains_iff_mem.mpr waitIn
    rw [reference_no_wait] at forbidden
    contradiction
  have complete : (run program seed inputs).phase = .completed := by
    have terminal := reference_completed
    rw [← tailPoses, poses_last] at terminal
    have final := Option.some.inj terminal
    rw [← whole, run_append]
    exact final
  have released : ∀ pad ∈ pinTrace program seed inputs, pad.enabled = 0 := by
    rw [← whole]
    apply released_append seed _ _ headPins
    intro pad member
    change pad ∈ pinTrace program active tail at member
    rw [← poses_pins, tailPoses] at member
    have pin := beq_iff_eq.mp (List.all_eq_true.mp reference_pins _ member)
    rw [pin]
    rfl
  have cuts : cutsFrom 0 (poses program seed inputs) = (apertures f).map (fun k => (k+2, 0)) := by
    have all := cuts_append program 0 seed head tail
    rw [whole, headCuts, List.nil_append, Nat.zero_add, headLength] at all
    change cutsFrom 0 (poses program seed inputs) = cutsFrom (f+3) (poses program active tail) at all
    have shift := cuts_shift reference 0 (f+3)
    simp only [Nat.add_zero] at shift
    rw [all, tailPoses, shift, reference_cuts, apertures, List.map_map, List.map_map]
    apply List.map_congr_left
    intro k _
    simp only [Function.comp_apply]
    congr 1
    omega
  refine ⟨complete, ?_, released, ?_⟩
  · rw [capture_poses program seed inputs {} quiet, posedSamples, cuts, List.map_map]
    rfl
  · simp only [captureCuts, cuts, List.map_map, Function.comp_def]

end Pinwheel.Program.StreamingCANCore
