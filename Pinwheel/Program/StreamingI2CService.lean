import Pinwheel.Program.StreamingI2CTx

/-! Progress for the standard image under eventual host credit and a peer
that meets each finite guard deadline at the actual raw-input aperture. -/
namespace Pinwheel.Program.StreamingI2CService
open StreamingReady StreamingI2CTrace

set_option linter.unusedSimpArgs false

private theorem expiry_zero (limit : WaitLimit) (countdown : BitVec 8)
    (expired : limit.expires countdown = true) : countdown = 0#8 := by
  cases limit with
  | unbounded => simp [WaitLimit.expires] at expired
  | misses _ => simpa [WaitLimit.expires] using expired

private theorem safe_next (s : State a) (i : Input) (shape : Positioned s)
    (ordinary : Unreleased i)
    (deadline : s.phase = .waiting → s.countdown = 0#8 → s.waitReady = true) :
    (step program i s).phase ≠ .fault := by
  rw [step_eq_clock s i shape ordinary]
  change (engine program s).phase ≠ .fault
  rcases shape.phase with phase | (low | low | high) | waiting | completed
  · have fetched := fetch s.pc.toNat shape.cursor
    have slots : s.pc.toNat = 0 ∨ s.pc.toNat = 1 ∨ s.pc.toNat = 2 ∨ s.pc.toNat = 3 ∨
        s.pc.toNat = 4 ∨ s.pc.toNat = 5 ∨ s.pc.toNat = 6 := by
      have := shape.cursor
      omega
    rcases slots with pc | pc | pc | pc | pc | pc | pc
    all_goals rw [engine,phase,fetched,pc]
    all_goals simp [row,State.stop,i2cHold,i2cStopLow]
    by_cases empty : s.remaining = 0#16 <;> simp [empty,phase]
  · cases credit : s.canReserve <;> simp [engine,low,credit]
  · by_cases count : s.countdown = 0#8
    · cases guarded : s.current.hasHighGuard <;>
        simp [engine,low,count,guarded,State.enterHigh]
    · simp [engine,low,count]
  · by_cases count : s.countdown = 0#8
    · cases stream : s.current.isStream <;> by_cases more : 1 < s.remaining.toNat <;>
        simp [engine,high,count,stream,more]
    · simp [engine,high,count]
  · cases ready : s.waitReady
    · have live : s.current.guard.limit.expires s.countdown = false := by
        apply Bool.eq_false_iff.mpr
        intro expired
        have contradictory := deadline waiting (expiry_zero _ _ expired)
        rw [ready] at contradictory
        contradiction
      simp [engine,waiting,ready,live]
    · cases stream : s.current.isStream <;> simp [engine,waiting,ready,stream,State.enterHigh]
  · simp [engine,completed]

abbrev atClock (s : State a) (incoming : Nat → Input) (n : Nat) : State a :=
  EventualService.state program s incoming n

private theorem bounded_guard (s : State a) (shape : Positioned s) (waiting : s.phase = .waiting) :
    s.current.guard.limit = .misses 30 := by
  have rowIs := shape.current (Or.inr waiting)
  have slots := shape.waits waiting
  rcases slots with pc | pc | pc <;> rw [rowIs,pc] <;> rfl

private theorem eventually_completed_from_ready (before : State a) (start : Input)
    (incoming : Nat → Input) (positive : 0 < start.startCount.toNat)
    (ordinary : ∀ k, Unreleased (incoming k))
    (ready : ∀ k, (atClock (before.start program start) incoming k).phase = .waiting →
      (atClock (before.start program start) incoming k).countdown = 0#8 →
      (atClock (before.start program start) incoming k).waitReady = true)
    (credits : ∀ k, (atClock (before.start program start) incoming k).phase = .boundary →
      ∃ m, k ≤ m ∧ (atClock (before.start program start) incoming m).canReserve = true) :
    ∃ edges, (run program (before.start program start)
      (EventualService.clocks incoming edges)).phase = .completed := by
  let initial := before.start program start
  have positions (k : Nat) : Positioned (atClock initial incoming k) := by
    induction k with
    | zero => exact positioned_start before start positive
    | succ k ih =>
      let s := atClock initial incoming k
      exact (positioned_step s (incoming k) ih (ordinary k)
        (safe_next s (incoming k) ih (ordinary k) (ready k))).1
  have fair : EventualService.Fair program initial incoming := by
    refine ⟨credits,?_⟩
    intro k waiting unbounded
    have finite := bounded_guard _ (positions k) waiting
    rw [finite] at unbounded
    contradiction
  obtain ⟨edges,retained⟩ := EventualService.started program before start incoming
    (fun k => (ordinary k).1) fair
  refine ⟨edges,?_⟩
  rw [← EventualService.state_eq_run] at retained ⊢
  change (atClock initial incoming edges).phase.retained = true at retained
  change (atClock initial incoming edges).phase = .completed
  rcases (positions edges).phase with phase | (phase | phase | phase) | phase | phase <;>
    simp [phase,Phase.retained] at retained ⊢

/-- Each raw input is the actual pad's open-drain resolution against the
independent peer drive for that clock. -/
def Connected (initial : State a) (incoming : Nat → Input)
    (peer : Nat → I2C.Pins) : Prop :=
  ∀ k, (incoming k).rawInputs =
    StreamingI2CRead.resolvedRaw (atClock initial incoming k).pins (peer k)

theorem Connected.finite {initial : State a} {incoming : Nat → Input} {peer : Nat → I2C.Pins}
    (connected : Connected initial incoming peer) (edges : Nat) :
    StreamingI2CTrace.Connected initial (EventualService.clocks incoming edges) peer := by
  intro earlier i rest history
  have inside : earlier.length < edges := by
    have length := congrArg List.length history
    simp only [EventualService.clocks,List.length_map,List.length_range,List.length_append,
      List.length_cons] at length
    omega
  have take := congrArg (List.take earlier.length) history
  rw [List.take_append_length,EventualService.clocks,← List.map_take,List.take_range,
    Nat.min_eq_left (Nat.le_of_lt inside)] at take
  have inputAt := congrArg (fun inputs : List Input => inputs[earlier.length]?) history
  have inputEq : incoming earlier.length = i := by
    change (EventualService.clocks incoming edges)[earlier.length]? =
      (earlier ++ i :: rest)[earlier.length]? at inputAt
    rw [EventualService.clocks,List.getElem?_map,List.getElem?_range inside,
      List.getElem?_append_right (Nat.le_refl _),Nat.sub_self] at inputAt
    exact Option.some.inj inputAt
  have cut : run program initial earlier = atClock initial incoming earlier.length := by
    exact (congrArg (run program initial) take.symm).trans
      (EventualService.state_eq_run program initial incoming earlier.length).symm
  rw [← inputEq,cut]
  exact connected earlier.length

/-- Every final WAIT poll sees its required bus level at the earlier raw
aperture. This covers the initial bus-idle wait, the data stretches, and
the STOP SCL wait. -/
def MeetsDeadlines (initial : State a) (incoming : Nat → Input) (peer : Nat → I2C.Pins) : Prop :=
  ∀ k, (atClock initial incoming k).phase = .waiting →
    (atClock initial incoming k).countdown = 0#8 →
    (atClock initial incoming k).current.guard.matches
      (StreamingI2CRead.resolvedRaw (atClock initial incoming (k-2)).pins (peer (k-2))) = true

private theorem first_poll_budget (before : State a) (start i : Input) (ordinary : i.Runtime) :
    (step program i (before.start program start)).countdown = 30#8 := by
  let initial := before.start program start
  have busy : initial.phase.busy = true := rfl
  have fetchPhase : initial.phase = .fetch := rfl
  have pc : initial.pc.toNat = 0 := rfl
  change (step program i initial).countdown = 30#8
  rw [step_busy_eq_clock program initial i ordinary busy,clock,engine,fetchPhase,pc,fetch 0 (by decide)]
  rfl

private theorem atClock_second (initial : State a) (incoming : Nat → Input)
    (ordinary : ∀ k, Unreleased (incoming k)) (k : Nat) :
    (atClock initial incoming (k+2)).samplerSecond = (incoming k).rawInputs := by
  let s := atClock initial incoming k
  change (step program (incoming (k+1)) (step program (incoming k) s)).samplerSecond = _
  rw [(step_samples program _ _ (ordinary (k+1)).1).2,(step_samples program _ _ (ordinary k).1).1]

/-- Eventual credit and raw peer responses at each declared deadline
guarantee a completed exchange without assuming a terminal state. -/
theorem eventually_completed (before : State a) (start : Input)
    (incoming : Nat → Input) (positive : 0 < start.startCount.toNat)
    (ordinary : ∀ k, Unreleased (incoming k)) (peer : Nat → I2C.Pins)
    (connected : Connected (before.start program start) incoming peer)
    (deadlines : MeetsDeadlines (before.start program start) incoming peer)
    (credits : ∀ k, (atClock (before.start program start) incoming k).phase = .boundary →
      ∃ m, k ≤ m ∧ (atClock (before.start program start) incoming m).canReserve = true) :
    ∃ edges, (run program (before.start program start)
      (EventualService.clocks incoming edges)).phase = .completed := by
  apply eventually_completed_from_ready before start incoming positive ordinary _ credits
  intro k waiting count
  cases k with
  | zero => cases waiting
  | succ k =>
    cases k with
    | zero =>
      have initial := first_poll_budget before start (incoming 0) (ordinary 0).1
      change (step program (incoming 0) (before.start program start)).countdown = 0#8 at count
      rw [initial] at count
      cases count
    | succ k =>
      have peerReady := deadlines (k+2) waiting count
      simp only [Nat.add_sub_cancel] at peerReady
      change (atClock (before.start program start) incoming (k+2)).waitReady = true
      rw [State.waitReady,atClock_second _ incoming ordinary,connected k]
      exact peerReady

private theorem slot_count (s : State a) (inputs : List Input) :
    (frameEvents s inputs).count .slot = (qualifiedStates s inputs).length := by
  induction inputs generalizing s with
  | nil => rfl
  | cons i rest ih =>
    have edge : (observed s).count .slot = (if s.captures then 1 else 0) := by
      by_cases start : s.phase = .fetch ∧ s.pc.toNat = 1
      · simp [observed,start,State.captures,start.1]
      · cases cap : s.captures
        · by_cases stop : s.phase = .fetch ∧ s.pc.toNat = 6 <;> simp [observed,start,cap,stop]
        · simp [observed,start,cap]
    simp only [frameEvents,qualifiedStates,List.count_append,List.length_append,ih,edge]
    cases s.captures <;> rfl

/-- A legitimate peer and eventual host credit give a finite, exact 64-byte
    read. The host may supply any finite prefix of its outgoing plan at each cut. -/
theorem read_under_service (before : State a) (start : Input) (incoming : Nat → Input)
    (count : start.startCount = 585#16) (ordinary : ∀ k, Unreleased (incoming k))
    (payload : List (BitVec 8)) (size : payload.length = 64) (peer : Nat → I2C.Pins) :
    let initial := before.start program start
    Connected initial incoming peer →
    MeetsDeadlines initial incoming peer →
    (∀ k, (atClock initial incoming k).phase = .boundary →
      ∃ m, k ≤ m ∧ (atClock initial incoming m).canReserve = true) →
    (∀ edges, ReadPeer initial (EventualService.clocks incoming edges) payload peer) →
    (∀ edges, (traceRun program initial {} (EventualService.clocks incoming edges)).accepted
      <+: StreamingI2CRead.hostBits) →
    ∃ edges, let inputs := EventualService.clocks incoming edges
      let trace := traceRun program initial {} inputs
      (run program initial inputs).phase = .completed ∧
      frameEvents initial inputs = [.start] ++ List.replicate 585 .slot ++ [.stop] ∧
      ResolvedFraming initial inputs peer ∧ StreamingI2CRead.project trace.captured = some payload := by
  intro initial connected deadlines credits legal host
  have positive : 0 < start.startCount.toNat := by rw [count]; decide +kernel
  obtain ⟨edges,completed⟩ := eventually_completed before start incoming positive ordinary peer
    connected deadlines credits
  let inputs := EventualService.clocks incoming edges
  let trace := traceRun program initial {} inputs
  have runtime : ∀ i ∈ inputs, Unreleased i := by
    intro i member
    obtain ⟨k,_,rfl⟩ := List.mem_map.mp member
    exact ordinary k
  have accepted := (started_trace program before start inputs).1.txOrder
  have qualified := started_tx_qualified before start inputs positive runtime completed
  have framing := completed_frame before start inputs positive runtime completed
  have length : trace.consumed.length = StreamingI2CRead.hostBits.length := by
    change (traceRun program (before.start program start) {} inputs).consumed.length = _
    rw [qualified,txQualified_states,List.length_map,← slot_count,framing,count,
      StreamingI2CRead.hostBits_length]
    decide +kernel
  have sent : trace.consumed <+: trace.accepted := ⟨_,by simpa [List.append_assoc] using accepted.symm⟩
  have ordered := (sent.trans (host edges)).eq_of_length length
  have result := completed_read before start inputs runtime completed count payload peer size
    (connected.finite edges) (legal edges) (qualified.symm.trans ordered)
  refine ⟨edges,completed,result.1,result.2.1,?_⟩
  rw [result.2.2]
  exact StreamingI2CRead.decode_wireBits payload size

end Pinwheel.Program.StreamingI2CService
