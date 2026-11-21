import Pinwheel.Hardware.StreamingReady.SegmentCadencedHost
import Pinwheel.Hardware.StreamingReady.SegmentPolicyCredit
import Pinwheel.Hardware.StreamingReady.SegmentTimingContract

/-! Derive the scheduled command windows of a causal clock tape from a host
    that paces its TX offers. The host uses its own timer and public flags. -/
namespace Pinwheel.Hardware.StreamingReady.SegmentPolicyTiming

open Pinwheel.Hardware SegmentCore SegmentPathControl SegmentCausal
open SegmentCadencedHost (Policy host)
open SegmentUnguardedReceive (ParkHistory)
open ProtocolOwnership (DrainInput)
open Pinwheel.Program.StreamingReady (Instruction Cell Guard)
open Pinwheel.Program.StreamingReadySegments

private theorem clock_split (registered : Bool) (driver : Host H) (peer : Peer P)
    (s : State a H P) (n : Nat) (before after : List (Values Core.Input))
    (split : clocks registered driver peer s n = before ++ after) :
    before = clocks registered driver peer s before.length ∧
      after = clocks registered driver peer (run registered driver peer s before.length) (n - before.length) := by
  have lengths := congrArg List.length split
  rw [clocks_length, List.length_append] at lengths
  have within : before.length ≤ n := by omega
  constructor
  · calc
      before = (clocks registered driver peer s n).take before.length := by rw [split, List.take_left]
      _ = _ := clocks_take _ _ _ _ _ _ within
  · calc
      after = (clocks registered driver peer s n).drop before.length := by rw [split, List.drop_left]
      _ = _ := clocks_drop _ _ _ _ _ _ within

private theorem park_phase (registered : Bool) (s : Values (Register a)) (inputs : List (Values Core.Input))
    (initial : s (.base .phase) = 2#3) (history : ParkHistory registered s inputs) :
    SegmentTiming.run registered s inputs (.base .phase) = 2#3 := by
  induction inputs generalizing s with
  | nil => exact initial
  | cons i rest ih =>
    obtain ⟨ordinary, blocked, later⟩ := history
    have parked := SegmentStreamStep.park_runtime registered i s ordinary initial blocked
    exact ih _ parked.phase later

/-- A reservation edge clears the host's TX wait age. Derive all later
    quiet aperture clocks from this reset rather than the peer response. -/
theorem after_reservation (policy : Policy) (registered : Bool) (peer : Peer P) (s : State a Nat P)
    (count bound : Nat) (cooldown : bound ≤ policy.cooldown)
    (boundary : s.core (.base .phase) = 2#3)
    (parks : List (Values Core.Input)) (admit : Values Core.Input) (rest : List (Values Core.Input))
    (split : clocks registered (host policy) peer s count = parks ++ @admit :: rest)
    (history : ParkHistory registered s.core parks)
    (credit : Core.credit.eval admit (project (SegmentTiming.run registered s.core parks)) = 1#1) :
    ∀ i ∈ rest.take bound, DrainInput i := by
  let running := run registered (host policy) peer s parks.length
  let stepped := step registered (host policy) peer running
  obtain ⟨past, future⟩ := clock_split registered (host policy) peer s count parks (@admit :: rest) split
  have coreEq : @running.core = @SegmentTiming.run a registered s.core parks := by
    unfold running
    rw [run_core, ← past]
  have phase : running.core (.base .phase) = 2#3 := by
    have preserved := park_phase registered s.core parks boundary history
    exact (congrFun (congrFun coreEq 3) (.base .phase)).trans preserved
  have actual : Core.credit.eval admit (project running.core) = 1#1 := by
    rw [coreEq]
    exact credit
  have flags := (SegmentHostService.available_iff_credit registered admit running.core phase).mpr actual
  have clear : status registered running .waitingTX = 0#1 :=
    (SegmentTransmitPolicy.waiting_input_independent registered quiet admit running.core).trans flags.1
  have reset : stepped.host = 0 := (SegmentCadencedHost.cleardown policy registered peer running clear).2
  have left : ∃ tailCount, rest = clocks registered (host policy) peer stepped tailCount := by
    cases remain : count - parks.length with
    | zero => simp [remain, clocks] at future
    | succ tailCount =>
      refine ⟨tailCount, ?_⟩
      rw [remain] at future
      exact (List.cons.inj (show @admit :: rest =
        @input Nat P a registered (host policy) peer running :: clocks registered (host policy) peer stepped tailCount
        from future)).2
  obtain ⟨tailCount, shape⟩ := left
  have capped : (clocks registered (host policy) peer stepped tailCount).take bound =
      clocks registered (host policy) peer stepped (min bound tailCount) := by
    by_cases within : bound ≤ tailCount
    · rw [Nat.min_eq_left within, clocks_take _ _ _ _ _ _ within]
    · have above : tailCount ≤ bound := by omega
      have fits : (clocks registered (host policy) peer stepped tailCount).length ≤ bound := by
        rw [clocks_length]
        exact above
      rw [List.take_of_length_le fits, Nat.min_eq_right above]
  rw [shape, capped]
  apply SegmentCadencedHost.quiet_clocks
  rw [reset, Nat.zero_add]
  exact Nat.le_trans (Nat.min_le_left _ _) cooldown

def requiredClocks (slots parkBound : Nat) : Instruction → Nat
  | .halt | .fault => 1
  | .pulse cell => SegmentTimedPulse.duration cell
  | .driveWait _ guard => guard.limit.initialCountdown.toNat + 2
  | .stream cell none => 1 + slots * SegmentTimedUnguarded.slotBudget cell parkBound
  | .stream cell (some guard) =>
      1 + slots * (parkBound + cell.lowDuration.val + guard.limit.initialCountdown.toNat + cell.highDuration.val + 4)

def requiredQuiet : Instruction → Nat
  | .halt | .fault | .stream _ none => 0
  | .pulse cell => cell.lowDuration.val + 1
  | .driveWait _ guard => guard.limit.initialCountdown.toNat + 1
  | .stream cell (some guard) => cell.lowDuration.val + guard.limit.initialCountdown.toNat + 2

private theorem countdown (g : Pinwheel.Program.StreamingReady.Guard) (n : Fin 255)
    (limit : g.limit = .misses n) : g.limit.initialCountdown.toNat = n.val := by
  rw [limit]
  simp [Pinwheel.Program.StreamingReady.WaitLimit.initialCountdown, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show n.val < 256 by omega)]

/-- The finite horizon supplies enough clocks at each reached public cut.
    TX chunks are selected by the independent host at its public offer
    cut. Neither condition names a successful wire value or end state. -/
structure Horizon (policy : Policy) (registered : Bool) (peer : Peer P)
    (s : State a Nat P) (rows : List Row) (count : Nat) : Prop where
  fetch : ∀ k ≤ count, (run registered (host policy) peer s k).core (.base .phase) = 1#3 →
    0 < count - k ∧ ∀ instruction, rows[((run registered (host policy) peer s k).core (.base .pc)).toNat]? =
      some (.cell instruction) →
      requiredClocks ((run registered (host policy) peer s k).core (.base .remaining)).toNat
        (policy.cooldown + 1) instruction ≤ count - k
  reserve : ∀ k ≤ count, (run registered (host policy) peer s k).core (.base .phase) = 2#3 →
    policy.cooldown + 2 ≤ count - k
  chunks : ∀ k ≤ count, let state := run registered (host policy) peer s k
    state.core (.base .phase) = 2#3 → status registered state .waitingTX = 1#1 →
    policy.cooldown ≤ state.host → SegmentPolicyCredit.PacketReady policy registered state
  quiet : ∀ (pc : Nat) (instruction : Instruction), rows[pc]? = some (.cell instruction) →
    requiredQuiet instruction ≤ policy.cooldown

private theorem drain_control (policy : Policy) (registered : Bool) (peer : Peer P) (s : State a Nat P)
    (fetch : s.core (.base .phase) = 1#3) : DrainInput (input registered (host policy) peer s) :=
  (SegmentCadencedHost.cleardown policy registered peer s
    (SegmentCadencedHost.waiting_clear_outside_boundary registered s (by simp [fetch]))).1

private theorem command_zero (policy : Policy) (registered : Bool) (peer : Peer P) (s : State a Nat P)
    (n : Nat) : ∀ i ∈ clocks registered (host policy) peer s n, i .initialize = 0#1 ∧ i .command = 0#4 := by
  induction n generalizing s with
  | zero => simp [clocks]
  | succ n ih =>
    intro i membership
    rcases List.mem_cons.mp membership with first | later
    · subst i
      exact ⟨rfl, rfl⟩
    · exact ih _ i later

private theorem rx_count (policy : Policy) (registered : Bool) (peer : Peer P) (s : State a Nat P)
    (empty : s.core (.base .rxCount) = 0#4) (k : Nat) :
    ((run registered (host policy) peer s k).core (.base .rxCount)).toNat ≤ 1 := by
  induction k with
  | zero => simp [run, empty]
  | succ k ih =>
    rw [run_add]
    let atEdge := run registered (host policy) peer s k
    let i : Values Core.Input := input registered (host policy) peer atEdge
    obtain ⟨generation, transfer, pop⟩ := SegmentPolicyCredit.tags policy registered peer atEdge
    exact SegmentReceivePolicy.rx_count_one_ordinary registered i atEdge.core rfl rfl generation transfer ih (fun _ => pop)

private theorem credit_at {count : Nat} (policy : Policy) (registered : Bool) (peer : Peer P) (s : State a Nat P)
    (boot : Values (Register a)) (start : Values Core.Input)
    (opened : @s.core = @Circuit.step _ _ _ (circuit a registered) start boot)
    (admitted : Core.starting.eval start (project boot) = 1#1) (depth : a ≤ 3)
    (horizon : Horizon policy registered peer s rows count) (k : Nat) (within : k ≤ count)
    (phase : (run registered (host policy) peer s k).core (.base .phase) = 2#3) :
    SegmentHostService.BoundedCredit registered (run registered (host policy) peer s k).core
      (clocks registered (host policy) peer (run registered (host policy) peer s k) (count - k))
      (policy.cooldown + 1) := by
  have empty : s.core (.base .rxCount) = 0#4 := by
    rw [opened]
    exact SegmentReceivePolicy.rx_count_at_start registered start boot admitted
  have size : 1 ≤ 2 ^ a := Nat.succ_le_of_lt (Nat.two_pow_pos _)
  have room := horizon.reserve k within phase
  apply SegmentPolicyCredit.bounded_credit policy registered peer _ _ room depth phase
  · intro j hj
    rw [← run_add]
    exact Nat.le_trans (rx_count policy registered peer s empty (k + j)) size
  · intro j hj
    dsimp only
    intro atBoundary waiting elapsed
    rw [← run_add] at atBoundary waiting elapsed ⊢
    refine ⟨?_, horizon.chunks (k + j) (by omega) atBoundary waiting elapsed⟩
    have coreEq := run_core registered (host policy) peer s (k + j)
    have atCut : SegmentTiming.run registered ((circuit a registered).step start boot)
        (clocks registered (host policy) peer s (k + j)) (.base .phase) = 2#3 := by
      rw [← opened, ← coreEq]
      exact atBoundary
    rw [coreEq, opened]
    exact SegmentTransmitPolicy.open_at_reservation registered start boot admitted _ (command_zero policy registered peer s _) atCut

private theorem guarded_supply (policy : Policy) (registered : Bool) (peer : Peer P) (s : State a Nat P)
    (count : Nat) (cell : Cell) (n : Fin 255)
    (quietBound : cell.lowDuration.val + n.val + 2 ≤ policy.cooldown)
    (credit : SegmentTimedUnguarded.CreditFrom registered s.core
      (clocks registered (host policy) peer s count) (policy.cooldown + 1)) :
    SegmentTimedGuarded.SupplyFrom registered s.core (clocks registered (host policy) peer s count)
      cell n (policy.cooldown + 1) := by
  intro before rest split phase room
  have served := credit before rest split phase
  obtain ⟨past, future⟩ := clock_split registered (host policy) peer s count before rest split
  let reached := run registered (host policy) peer s before.length
  have coreEq : @SegmentTiming.run a registered s.core before = @reached.core := by rw [past, ← run_core]
  have phaseEq : reached.core (.base .phase) = 2#3 := by
    change SegmentTiming.run registered s.core before (.base .phase) = 2#3 at phase
    exact (congrFun (congrFun coreEq 3) (.base .phase)).symm.trans phase
  rw [future] at room
  rw [coreEq, future] at served ⊢
  refine ⟨room, clocks_ordinary registered (host policy) peer reached _ (SegmentCadencedHost.runtime policy), served, ?_⟩
  intro parks admit tail shape history atCredit
  exact after_reservation policy registered peer reached _ _ quietBound phaseEq parks admit tail shape history atCredit

/-- The causal peer determines the samples and the host provides bounded
    credit and the required TX-quiet windows. The remaining numeric premises
    are sufficient lookahead and legal chunks at public TX offer offsets. -/
theorem timing {count : Nat} (policy : Policy) (registered : Bool) (peer : Peer P) (s : State a Nat P)
    (boot : Values (Register a)) (start : Values Core.Input)
    (opened : @s.core = @Circuit.step _ _ _ (circuit a registered) start boot)
    (admitted : Core.starting.eval start (project boot) = 1#1) (depth : a ≤ 3)
    (horizon : Horizon policy registered peer s rows count) :
    SegmentTimingContract.Timing registered rows s.core (clocks registered (host policy) peer s count)
      (policy.cooldown + 1) := by
  let driver := host policy
  refine ⟨clocks_ordinary registered driver peer s count (SegmentCadencedHost.runtime policy), ?_, ?_⟩
  · intro before remaining split fetch
    obtain ⟨past, future⟩ := clock_split registered driver peer s count before remaining split
    have lengths := congrArg List.length split
    rw [clocks_length, List.length_append] at lengths
    let reached := run registered driver peer s before.length
    have coreEq : @SegmentTiming.run a registered s.core before = @reached.core := by rw [past, ← run_core]
    have phase : reached.core (.base .phase) = 1#3 :=
      (congrFun (congrFun coreEq 3) (.base .phase)).symm.trans fetch
    have enough := (horizon.fetch before.length (by omega) phase).1
    cases tail : count - before.length with
    | zero => omega
    | succ n =>
      refine ⟨input registered driver peer reached, clocks registered driver peer (step registered driver peer reached) n, ?_,
        drain_control policy registered peer reached phase⟩
      rw [future, tail]
      rfl
  · intro before remaining pc instruction split fetch position row
    obtain ⟨past, future⟩ := clock_split registered driver peer s count before remaining split
    have lengths := congrArg List.length split
    rw [clocks_length, List.length_append] at lengths
    let reached := run registered driver peer s before.length
    let horizonLeft := count - before.length
    have coreEq : @SegmentTiming.run a registered s.core before = @reached.core := by rw [past, ← run_core]
    have phase : reached.core (.base .phase) = 1#3 :=
      (congrFun (congrFun coreEq 3) (.base .phase)).symm.trans fetch
    have atPC : (reached.core (.base .pc)).toNat = pc := by
      rw [← coreEq]
      exact position
    have room := (horizon.fetch before.length (by omega) phase).2 instruction (atPC ▸ row)
    have calendar : ∀ k, k ≤ horizonLeft →
        (run registered driver peer reached k).core (.base .phase) = 2#3 →
        SegmentHostService.BoundedCredit registered (run registered driver peer reached k).core
          (clocks registered driver peer (run registered driver peer reached k) (horizonLeft - k)) (policy.cooldown + 1) := by
      intro k within boundary
      have left : horizonLeft - k = count - (before.length + k) := by omega
      rw [left, show run registered driver peer reached k = run registered driver peer s (before.length + k)
        from (run_add _ _ _ _ _ _).symm]
      exact credit_at policy registered peer s boot start opened admitted depth horizon _ (by omega)
        (by unfold reached at boundary; rw [run_add]; exact boundary)
    have service : SegmentTimedUnguarded.CreditFrom registered reached.core
        (clocks registered driver peer reached horizonLeft) (policy.cooldown + 1) := by
      intro elapsed rest shape reservation
      obtain ⟨prefixEq, suffixEq⟩ := clock_split registered driver peer reached horizonLeft elapsed rest shape
      have sizes := congrArg List.length shape
      rw [clocks_length, List.length_append] at sizes
      have atCut : @SegmentTiming.run a registered reached.core elapsed =
          @(run registered driver peer reached elapsed.length).core := by rw [prefixEq, ← run_core]; simp [clocks_length]
      rw [atCut] at reservation ⊢
      rw [suffixEq]
      exact calendar elapsed.length (by omega) reservation
    have quietBound := horizon.quiet pc instruction row
    rw [coreEq, future]
    cases instruction with
    | halt | fault => trivial
    | pulse cell =>
      refine ⟨by simpa [SegmentTimingContract.RowTiming, requiredClocks, clocks_length] using room, ?_⟩
      intro i member
      have prefixEq : ((clocks registered driver peer reached horizonLeft).take (cell.lowDuration.val + 2)).drop 2 =
          ((clocks registered driver peer reached horizonLeft).drop 2).take cell.lowDuration.val := by
        rw [List.take_drop, Nat.add_comm]
      have clear := SegmentCadencedHost.waiting_clear_outside_boundary registered reached (by simp [phase])
      apply SegmentCadencedHost.clear_prefix_drains policy registered peer reached clear horizonLeft (cell.lowDuration.val + 2)
      · simp only [requiredClocks, SegmentTimedPulse.duration] at room
        omega
      · simp only [requiredQuiet] at quietBound
        omega
      · rw [← prefixEq] at member
        exact List.mem_of_mem_drop member
    | driveWait pins guard =>
      intro n limit
      have size := countdown guard n limit
      have enough : n.val + 2 ≤ horizonLeft := by simpa [requiredClocks, size] using room
      have clear := SegmentCadencedHost.waiting_clear_outside_boundary registered reached (by simp [phase])
      exact ⟨by simpa [clocks_length] using enough,
        SegmentCadencedHost.clear_prefix_drains policy registered peer reached clear horizonLeft _ enough
          (by simp only [requiredQuiet, size] at quietBound; omega)⟩
    | stream cell guard =>
      cases guard with
      | none =>
        exact ⟨by simpa [requiredClocks, clocks_length] using room, service⟩
      | some g =>
        intro n limit
        have size := countdown g n limit
        exact ⟨by simpa [requiredClocks, size, SegmentTimedGuarded.slotBudget, clocks_length] using room,
          guarded_supply policy registered peer reached horizonLeft cell n
            (by simpa [requiredQuiet, size] using quietBound) service⟩

/-- Start a supported image, attach the independent host and peer, and
    derive admission on the causal tape from its service horizon. -/
theorem from_start (image : Image rows budget) (supported : SegmentTimingImages.SupportedRows rows)
    (policy : Policy) (registered : Bool) (peer : Peer P) (boot : Values (Register a))
    (start : Values Core.Input) (hostAge : Nat) (peerState : P) (count : Nat)
    (installed : Installed rows boot) (admitted : Core.starting.eval start (project boot) = 1#1)
    (depth : a ≤ 3) :
    let opened : State a Nat P := ⟨(circuit a registered).step start boot, hostAge, peerState⟩
    let tape := clocks registered (host policy) peer opened count
    Horizon policy registered peer opened rows count →
    ∃ (active : List (Values Core.Input)) (last : Values Core.Input) (rest : List (Values Core.Input))
      (ending : Execution.Terminal), tape = active ++ @last :: rest ∧
      SegmentAdmission.Admitted image registered boot start active last ending := by
  intro opened tape horizon
  exact SegmentTimingContract.from_start image supported registered boot start tape (policy.cooldown + 1)
    installed admitted (timing policy registered peer opened boot start rfl admitted depth horizon)

/-- The same causal host supplies bounded rows in a program that can also
    await independently timed peer events. The event contract supplies only
    progress at those waits; ownership and the selected edge are derived. -/
theorem from_start_with_events (image : Image rows budget)
    (policy : Policy) (registered : Bool) (peer : Peer P) (boot : Values (Register a))
    (start : Values Core.Input) (hostAge : Nat) (peerState : P) (count : Nat)
    (installed : Installed rows boot) (admitted : Core.starting.eval start (project boot) = 1#1)
    (depth : a ≤ 3)
    (receiving : ∀ (pc : Nat) (cell : Cell) (g : Guard),
      rows[pc]? = some (Row.cell (.stream cell (some g))) → cell.receive = true) :
    let opened : State a Nat P := ⟨(circuit a registered).step start boot, hostAge, peerState⟩
    let tape := clocks registered (host policy) peer opened count
    Horizon policy registered peer opened rows count →
    SegmentTimingContract.Events registered rows opened.core tape (policy.cooldown + 1) →
    ∃ (active : List (Values Core.Input)) (last : Values Core.Input) (rest : List (Values Core.Input))
      (ending : Execution.Terminal), tape = active ++ @last :: rest ∧
      SegmentAdmission.Admitted image registered boot start active last ending := by
  intro opened tape horizon events
  exact SegmentTimingContract.from_start_with_events image registered boot start tape (policy.cooldown + 1)
    installed admitted (timing policy registered peer opened boot start rfl admitted depth horizon)
    events receiving

end Pinwheel.Hardware.StreamingReady.SegmentPolicyTiming
