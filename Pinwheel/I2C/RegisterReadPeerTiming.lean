import Pinwheel.I2C.RegisterReadFetch
import Pinwheel.I2C.RegisterReadPeer

namespace Pinwheel.I2C.RegisterReadPeer

open RegisterReadFetch

def observationsFrom (target : Target) (state : Pair) : Nat → List Observation
  | 0 => []
  | n + 1 => RegisterReadFetch.observe request state.1 (.step (drive state.2)) ::
    observationsFrom target (edge cfg request target state) n

def observations (target : Target) (clocks : Nat) : List Observation :=
  observationsFrom target start clocks

private theorem observationsFrom_length (target : Target) (state : Pair) (clocks : Nat) :
    (observationsFrom target state clocks).length = clocks := by
  induction clocks generalizing state with
  | zero => rfl
  | succ clocks ih => simp only [observationsFrom, List.length_cons, ih]

private theorem observationsFrom_add (target : Target) (state : Pair) (left right : Nat) :
    observationsFrom target state (left + right) = observationsFrom target state left ++
      observationsFrom target (run cfg request target state left) right := by
  induction left generalizing state with
  | zero => simp only [Nat.zero_add, observationsFrom, run, List.nil_append]
  | succ left ih =>
    simp only [Nat.succ_add, observationsFrom, run, List.cons_append, ih]

private theorem observationsFrom_get (target : Target) (state : Pair) (n k : Nat) :
    (observationsFrom target state n)[k]? = if k < n then
      let atClock := run cfg request target state k
      some (RegisterReadFetch.observe request atClock.1 (.step (drive atClock.2)))
    else none := by
  induction n generalizing state k with
  | zero => simp [observationsFrom]
  | succ n ih =>
    cases k with
    | zero => simp [observationsFrom, run]
    | succ k => simp [observationsFrom, run, ih, Nat.succ_lt_succ_iff]

private theorem observations_blind (target : Target) (clocks : Nat) (within : clocks ≤ 134) :
    observations target clocks = observations {target with payload := 0} clocks := by
  apply List.ext_getElem?
  intro k
  simp only [observations, observationsFrom_get]
  split
  · rename_i present
    rw [show run cfg request target start k = run cfg request {target with payload := 0} start k from
      prefix_payload_independent target k (by omega)]
  · rfl

def Target.firstAckTiming (target : Target) : AckTiming :=
  ⟨116 + target.extra, 121 + target.extra, 121 + target.extra, 129 + target.extra⟩

def firstAckWindow : AckWindow := ⟨4, 5, 9⟩

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem firstAck_zero (nack : Option (Fin 3)) (delay : Fin 6) :
    let target : Target := ⟨0, nack, delay⟩
    target.firstAckTiming.Observed (observations target 134) 8 (nack == some 0) := by
  have stretch : delay = 0 ∨ delay = 1 ∨ delay = 2 ∨ delay = 3 ∨ delay = 4 ∨ delay = 5 := by omega
  have branches : nack = none ∨ nack = some 0 ∨ nack = some 1 ∨ nack = some 2 := by
    cases nack with
    | none => exact Or.inl rfl
    | some stage =>
      have branch : stage = 0 ∨ stage = 1 ∨ stage = 2 := by omega
      simpa using branch
  rcases branches with rfl | rfl | rfl | rfl <;>
    rcases stretch with rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide +kernel

private theorem firstAck_prefix (target : Target) :
    target.firstAckTiming.Observed (observations target 134) 8 (target.nack == some 0) := by
  rw [observations_blind target 134 (by decide)]
  exact firstAck_zero target.nack target.initialStretch

theorem firstAck_fits (target : Target) : target.firstAckTiming.Fits firstAckWindow := by
  simp only [Target.firstAckTiming, AckTiming.Fits, firstAckWindow]
  omega

private theorem observed_append {timing : AckTiming} {initial : List Observation}
    (tail : List Observation) {slot : Fin 16} {value : Bool}
    (observed : timing.Observed initial slot value) (fits : timing.Fits firstAckWindow)
    (within : timing.nextRise < initial.length) : timing.Observed (initial ++ tail) slot value := by
  have level (k : Nat) (earlier : k < initial.length) :
      sclAt (initial ++ tail) k = sclAt initial k := by
    simp only [sclAt, List.getElem?_append_left earlier]
  have edge (start stop : Bool) (k : Nat) (earlier : k < initial.length)
      (change : sclEdge initial start stop k) : sclEdge (initial ++ tail) start stop k := by
    obtain ⟨j, index, fromLevel, toLevel⟩ := change
    exact ⟨j, index, (level j (by omega)).trans fromLevel, (level k earlier).trans toLevel⟩
  have riseSample := Nat.le_trans (Nat.le_add_right timing.rise firstAckWindow.earliestSample) fits.1
  obtain ⟨_, _, sampleFall, fallRise, _⟩ := fits
  refine ⟨edge _ _ _ (by omega) observed.rise, ?_, edge _ _ _ (by omega) observed.fall,
    edge _ _ _ within observed.nextRise, ?_, ?_⟩
  · obtain ⟨j, index, capture⟩ := observed.sample
    exact ⟨j, index, by rwa [List.getElem?_append_left (by omega)]⟩
  · intro k lo hi
    exact (level k (by omega)).trans (observed.high k lo hi)
  · intro k lo hi
    exact (level k (by omega)).trans (observed.low k lo hi)

/-- The target's first ACK is sampled five clocks after the resolved rise.
    The result includes the following rise and all intervening wire levels. -/
theorem firstAck_observed (target : Target) (clocks : Nat) (enough : 134 ≤ clocks) :
    target.firstAckTiming.Observed (observations target clocks) 8 (target.nack == some 0) := by
  rw [← Nat.add_sub_of_le enough, observations, observationsFrom_add]
  apply observed_append _ (firstAck_prefix target) (firstAck_fits target)
  rw [observations, observationsFrom_length]
  have := target.initialStretch.isLt
  simp only [Target.firstAckTiming, Target.extra]
  omega

theorem firstAck_low_slack (target : Target) :
    target.firstAckTiming.nextRise + 1 ≤ target.firstAckTiming.fall + firstAckWindow.lowLimit := by
  simp only [Target.firstAckTiming, firstAckWindow]
  omega

theorem firstDispatch_within_ack_low (target : Target) :
    target.firstAckTiming.fall ≤ target.firstDispatch ∧ target.firstDispatch < target.firstAckTiming.nextRise := by
  simp only [Target.firstAckTiming, Target.firstDispatch]
  omega

end Pinwheel.I2C.RegisterReadPeer
