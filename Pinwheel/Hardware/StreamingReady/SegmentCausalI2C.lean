import Pinwheel.Hardware.StreamingReady.SegmentCausal
import Pinwheel.Program.StreamingI2CRead
import Pinwheel.I2C.RegisterReadPeer

/-! A causal target for the segmented core. Both sides use their old drive
    state to resolve each pin. The target sees that bus sample only. -/
namespace Pinwheel.Hardware.StreamingReady.SegmentCausalI2C

open Pinwheel.Hardware SegmentCausal SegmentCore
open Pinwheel.Program.StreamingReady (Guard)
open Pinwheel.Program.StreamingI2CRead (busRaw controllerPins resolvedRaw resolvedRaw_scl)
open Pinwheel.I2C (Bus Drive Pins resolve resolveLine)
open Pinwheel.I2C.RegisterReadPeer (State Target drive initial)
open SegmentRawAperture (LoadedGuard)
open ProtocolOwnership (DrainInput)

def decodeBus (raw : BitVec 2) : Bus := ⟨raw.getLsbD 0, raw.getLsbD 1⟩

private theorem decodeBus_roundtrip (bus : Bus) : decodeBus (busRaw bus) = bus := by
  cases bus with
  | mk scl sda => cases scl <;> cases sda <;> rfl

def peer (target : Target) : Peer State where
  resolve state pads := resolvedRaw pads (drive state)
  next state raw := Pinwheel.I2C.RegisterReadPeer.step target state (decodeBus raw)

theorem next_peer (registered : Bool) (host : Host H) (target : Target)
    (s : SegmentCausal.State a H State) :
    (step registered host (peer target) s).peer =
      Pinwheel.I2C.RegisterReadPeer.step target s.peer (resolve (controllerPins (pads registered s)) (drive s.peer)) := by
  change Pinwheel.I2C.RegisterReadPeer.step target s.peer
    (decodeBus (busRaw (resolve (controllerPins (pads registered s)) (drive s.peer)))) = _
  rw [decodeBus_roundtrip]

/-- A stretch starts only on a falling resolved edge. While nonzero it
    holds SCL low, so its own drive cannot create a second falling edge. -/
structure StretchBound (target : Target) (state : State) : Prop where
  count : state.left ≤ target.initialStretch.val
  held : state.left ≠ 0 → state.previous.scl = false

theorem StretchBound.initial (target : Target) : StretchBound target initial := by
  exact ⟨Nat.zero_le _, fun incompatible => (incompatible rfl).elim⟩

private theorem left_update (target : Target) (state : State) (bus : Bus) :
    (Pinwheel.I2C.RegisterReadPeer.step target state bus).left =
      if (state.previous.scl && !bus.scl) && (state.starts != 0 && !state.stopped) &&
          state.starts == 1 && state.slots == 0 then target.initialStretch.val else state.left - 1 := rfl

private theorem scl_low_if_held (ctl : Pins) (state : State) (held : state.left ≠ 0) :
    (resolve ctl (drive state)).scl = false := by
  simp [resolve, drive, held, resolveLine]

theorem StretchBound.step (target : Target) (state : State) (ctl : Pins) (valid : StretchBound target state) :
    StretchBound target (Pinwheel.I2C.RegisterReadPeer.step target state (resolve ctl (drive state))) := by
  let bus := resolve ctl (drive state)
  refine ⟨?_, ?_⟩
  · rw [left_update]
    split
    · exact Nat.le_refl _
    · exact Nat.le_trans (Nat.sub_le _ _) valid.count
  · intro nonzero
    change bus.scl = false
    by_cases held : state.left = 0
    · change (Pinwheel.I2C.RegisterReadPeer.step target state bus).left ≠ 0 at nonzero
      rw [left_update] at nonzero
      cases observation : bus.scl with
      | false => rfl
      | true => simp [observation, held] at nonzero
    · exact scl_low_if_held ctl state held

theorem stretch_run (registered : Bool) (host : Host H) (target : Target)
    (s : SegmentCausal.State a H State) (n : Nat) (valid : StretchBound target s.peer) :
    StretchBound target (run registered host (peer target) s n).peer := by
  induction n generalizing s with
  | zero => exact valid
  | succ n ih =>
    apply ih (step registered host (peer target) s)
    rw [next_peer]
    exact StretchBound.step target s.peer _ valid

private theorem count_down (target : Target) (state : State) (ctl : Pins)
    (valid : StretchBound target state) (released : ctl.scl = .release) :
    (Pinwheel.I2C.RegisterReadPeer.step target state (resolve ctl (drive state))).left = state.left - 1 := by
  rw [left_update]
  by_cases held : state.left = 0
  · have high : (resolve ctl (drive state)).scl = true := by simp [resolve, resolveLine, drive, released, held]
    simp [high]
  · simp [valid.held held]

/-- The previous peer counter drops once per clock while the controller
    leaves SCL undriven, even if SDA changes. -/
theorem stretch_counts_down (registered : Bool) (host : Host H) (target : Target)
    (s : SegmentCausal.State a H State) (n : Nat) (valid : StretchBound target s.peer)
    (released : ∀ k < n, (pads registered (run registered host (peer target) s k)).enabled.getLsbD 0 = false) :
    (run registered host (peer target) s n).peer.left = s.peer.left - n := by
  induction n generalizing s with
  | zero => simp [run]
  | succ n ih =>
    let next := step registered host (peer target) s
    have validNext : StretchBound target next.peer := by
      rw [show next.peer = _ from next_peer registered host target s]
      exact StretchBound.step target s.peer _ valid
    have releaseNext : ∀ k < n,
        (pads registered (run registered host (peer target) next k)).enabled.getLsbD 0 = false := by
      intro k inside
      exact released (k + 1) (Nat.succ_lt_succ inside)
    have releaseNow : (controllerPins (pads registered s)).scl = .release := by
      have atZero := released 0 (Nat.zero_lt_succ n)
      simpa [run, controllerPins, Pinwheel.Program.StreamingI2CRead.drive, atZero]
    change (run registered host (peer target) next n).peer.left = _
    rw [ih next validNext releaseNext, show next.peer = _ from next_peer registered host target s]
    rw [count_down target s.peer _ valid releaseNow, Nat.sub_sub, Nat.add_comm]

/-- Once the controller continuously releases SCL for the old stretch
    budget, it obtains a resolved high sample. -/
theorem sample_by_stretch_bound (registered : Bool) (host : Host H) (target : Target)
    (s : SegmentCausal.State a H State) (bound : Nat) (valid : StretchBound target s.peer)
    (enough : target.initialStretch.val ≤ bound)
    (released : ∀ k ≤ bound, (pads registered (run registered host (peer target) s k)).enabled.getLsbD 0 = false) :
    (resolved registered (peer target) (run registered host (peer target) s bound)).getLsbD 0 = true := by
  have countdown := stretch_counts_down registered host target s bound valid
    (fun k inside => released k (Nat.le_of_lt inside))
  have expired : (run registered host (peer target) s bound).peer.left = 0 := by
    rw [countdown]
    exact Nat.sub_eq_zero_of_le (Nat.le_trans valid.count enough)
  change (resolvedRaw _ _).getLsbD 0 = true
  rw [resolvedRaw_scl, released bound (Nat.le_refl _)]
  simp [drive, expired]

/-- A SCL-only guard sees the physically released clock after the two
    sampler clocks. The release bound is on old pad drives and target
    policy state, so it can be used to justify a guard deadline. -/
theorem guard_by_stretch_bound (registered : Bool) (host : Host H) (target : Target)
    (s : SegmentCausal.State a H State) (bound : Nat) (valid : StretchBound target s.peer)
    (enough : target.initialStretch.val ≤ bound)
    (released : ∀ k ≤ bound, (pads registered (run registered host (peer target) s k)).enabled.getLsbD 0 = false)
    (ordinary : host.Runtime) (g : Guard) (clockMask : g.mask = 1#2) (clockHigh : g.expected = 1#2)
    (loaded : LoadedGuard g (run registered host (peer target) s (bound + 2)).core) :
    SegmentTiming.ready (input registered host (peer target) (run registered host (peer target) s (bound + 2)))
      (run registered host (peer target) s (bound + 2)).core = 1#1 := by
  have scl := sample_by_stretch_bound registered host target s bound valid enough released
  rw [guard_after_two registered host (peer target) s bound ordinary g loaded]
  have high : ∀ raw : BitVec 2, raw.getLsbD 0 = true → raw &&& 1#2 = 1#2 := by decide +kernel
  simp [Guard.matches, clockMask, clockHigh, high _ scl]

private theorem history_take (registered : Bool) (s : Values (Register a))
    (inputs : List (Values Core.Input)) (k : Nat)
    (history : SegmentTiming.MissHistory registered s inputs) :
    SegmentTiming.MissHistory registered s (inputs.take k) := by
  induction k generalizing s inputs with
  | zero => trivial
  | succ k ih =>
    cases inputs with
    | nil => trivial
    | cons clock rest =>
      exact ⟨history.1, history.2.1, ih _ _ history.2.2⟩

/-- Start in a bounded wait with SCL released. If the peer stays low, each
    missed poll preserves the controller's released SCL state. The target
    therefore runs out of stretch clocks and the loaded guard necessarily
    qualifies after at most two further sampler clocks. No index of a
    successful poll or continued release promise is supplied. -/
theorem guard_must_qualify (registered : Bool) (host : Host H) (target : Target)
    (s : SegmentCausal.State a H State) (bound : Nat) (valid : StretchBound target s.peer)
    (enough : target.initialStretch.val ≤ bound)
    (ordinary : host.Runtime)
    (draining : ∀ i ∈ clocks registered host (peer target) s (bound + 3), DrainInput i)
    (g : Guard) (clockMask : g.mask = 1#2) (clockHigh : g.expected = 1#2)
    (loaded : LoadedGuard g s.core) (waiting : s.core (.base .phase) = 7#3)
    (bounded : SegmentTiming.guardBudget s.core ≠ 0#8)
    (room : bound + 2 ≤ (s.core (.base .countdown)).toNat)
    (released : (pads registered s).enabled.getLsbD 0 = false) :
    ∃ (prior : List (Values Core.Input)) (last : Values Core.Input) (rest : List (Values Core.Input)),
      clocks registered host (peer target) s (bound + 3) = prior ++ @last :: rest ∧
      prior.length ≤ bound + 2 ∧ SegmentTiming.MissHistory registered s.core prior ∧
        SegmentTiming.ready last (SegmentTiming.run registered s.core prior) = 1#1 := by
  let tape := clocks registered host (peer target) s (bound + 3)
  let old := s.core (.base .stage2)
  let recent := s.core (.base .stage1)
  have length : tape.length = bound + 3 := clocks_length registered host (peer target) s _
  obtain ⟨prior, last, rest, split, within, missed, outcome⟩ :=
    SegmentRawAperture.select_poll g old recent tape (bound + 2) (by rw [length]; omega)
  have priorOrdinary : ∀ i ∈ prior, DrainInput i := by
    intro i member
    apply draining i
    change @i ∈ tape
    rw [split]
    exact List.mem_append_left _ member
  have traced := SegmentRawAperture.poll_from_raw registered s.core g old recent prior last rfl rfl
    priorOrdinary waiting loaded bounded (Nat.le_trans within room) missed
  refine ⟨prior, last, rest, split, within, traced.history, ?_⟩
  cases outcome with
  | inl success => rw [traced.comparator, success]; rfl
  | inr full =>
    have prefixEq (m : Nat) (inside : m ≤ prior.length) :
        clocks registered host (peer target) s m = prior.take m := by
      have priorEq : tape.take prior.length = prior := by rw [split, List.take_left]
      rw [← priorEq, List.take_take, Nat.min_eq_left inside]
      exact (clocks_take registered host (peer target) s (bound + 3) m (by omega)).symm
    have liveRelease : ∀ m ≤ bound,
        (pads registered (run registered host (peer target) s m)).enabled.getLsbD 0 = false := by
      intro m withinBound
      have pref := SegmentTiming.miss_prefix registered s.core (prior.take m) waiting bounded
        (history_take registered s.core prior m traced.history)
        (Nat.le_trans (List.length_take_le _ _) (by omega))
      have pose := pref.pose.enabled
      rw [← prefixEq m (by omega), ← run_core] at pose
      change ((run registered host (peer target) s m).core (.base .enabled)).getLsbD 0 = false
      rw [pose]
      exact released
    let actual := run registered host (peer target) s (bound + 2)
    have actualCore : @actual.core = @SegmentTiming.run a registered s.core prior := by
      have prefixMatches := prefixEq (bound + 2) (by omega)
      rw [← full, List.take_length] at prefixMatches
      exact (run_core registered host (peer target) s _).trans
        (congrArg (fun clocks => @SegmentTiming.run a registered s.core clocks) (by simpa only [full] using prefixMatches))
    have loadedAt : LoadedGuard g actual.core := by
      rw [actualCore]
      exact loaded.same_word traced.cut.pose.current
    have live := guard_by_stretch_bound registered host target s bound valid enough liveRelease ordinary g
      clockMask clockHigh loadedAt
    rw [← actualCore, loadedAt.qualifies]
    rwa [loadedAt.qualifies] at live

end Pinwheel.Hardware.StreamingReady.SegmentCausalI2C
