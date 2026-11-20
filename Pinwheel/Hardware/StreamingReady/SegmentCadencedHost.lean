import Pinwheel.Hardware.StreamingReady.SegmentHostService
import Pinwheel.Hardware.StreamingReady.SegmentCausal

/-! A core-port host policy. It drains RX continuously and offers the next
    TX chunk only after a sustained public TX wait. The cooldown leaves
    the wire engine's timed apertures free of TX offers. -/
namespace Pinwheel.Hardware.StreamingReady.SegmentCadencedHost

open Pinwheel.Hardware SegmentCore SegmentPathControl
open ProtocolOwnership (DrainInput)

structure Chunk where
  data : BitVec 32
  sizeMinusOne : Fin 32

def Chunk.size (chunk : Chunk) : BitVec 6 := BitVec.ofNat 6 (chunk.sizeMinusOne.val + 1)

structure Policy where
  cooldown : Nat
  chunkAt : Nat → Option Chunk

def nextAge (age : Nat) (waiting : Bool) : Nat := if waiting then age + 1 else 0

def ageAfter (age : Nat) (waiting : List Bool) : Nat := waiting.foldl nextAge age

def offer (policy : Policy) (age : Nat) (status : Values Core.Output) : Option Chunk :=
  if status .waitingTX = 1#1 ∧ policy.cooldown ≤ age then
    policy.chunkAt (status .txAccepted).toNat
  else none

/-- The host consumes only normal core status, with both tags copied from
    the same pre-edge observation. The peer owns the raw pins. -/
def input (policy : Policy) (age : Nat) (status : Values Core.Output) : Values Core.Input :=
  let next := offer policy age status
  fun port => match port with
    | .expectedGeneration => status .generation
    | .expectedTransfer => status .transfer
    | .txPush => BitVec.ofBool next.isSome
    | .txData => (next.map Chunk.data).getD 0
    | .txBits => (next.map Chunk.size).getD 0
    | .rxPop => 1
    | _ => 0

theorem ordinary (policy : Policy) (age : Nat) (status : Values Core.Output) :
    NoReset (input policy age status) := by
  constructor
  · rfl
  · change (0#4 : BitVec 4) ≠ 15#4
    decide

theorem input_drains (policy : Policy) (age : Nat) (status : Values Core.Output)
    (quiet : offer policy age status = none) : DrainInput (input policy age status) := by
  exact ⟨rfl, rfl, by simp only [input, quiet, Option.isSome_none]; rfl⟩

theorem no_offer_without_wait (policy : Policy) (age : Nat) (status : Values Core.Output)
    (clear : status .waitingTX = 0#1) : offer policy age status = none := by simp [offer, clear]

theorem age_le (age : Nat) (waiting : List Bool) : ageAfter age waiting ≤ age + waiting.length := by
  induction waiting generalizing age with
  | nil => simp [ageAfter]
  | cons w tail ih =>
    have first : nextAge age w ≤ age + 1 := by cases w <;> simp [nextAge]
    have later := ih (nextAge age w)
    simp only [ageAfter, List.foldl_cons, List.length_cons] at later ⊢
    omega

/-- One clear TX wait sample resets the host timer. All remaining clocks
    within the cooldown can drain RX and cannot carry a new TX offer. -/
theorem after_credit_drains (policy : Policy) (age : Nat) (waiting : List Bool) (status : Values Core.Output)
    (elapsed : waiting.length < policy.cooldown) :
    DrainInput (input policy (ageAfter age (false :: waiting)) status) := by
  apply input_drains
  have bound : ageAfter age (false :: waiting) ≤ waiting.length := by
    simpa only [ageAfter, List.foldl_cons, nextAge, Bool.false_eq_true, if_false, Nat.zero_add] using age_le 0 waiting
  have below : ¬ policy.cooldown ≤ ageAfter age (false :: waiting) := by omega
  simp [offer, below]

theorem sustained_wait (age : Nat) (clocks : Nat) :
    ageAfter age (List.replicate clocks true) = age + clocks := by
  induction clocks generalizing age with
  | zero => simp [ageAfter]
  | succ clocks ih =>
    simp only [ageAfter, List.replicate_succ, List.foldl_cons, nextAge, if_true] at ih ⊢
    rw [ih]
    omega

/-- Given a next chunk, a sustained wait reaches the offer edge after at
    most the configured cooldown. The chunk selection uses accepted offset. -/
theorem offer_after_wait (policy : Policy) (age : Nat) (status : Values Core.Output)
    (waiting : status .waitingTX = 1#1) :
    offer policy (ageAfter age (List.replicate policy.cooldown true)) status =
      policy.chunkAt (status .txAccepted).toNat := by
  simp [offer, sustained_wait, waiting]

def host (policy : Policy) : SegmentCausal.Host Nat where
  input := input policy
  next age ports := nextAge age (ports .waitingTX == 1#1)

theorem runtime (policy : Policy) : (host policy).Runtime := ordinary policy

theorem causal_input_drains (policy : Policy) (registered : Bool) (peer : SegmentCausal.Peer P)
    (s : SegmentCausal.State a Nat P) (quiet : offer policy s.host (SegmentCausal.status registered s) = none) :
    DrainInput (SegmentCausal.input registered (host policy) peer s) :=
  input_drains policy s.host (SegmentCausal.status registered s) quiet

/-- Credit and non-reservation phases have a clear public TX wait flag.
    The policy makes no offer and resets its cooldown there. -/
theorem cleardown (policy : Policy) (registered : Bool) (peer : SegmentCausal.Peer P)
    (s : SegmentCausal.State a Nat P) (clear : SegmentCausal.status registered s .waitingTX = 0#1) :
    DrainInput (SegmentCausal.input registered (host policy) peer s) ∧
      (SegmentCausal.step registered (host policy) peer s).host = 0 := by
  exact ⟨causal_input_drains policy registered peer s
    (no_offer_without_wait policy s.host (SegmentCausal.status registered s) clear),
    by simp [SegmentCausal.step, host, nextAge, clear]⟩

theorem waiting_clear_outside_boundary (registered : Bool) (s : SegmentCausal.State a H P)
    (outside : s.core (.base .phase) ≠ 2#3) : SegmentCausal.status registered s .waitingTX = 0#1 := by
  change (bindWord (word registered) (output .waitingTX)).eval SegmentCausal.quiet s.core = 0#1
  rw [bindWord_eval]
  simp [output, lift, Expr.eval_bind, Core.output, Core.both, Core.isPhase, Expr.eval, withFetch, outside]

theorem wait_age_step_le (policy : Policy) (registered : Bool) (peer : SegmentCausal.Peer P)
    (s : SegmentCausal.State a Nat P) : (SegmentCausal.step registered (host policy) peer s).host ≤ s.host + 1 := by
  change nextAge s.host (SegmentCausal.status registered s .waitingTX == 1#1) ≤ _
  simp only [nextAge]
  split <;> omega

/-- Any clock interval shorter than the remaining cooldown is TX-quiet,
    irrespective of the peer or of later queue status. -/
theorem quiet_clocks (policy : Policy) (registered : Bool) (peer : SegmentCausal.Peer P)
    (s : SegmentCausal.State a Nat P) (n : Nat) (room : s.host + n ≤ policy.cooldown) :
    ∀ i ∈ SegmentCausal.clocks registered (host policy) peer s n, DrainInput i := by
  induction n generalizing s with
  | zero => simp [SegmentCausal.clocks]
  | succ n ih =>
    intro i member
    rcases List.mem_cons.mp member with first | tail
    · subst i
      apply causal_input_drains
      have below : ¬ policy.cooldown ≤ s.host := by omega
      simp [offer, below]
    · apply ih _ _ i tail
      have advanced := wait_age_step_le policy registered peer s
      omega

theorem all_drains (policy : Policy) (empty : ∀ offset, policy.chunkAt offset = none)
    (registered : Bool) (peer : SegmentCausal.Peer P) (s : SegmentCausal.State a Nat P) (clocks : Nat) :
    ∀ i ∈ SegmentCausal.clocks registered (host policy) peer s clocks, DrainInput i := by
  induction clocks generalizing s with
  | zero => simp [SegmentCausal.clocks]
  | succ n ih =>
    intro i member
    rcases List.mem_cons.mp member with first | rest
    · subst i
      apply causal_input_drains
      simp [offer, empty]
    · exact ih _ i rest

/-- The cleared edge itself is ordinary, then the following clocks use
    the reset cooldown. -/
theorem clear_prefix_drains (policy : Policy) (registered : Bool) (peer : SegmentCausal.Peer P)
    (s : SegmentCausal.State a Nat P) (clear : SegmentCausal.status registered s .waitingTX = 0#1)
    (length keep : Nat) (within : keep ≤ length) (quiet : keep ≤ policy.cooldown + 1) :
    ∀ i ∈ (SegmentCausal.clocks registered (host policy) peer s length).take keep, DrainInput i := by
  rw [SegmentCausal.clocks_take _ _ _ _ _ _ within]
  cases keep with
  | zero => simp [SegmentCausal.clocks]
  | succ n =>
    obtain ⟨first, reset⟩ := cleardown policy registered peer s clear
    intro i member
    rcases List.mem_cons.mp member with same | later
    · subst i
      exact first
    · apply quiet_clocks policy registered peer _ n _ i later
      omega

end Pinwheel.Hardware.StreamingReady.SegmentCadencedHost
