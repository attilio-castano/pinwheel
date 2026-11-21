import Pinwheel.Hardware.StreamingReady.SegmentRawAperture
import Pinwheel.Hardware.StreamingReady.SegmentStore

/-! Connect a segmented core to two independent state machines. On each
    clock the pre-edge core drives determine the resolved digital inputs,
    and a separate host observes the pre-edge status ports. -/
namespace Pinwheel.Hardware.StreamingReady.SegmentCausal

open Pinwheel.Hardware SegmentCore SegmentPathControl
open Pinwheel.Program.StreamingReady (Guard Pins)
open SegmentRawAperture (LoadedGuard)

structure Host (H : Type) where
  input : H → Values Core.Output → Values Core.Input
  next : H → Values Core.Output → H

structure Peer (P : Type) where
  resolve : P → Pins → BitVec 2
  next : P → BitVec 2 → P

structure State (a : Nat) (H P : Type) where
  core : Values (Register a)
  host : H
  peer : P

def quiet : Values Core.Input := fun _ => 0

/-- Source for the host's pre-edge read of the status ports. Evaluating at
    idle command pins avoids feedback from the newly chosen offer. -/
def status (registered : Bool) (s : State a H P) : Values Core.Output :=
  (circuit a registered).observe quiet s.core

def pads (registered : Bool) (s : State a H P) : Pins :=
  ⟨status registered s .levels, status registered s .enabled⟩

def resolved (registered : Bool) (peer : Peer P) (s : State a H P) : BitVec 2 :=
  peer.resolve s.peer (pads registered s)

def withRaw (offer : Values Core.Input) (raw : BitVec 2) : Values Core.Input
  | _, .rawInputs => raw
  | _, port => offer port

/-- The peer owns the raw pins. The host's other inputs reach the core
    exactly as offered. -/
def input (registered : Bool) (host : Host H) (peer : Peer P) (s : State a H P) : Values Core.Input :=
  withRaw (host.input s.host (status registered s)) (resolved registered peer s)

@[simp] theorem input_init (registered : Bool) (host : Host H) (peer : Peer P) (s : State a H P) :
    input registered host peer s .initialize = host.input s.host (status registered s) .initialize := rfl

@[simp] theorem input_command (registered : Bool) (host : Host H) (peer : Peer P) (s : State a H P) :
    input registered host peer s .command = host.input s.host (status registered s) .command := rfl

@[simp] theorem input_push (registered : Bool) (host : Host H) (peer : Peer P) (s : State a H P) :
    input registered host peer s .txPush = host.input s.host (status registered s) .txPush := rfl

@[simp] theorem input_pop (registered : Bool) (host : Host H) (peer : Peer P) (s : State a H P) :
    input registered host peer s .rxPop = host.input s.host (status registered s) .rxPop := rfl

@[simp] theorem input_raw (registered : Bool) (host : Host H) (peer : Peer P) (s : State a H P) :
    input registered host peer s .rawInputs = resolved registered peer s := rfl

def step (registered : Bool) (host : Host H) (peer : Peer P) (s : State a H P) : State a H P :=
  ⟨(circuit a registered).step (input registered host peer s) s.core,
   host.next s.host (status registered s),
   peer.next s.peer (resolved registered peer s)⟩

def run (registered : Bool) (host : Host H) (peer : Peer P) (s : State a H P) : Nat → State a H P
  | 0 => s
  | n + 1 => run registered host peer (step registered host peer s) n

def clocks (registered : Bool) (host : Host H) (peer : Peer P) (s : State a H P) : Nat → List (Values Core.Input)
  | 0 => []
  | n + 1 => @input H P a registered host peer s :: clocks registered host peer (step registered host peer s) n

theorem clocks_length (registered : Bool) (host : Host H) (peer : Peer P) (s : State a H P) (n : Nat) :
    (clocks registered host peer s n).length = n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simp [clocks, ih]

theorem run_add (registered : Bool) (host : Host H) (peer : Peer P) (s : State a H P) (n m : Nat) :
    run registered host peer s (n + m) = run registered host peer (run registered host peer s n) m := by
  induction n generalizing s with
  | zero => simp only [Nat.zero_add, run]
  | succ n ih => simpa only [Nat.succ_add, run] using ih (step registered host peer s)

theorem clocks_append (registered : Bool) (host : Host H) (peer : Peer P) (s : State a H P) (n m : Nat) :
    clocks registered host peer s (n + m) =
      clocks registered host peer s n ++ clocks registered host peer (run registered host peer s n) m := by
  induction n generalizing s with
  | zero => simp only [Nat.zero_add, clocks, run, List.nil_append]
  | succ n ih => simp only [Nat.succ_add, clocks, run, List.cons_append, ih]

theorem clocks_split (registered : Bool) (host : Host H) (peer : Peer P) (s : State a H P)
    (n k : Nat) (within : k ≤ n) :
    clocks registered host peer s n =
      clocks registered host peer s k ++ clocks registered host peer (run registered host peer s k) (n - k) :=
  (congrArg (clocks registered host peer s) (show n = k + (n - k) by omega)).trans
    (clocks_append registered host peer s k (n - k))

theorem clocks_take (registered : Bool) (host : Host H) (peer : Peer P) (s : State a H P)
    (n k : Nat) (within : k ≤ n) :
    (clocks registered host peer s n).take k = clocks registered host peer s k := by
  rw [clocks_split registered host peer s n k within]
  exact List.take_left' (clocks_length registered host peer s k)

theorem clocks_drop (registered : Bool) (host : Host H) (peer : Peer P) (s : State a H P)
    (n k : Nat) (within : k ≤ n) :
    (clocks registered host peer s n).drop k = clocks registered host peer (run registered host peer s k) (n - k) := by
  rw [clocks_split registered host peer s n k within]
  exact List.drop_left' (clocks_length registered host peer s k)

theorem run_core (registered : Bool) (host : Host H) (peer : Peer P) (s : State a H P) (n : Nat) :
    @(run registered host peer s n).core = @SegmentTiming.run a registered s.core
      (clocks registered host peer s n) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => exact ih (step registered host peer s)

theorem clocks_at (registered : Bool) (host : Host H) (peer : Peer P) (s : State a H P)
    (n k : Nat) (within : k < n) :
    (clocks registered host peer s n)[k]? = some (@input H P a registered host peer (run registered host peer s k)) := by
  induction n generalizing s k with
  | zero => omega
  | succ n ih =>
    cases k with
    | zero => rfl
    | succ k => exact ih (step registered host peer s) k (Nat.lt_of_succ_lt_succ within)

def Host.Runtime (host : Host H) : Prop :=
  ∀ h (ports : Values Core.Output), NoReset (host.input h ports)

theorem input_ordinary (registered : Bool) (host : Host H) (peer : Peer P) (s : State a H P)
    (ordinary : host.Runtime) : NoReset (input registered host peer s) :=
  ordinary s.host (status registered s)

theorem clocks_ordinary (registered : Bool) (host : Host H) (peer : Peer P) (s : State a H P)
    (n : Nat) (ordinary : host.Runtime) : ∀ i ∈ clocks registered host peer s n, NoReset i := by
  induction n generalizing s with
  | zero => simp [clocks]
  | succ n ih =>
    intro i member
    rcases List.mem_cons.mp member with rfl | later
    · exact input_ordinary registered host peer s ordinary
    · exact ih (step registered host peer s) i later

/-- A physical sample at clock `n` is the sample available to the
    comparator immediately before clock `n + 2`. -/
theorem sample_after_two (registered : Bool) (host : Host H) (peer : Peer P) (s : State a H P)
    (n : Nat) (ordinary : host.Runtime) :
    (run registered host peer s (n + 2)).core (.base .stage2) =
      resolved registered peer (run registered host peer s n) := by
  rw [run_add]
  let seen := run registered host peer s n
  exact SegmentTrace.sampler_after_two registered (input registered host peer seen)
    (input registered host peer (step registered host peer seen)) seen.core
    (input_ordinary registered host peer seen ordinary)
    (input_ordinary registered host peer (step registered host peer seen) ordinary)

/-- The second sampler and loaded comparator consume the independently
    resolved peer sample. -/
theorem guard_after_two (registered : Bool) (host : Host H) (peer : Peer P) (s : State a H P)
    (n : Nat) (ordinary : host.Runtime) (guard : Guard)
    (loaded : LoadedGuard guard (run registered host peer s (n + 2)).core) :
    SegmentTiming.ready (input registered host peer (run registered host peer s (n + 2)))
        (run registered host peer s (n + 2)).core =
      BitVec.ofBool (guard.matches (resolved registered peer (run registered host peer s n))) := by
  rw [loaded.qualifies, sample_after_two registered host peer s n ordinary]

def Related (direct cached : State a H P) : Prop :=
  SegmentStore.Related direct.core cached.core ∧ direct.host = cached.host ∧ direct.peer = cached.peer

private theorem old_status_same (direct cached : State a H P) (same : Related direct cached) :
    @status a H P false direct = @status a H P true cached :=
  SegmentStore.observe quiet direct.core cached.core same.1

private theorem same_pads (direct cached : State a H P) (same : Related direct cached) :
    pads false direct = pads true cached := by
  unfold pads
  rw [old_status_same direct cached same]

theorem input_same (host : Host H) (peer : Peer P) (direct cached : State a H P) (same : Related direct cached) :
    @input H P a false host peer direct = @input H P a true host peer cached := by
  unfold input resolved
  rw [old_status_same direct cached same, same.2.1, same_pads direct cached same, same.2.2]

theorem step_same (host : Host H) (peer : Peer P) (direct cached : State a H P) (same : Related direct cached) :
    Related (step false host peer direct) (step true host peer cached) := by
  constructor
  · change SegmentStore.Related ((circuit a false).step (input false host peer direct) direct.core)
      ((circuit a true).step (input true host peer cached) cached.core)
    rw [input_same host peer direct cached same]
    exact SegmentStore.step _ _ _ same.1
  · simp only [step, resolved, same.2.1, same.2.2, old_status_same direct cached same,
      same_pads direct cached same, and_self]

/-- The two instruction stores generate the same causal input tape, while
    each independently reacts to its own host and peer state. -/
theorem run_same (host : Host H) (peer : Peer P) (direct cached : State a H P) (same : Related direct cached) (n : Nat) :
    Related (run false host peer direct n) (run true host peer cached n) ∧
      clocks false host peer direct n = clocks true host peer cached n := by
  induction n generalizing direct cached with
  | zero => exact ⟨same, rfl⟩
  | succ n ih =>
    obtain ⟨next, tape⟩ := ih (step false host peer direct) (step true host peer cached)
      (step_same host peer direct cached same)
    refine ⟨next, ?_⟩
    simp only [clocks, input_same host peer direct cached same, tape]

end Pinwheel.Hardware.StreamingReady.SegmentCausal
