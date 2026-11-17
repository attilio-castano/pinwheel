import Pinwheel.Hardware.Memory.SinglePort
import Pinwheel.Hardware.Stream.Machine

/-! One-outstanding-read adapter for the exclusive single-port memory contract.
The memory's Q register is the held response; the adapter adds only a pending
bit. Requests stall while a response is blocked, including writes. A response
may retire on the same edge that accepts a new read. Reset cancels handshakes
and pending responses, and preserves both the array and Q. No initial memory
contents, initial Q, eventual readiness, or fixed reset state are assumed.
-/
namespace Pinwheel.Hardware.Memory.StreamModel

inductive Request (a w : Nat) where
  | read (address : BitVec a)
  | write (address : BitVec a) (data : BitVec w)
  deriving DecidableEq, Repr

def Request.command : Request a w → SinglePort.Command a w
  | .read address => .read address
  | .write address data => .write address data

def Request.isRead : Request a w → Bool
  | .read _ => true
  | .write _ _ => false

/-- A read's response is the word at its acceptance edge, before the memory
transition. Writes produce no response. -/
def Request.response (contents : Contents a w) : Request a w → Option (BitVec w)
  | .read address => some (contents address)
  | .write _ _ => none

structure State (a w : Nat) where
  memory : Sram.State a w
  pending : Bool

abbrev Input (a w : Nat) := Hardware.Stream.Input (Request a w)
abbrev Output (w : Nat) := Hardware.Stream.Output (BitVec w)

def ready (downstream : Bool) (s : State a w) : Bool := !s.pending || downstream

def offer (s : State a w) : Option (BitVec w) := if s.pending then some s.memory.q else none

/-- Only an accepted request reaches memory. In particular, reset commands idle
instead of resetting or writing memory. -/
def command (i : Input a w) (s : State a w) : SinglePort.Command a w :=
  if i.reset then .idle
  else if ready i.ready s then (i.offered.map Request.command).getD .idle
  else .idle

def step (i : Input a w) (s : State a w) : State a w :=
  ⟨SinglePort.step s.memory (command i s),
    if i.reset then false
    else if ready i.ready s then i.offered.any Request.isRead
    else s.pending⟩

def machine (a w : Nat) : Hardware.Stream.Machine (Request a w) (BitVec w) (State a w) :=
  ⟨ready, offer, step⟩

def component (a w : Nat) : Timed.Component (Input a w) (State a w) (Output w) :=
  (machine a w).component

def acceptedRequests (i : Input a w) (s : State a w) : List (Request a w) :=
  Hardware.Stream.accepted i ((component a w).observe i s)

def emittedResponses (i : Input a w) (s : State a w) : List (BitVec w) :=
  Hardware.Stream.emitted i ((component a w).observe i s)

def acceptedReadValues (i : Input a w) (s : State a w) : List (BitVec w) :=
  (acceptedRequests i s).filterMap (Request.response s.memory.contents)

def pendingValues (s : State a w) : List (BitVec w) := (offer s).toList

/-- The memory executes exactly the accepted requests. Canceled or blocked
offers have no memory effect. -/
theorem memory_step (i : Input a w) (s : State a w) :
    (step i s).memory =
      (acceptedRequests i s).foldl (fun memory request => SinglePort.step memory request.command) s.memory := by
  cases hr : i.reset <;> cases hc : ready i.ready s <;> cases ho : i.offered <;>
    simp [step, command, acceptedRequests, Hardware.Stream.accepted, component, machine,
      Hardware.Stream.Machine.component, hr, hc, ho, SinglePort.step]

/-- The local conservation equation is state dependent: an accepted read adds
its pre-edge memory value, while an accepted write adds no response. -/
theorem balance (i : Input a w) (s : State a w) (hr : i.reset = false) :
    pendingValues s ++ acceptedReadValues i s =
      emittedResponses i s ++ pendingValues (step i s) := by
  cases hp : s.pending <;> cases hd : i.ready <;> cases ho : i.offered
  all_goals simp [pendingValues, acceptedReadValues, acceptedRequests, emittedResponses,
    Hardware.Stream.accepted, Hardware.Stream.emitted, component, machine,
    Hardware.Stream.Machine.component, ready, offer, step, command, SinglePort.step,
    hr, hp, hd, ho]
  all_goals rename_i request; cases request <;>
    simp [Request.response, Request.isRead, Request.command, Sram.State.step]

/-- Reset is a projection on protocol state, not memory initialization. -/
theorem reset_state (i : Input a w) (s : State a w) (hr : i.reset = true) :
    step i s = ⟨s.memory, false⟩ := by
  simp [step, command, hr, SinglePort.step]

theorem reset_observe (i : Input a w) (s : State a w) (hr : i.reset = true) :
    (component a w).observe i s = ⟨false, none⟩ := by
  simp [component, Hardware.Stream.Machine.component, hr]

theorem reset_events (i : Input a w) (s : State a w) (hr : i.reset = true) :
    acceptedRequests i s = [] ∧ emittedResponses i s = [] := by
  simp [acceptedRequests, emittedResponses, Hardware.Stream.accepted, Hardware.Stream.emitted, hr]

theorem reset_empty (i : Input a w) (s : State a w) (hr : i.reset = true) :
    pendingValues (step i s) = [] := by
  simp [reset_state i s hr, pendingValues, offer]

/-- A blocked response prevents every memory command, including writes, and
preserves the entire state. -/
theorem blocked_holds (i : Input a w) (s : State a w)
    (hr : i.reset = false) (hd : i.ready = false) (hp : s.pending = true) :
    step i s = s := by
  simp [step, command, ready, hr, hd, hp, SinglePort.step]
  rw [← hp]

theorem response_stable (i : Input a w) (s : State a w)
    (hr : i.reset = false) (hd : i.ready = false) (hp : s.pending = true) :
    offer (step i s) = offer s := by
  rw [blocked_holds i s hr hd hp]

/-- The sampled value is the memory word before the acceptance edge. This also
covers simultaneous retirement of the previous response and a new read. -/
theorem read_samples (i : Input a w) (s : State a w) (address : BitVec a)
    (hr : i.reset = false) (hc : ready i.ready s = true)
    (ho : i.offered = some (.read address)) :
    (step i s).memory.contents = s.memory.contents ∧
      (step i s).memory.q = s.memory.contents address ∧ (step i s).pending = true := by
  simp [step, command, hr, hc, ho, Request.command, Request.isRead,
    SinglePort.step, Sram.State.step]

theorem accepted_write (i : Input a w) (s : State a w) (address : BitVec a) (data : BitVec w)
    (hr : i.reset = false) (hc : ready i.ready s = true)
    (ho : i.offered = some (.write address data)) :
    (step i s).memory = SinglePort.step s.memory (.write address data) ∧
      (step i s).pending = false := by
  simp [step, command, hr, hc, ho, Request.command, Request.isRead]

theorem pending_bound (s : State a w) : (pendingValues s).length ≤ 1 := by
  cases hp : s.pending <;> simp [pendingValues, offer, hp]

/-- Accepted requests and read snapshots are recorded at their acceptance edge.
Reset starts a new transaction epoch; it does not discard memory contents. -/
structure History (a w : Nat) where
  requests : List (Request a w) := []
  reads : List (BitVec w) := []
  responses : List (BitVec w) := []

def History.advance (h : History a w) (i : Input a w) (s : State a w) : History a w :=
  if i.reset then ⟨[], [], []⟩
  else ⟨h.requests ++ acceptedRequests i s,
    h.reads ++ acceptedReadValues i s, h.responses ++ emittedResponses i s⟩

def runHistory : State a w → History a w → List (Input a w) → State a w × History a w
  | s, h, [] => (s, h)
  | s, h, i :: rest => runHistory (step i s) (h.advance i s) rest

/-- Every read snapshot in the current epoch is either delivered in order or
is the single held response. No downstream-progress assumption is required. -/
theorem history_balance (s : State a w) (h : History a w)
    (hh : h.reads = h.responses ++ pendingValues s) (inputs : List (Input a w)) :
    let result := runHistory s h inputs
    result.2.reads = result.2.responses ++ pendingValues result.1 := by
  induction inputs generalizing s h with
  | nil => exact hh
  | cons i rest ih =>
    apply ih
    cases hr : i.reset <;> simp [History.advance, hr, hh, List.append_assoc, balance i s,
      reset_empty i s]

/-- Any physical memory valuation may seed a new epoch after protocol reset.
The contents and Q used by subsequent commands remain those of `s.memory`. -/
theorem history_after_reset (i : Input a w) (s : State a w) (hr : i.reset = true)
    (inputs : List (Input a w)) :
    let result := runHistory (step i s) {} inputs
    result.2.reads = result.2.responses ++ pendingValues result.1 :=
  history_balance (step i s) {} (by simp [reset_empty i s hr]) inputs

end Pinwheel.Hardware.Memory.StreamModel
