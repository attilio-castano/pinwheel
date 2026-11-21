import Pinwheel.Hardware.Memory.ByteAccess
import Pinwheel.Hardware.Memory.SinglePort
import Pinwheel.Hardware.Stream.Machine

/-! One-outstanding byte transaction on an exclusively owned 32-bit word RAM.
A valid request samples the addressed word into the existing RAM Q register.
The pending request retains its metadata, including a store's input operand;
there is no second response or old-word snapshot register. A store commits only
on response acceptance. Faults issue no memory access. Reset cancels pending
work while preserving all words and Q. This is a RAM contract, not MMIO.
-/
namespace Pinwheel.Hardware.Memory.ByteAdapterModel

open ByteAccess

inductive Request (a : Nat) where
  | read (signed : Bool) (size : BitVec 2) (address : BitVec a) (offset : Offset)
  | store (size : BitVec 2) (address : BitVec a) (offset : Offset) (data : Word)
  deriving DecidableEq, Repr

def Request.size : Request a → BitVec 2
  | .read _ size _ _ | .store size _ _ _ => size

def Request.address : Request a → BitVec a
  | .read _ _ address _ | .store _ address _ _ => address

def Request.offset : Request a → Offset
  | .read _ _ _ offset | .store _ _ offset _ => offset

def Request.check (request : Request a) : Except Fault Size :=
  ByteAccess.access request.size request.offset

inductive Response where
  | read (data : Word)
  | stored
  | fault (error : Fault)
  deriving DecidableEq, Repr

def Request.response (request : Request a) (q : Word) : Response :=
  match request.check with
  | .error error => .fault error
  | .ok size => match request with
    | .read signed _ _ offset => .read (loadCore size signed offset q)
    | .store _ _ _ _ => .stored

def Request.beginCommand (request : Request a) : SinglePort.Command a 32 :=
  match request.check with
  | .error _ => .idle
  | .ok _ => .read request.address

def Request.write (request : Request a) (q : Word) : Option (BitVec a × Word) :=
  match request.check with
  | .error _ => none
  | .ok size => match request with
    | .read _ _ _ _ => none
    | .store _ address offset data => some (address, storeCore size offset q data)

def Request.finishCommand (request : Request a) (q : Word) : SinglePort.Command a 32 :=
  match request.write q with
  | none => .idle
  | some (address, data) => .write address data

structure State (a : Nat) where
  memory : Sram.State a 32
  pending : Option (Request a)

abbrev Input (a : Nat) := Hardware.Stream.Input (Request a)
abbrev Output := Hardware.Stream.Output Response

def ready (s : State a) : Bool := s.pending.isNone
def offer (s : State a) : Option Response := s.pending.map (fun r => r.response s.memory.q)

def command (i : Input a) (s : State a) : SinglePort.Command a 32 :=
  if i.reset then .idle else
  match s.pending with
  | none => (i.offered.map Request.beginCommand).getD .idle
  | some request => if i.ready then request.finishCommand s.memory.q else .idle

def step (i : Input a) (s : State a) : State a :=
  ⟨SinglePort.step s.memory (command i s),
    if i.reset then none else match s.pending with
      | none => i.offered
      | some request => if i.ready then none else some request⟩

def machine (a : Nat) : Hardware.Stream.Machine (Request a) Response (State a) :=
  ⟨fun _ s => ready s, offer, step⟩

def component (a : Nat) : Timed.Component (Input a) (State a) Output := (machine a).component

def acceptedRequests (i : Input a) (s : State a) : List (Request a) :=
  Hardware.Stream.accepted i ((component a).observe i s)

def completedRequests (i : Input a) (s : State a) : List (Request a) :=
  if i.reset || !i.ready then [] else s.pending.toList

def emittedResponses (i : Input a) (s : State a) : List Response :=
  Hardware.Stream.emitted i ((component a).observe i s)

def pendingResponses (s : State a) : List Response := (offer s).toList

def acceptedResponses (i : Input a) (s : State a) : List Response :=
  (acceptedRequests i s).map (fun r => r.response (s.memory.contents r.address))

def committedWrites (i : Input a) (s : State a) : List (BitVec a × Word) :=
  (completedRequests i s).filterMap (fun r => r.write s.memory.q)

/-- Exclusive ownership keeps Q equal to the still-unmodified addressed word
until a valid pending transaction completes or is canceled. A fabricated
pending state need not satisfy this invariant. -/
def Valid (s : State a) : Prop :=
  ∀ request size, s.pending = some request → request.check = .ok size →
    s.memory.q = s.memory.contents request.address

def resetState (s : State a) : State a := ⟨s.memory, none⟩

theorem reset_state (i : Input a) (s : State a) (h : i.reset = true) :
    step i s = resetState s := by
  simp [step, command, h, resetState, SinglePort.step]

theorem reset_observe (i : Input a) (s : State a) (h : i.reset = true) :
    (component a).observe i s = ⟨false, none⟩ := by
  simp [component, machine, Hardware.Stream.Machine.component, h]

theorem reset_events (i : Input a) (s : State a) (h : i.reset = true) :
    acceptedRequests i s = [] ∧ completedRequests i s = [] ∧
      emittedResponses i s = [] ∧ committedWrites i s = [] := by
  simp [acceptedRequests, completedRequests, emittedResponses, committedWrites,
    Hardware.Stream.accepted, Hardware.Stream.emitted, h]

theorem stalled_holds (i : Input a) (s : State a) (request : Request a)
    (hr : i.reset = false) (hd : i.ready = false) (hp : s.pending = some request) :
    step i s = s := by
  simp [step, command, hr, hd, hp, SinglePort.step]
  rw [← hp]

theorem stalled_response (i : Input a) (s : State a) (request : Request a)
    (hr : i.reset = false) (hd : i.ready = false) (hp : s.pending = some request) :
    offer (step i s) = offer s := by
  rw [stalled_holds i s request hr hd hp]

theorem completion (i : Input a) (s : State a) (request : Request a)
    (hr : i.reset = false) (hd : i.ready = true) (hp : s.pending = some request) :
    completedRequests i s = [request] ∧ emittedResponses i s = [request.response s.memory.q] ∧
      (step i s).pending = none ∧ acceptedRequests i s = [] := by
  simp [completedRequests, emittedResponses, acceptedRequests, Hardware.Stream.accepted,
    Hardware.Stream.emitted, component, machine, Hardware.Stream.Machine.component,
    ready, offer, step, hr, hd, hp]

theorem request_balance (i : Input a) (s : State a) (hr : i.reset = false) :
    s.pending.toList ++ acceptedRequests i s = completedRequests i s ++ (step i s).pending.toList := by
  cases hp : s.pending <;> cases ho : i.offered <;> cases hd : i.ready <;>
    simp [acceptedRequests, completedRequests, Hardware.Stream.accepted, component, machine,
      Hardware.Stream.Machine.component, ready, step, hr, hp, ho, hd]

theorem emitted_eq_completed (i : Input a) (s : State a) :
    emittedResponses i s = (completedRequests i s).map (fun r => r.response s.memory.q) := by
  cases hr : i.reset <;> cases hd : i.ready <;> cases hp : s.pending <;>
    simp [emittedResponses, completedRequests, Hardware.Stream.emitted, component, machine,
      Hardware.Stream.Machine.component, offer, hr, hd, hp]

theorem Request.begin_contents (request : Request a) (memory : Sram.State a 32) :
    (SinglePort.step memory request.beginCommand).contents = memory.contents := by
  cases hc : request.check <;> simp [Request.beginCommand, hc, SinglePort.step, Sram.State.step]

theorem Request.begin_q (request : Request a) (memory : Sram.State a 32) (size : Size)
    (h : request.check = .ok size) :
    (SinglePort.step memory request.beginCommand).q = memory.contents request.address := by
  simp [Request.beginCommand, h, SinglePort.step, Sram.State.step]

theorem Request.begin_response (request : Request a) (memory : Sram.State a 32) :
    request.response (SinglePort.step memory request.beginCommand).q =
      request.response (memory.contents request.address) := by
  cases hc : request.check <;>
    simp [Request.response, Request.beginCommand, hc, SinglePort.step, Sram.State.step]

theorem acceptance (i : Input a) (s : State a) (request : Request a)
    (hr : i.reset = false) (hp : s.pending = none) (ho : i.offered = some request) :
    step i s = ⟨SinglePort.step s.memory request.beginCommand, some request⟩ ∧
      acceptedRequests i s = [request] ∧ emittedResponses i s = [] := by
  simp [step, command, acceptedRequests, emittedResponses, Hardware.Stream.accepted,
    Hardware.Stream.emitted, component, machine, Hardware.Stream.Machine.component,
    ready, offer, hr, hp, ho]

theorem acceptance_samples (i : Input a) (s : State a) (request : Request a) (size : Size)
    (hr : i.reset = false) (hp : s.pending = none) (ho : i.offered = some request)
    (hc : request.check = .ok size) :
    (step i s).memory.contents = s.memory.contents ∧
      (step i s).memory.q = s.memory.contents request.address ∧
      offer (step i s) = some (request.response (s.memory.contents request.address)) := by
  rw [(acceptance i s request hr hp ho).1]
  simp [Request.begin_contents, Request.begin_q request s.memory size hc, offer]

theorem fault_acceptance (i : Input a) (s : State a) (request : Request a) (error : Fault)
    (hr : i.reset = false) (hp : s.pending = none) (ho : i.offered = some request)
    (hc : request.check = .error error) :
    command i s = .idle ∧ step i s = ⟨s.memory, some request⟩ ∧
      offer (step i s) = some (.fault error) := by
  simp [command, step, hr, hp, ho, Request.beginCommand, hc, SinglePort.step, offer, Request.response]

theorem fault_pending_no_access (i : Input a) (s : State a) (request : Request a) (error : Fault)
    (hp : s.pending = some request) (hc : request.check = .error error) : command i s = .idle := by
  simp [command, hp, Request.finishCommand, Request.write, hc]

theorem read_completion_no_access (i : Input a) (s : State a)
    (hp : s.pending = some (.read signed raw address offset)) : command i s = .idle := by
  cases hc : (Request.read signed raw address offset).check <;>
    simp [command, hp, Request.finishCommand, Request.write, hc]

/-- An idle edge never writes, even when it accepts a valid store. -/
theorem idle_preserves_contents (i : Input a) (s : State a) (hp : s.pending = none) :
    (step i s).memory.contents = s.memory.contents := by
  cases hr : i.reset <;> cases ho : i.offered <;>
    simp [step, command, hr, hp, ho, SinglePort.idle_holds, Request.begin_contents]

theorem reset_valid (s : State a) : Valid (resetState s) := by
  simp [Valid, resetState]

theorem valid_preserved (i : Input a) (s : State a) (h : Valid s) : Valid (step i s) := by
  cases hr : i.reset
  · cases hp : s.pending with
    | none =>
      cases ho : i.offered with
      | none => simp [Valid, step, hr, hp, ho]
      | some request =>
        rw [(acceptance i s request hr hp ho).1]
        intro r size heq hc
        have heq' : request = r := Option.some.inj heq
        subst r
        rw [Request.begin_contents]
        exact Request.begin_q request s.memory size hc
    | some request =>
      cases hd : i.ready
      · rw [stalled_holds i s request hr hd hp]
        exact h
      · simp [Valid, step, hr, hp, hd]
  · rw [reset_state i s hr]
    exact reset_valid s

theorem response_balance (i : Input a) (s : State a) (hr : i.reset = false) :
    pendingResponses s ++ acceptedResponses i s = emittedResponses i s ++ pendingResponses (step i s) := by
  cases hp : s.pending <;> cases ho : i.offered <;> cases hd : i.ready <;>
    simp [pendingResponses, acceptedResponses, emittedResponses, acceptedRequests,
      Hardware.Stream.accepted, Hardware.Stream.emitted, component, machine,
      Hardware.Stream.Machine.component, ready, offer, step, command, hr, hp, ho, hd,
      SinglePort.idle_holds, Request.begin_response]

theorem Request.finish_contents (request : Request a) (memory : Sram.State a 32) :
    (SinglePort.step memory (request.finishCommand memory.q)).contents =
      (request.write memory.q).toList.foldl
        (fun contents write => contents.write ⟨true, write.1, write.2⟩) memory.contents := by
  cases hw : request.write memory.q <;>
    simp [Request.finishCommand, hw, SinglePort.step, Sram.State.step]

theorem contents_step (i : Input a) (s : State a) :
    (step i s).memory.contents = (committedWrites i s).foldl
      (fun contents write => contents.write ⟨true, write.1, write.2⟩) s.memory.contents := by
  cases hr : i.reset <;> cases hp : s.pending <;> cases hd : i.ready <;> cases ho : i.offered
  all_goals simp [step, command, committedWrites, completedRequests, hr, hp, hd, ho,
    SinglePort.idle_holds, Request.begin_contents, Request.finish_contents, List.filterMap_cons]
  all_goals split <;> simp_all

theorem store_command (i : Input a) (s : State a) (raw : BitVec 2) (address : BitVec a)
    (offset : Offset) (data : Word) (size : Size)
    (hr : i.reset = false) (hd : i.ready = true)
    (hp : s.pending = some (.store raw address offset data))
    (hc : ByteAccess.access raw offset = .ok size) :
    command i s = .write address (storeCore size offset s.memory.q data) := by
  simp [command, hr, hd, hp, Request.finishCommand, Request.write, Request.check,
    Request.size, Request.offset, hc]

/-- A write event is the very same edge as acceptance of the store response.
Blocked or merely offered acknowledgements cannot commit. -/
theorem store_completion (i : Input a) (s : State a) (raw : BitVec 2) (address : BitVec a)
    (offset : Offset) (data : Word) (size : Size)
    (hr : i.reset = false) (hd : i.ready = true)
    (hp : s.pending = some (.store raw address offset data))
    (hc : ByteAccess.access raw offset = .ok size) :
    emittedResponses i s = [.stored] ∧
      committedWrites i s = [(address, storeCore size offset s.memory.q data)] ∧
      (step i s).pending = none ∧ (step i s).memory.q = s.memory.q := by
  simp [emitted_eq_completed, committedWrites, completedRequests, hr, hd, hp,
    Request.response, Request.write, Request.check, Request.size, Request.offset, hc,
    step, store_command i s raw address offset data size hr hd hp hc, SinglePort.write_holds_q]

theorem store_word_result (i : Input a) (s : State a) (raw : BitVec 2) (address : BitVec a)
    (offset : Offset) (data : Word) (size : Size)
    (hr : i.reset = false) (hd : i.ready = true)
    (hp : s.pending = some (.store raw address offset data))
    (hc : ByteAccess.access raw offset = .ok size) :
    (step i s).memory.contents address = storeCore size offset s.memory.q data := by
  simp [step, store_command i s raw address offset data size hr hd hp hc,
    SinglePort.step, Sram.State.step]
  exact write_same _ _ rfl

theorem store_other_word (i : Input a) (s : State a) (raw : BitVec 2) (address other : BitVec a)
    (offset : Offset) (data : Word) (size : Size)
    (hr : i.reset = false) (hd : i.ready = true)
    (hp : s.pending = some (.store raw address offset data))
    (hc : ByteAccess.access raw offset = .ok size) (different : address ≠ other) :
    (step i s).memory.contents other = s.memory.contents other := by
  simp [step, store_command i s raw address offset data size hr hd hp hc,
    SinglePort.step, Sram.State.step, write_other, different]

/-- Byte preservation refers to the actual current RAM word, so it requires
the exclusive-ownership/Q invariant rather than an arbitrary fabricated Q. -/
theorem store_byte_result (i : Input a) (s : State a) (hs : Valid s)
    (raw : BitVec 2) (address : BitVec a) (offset lane : Offset) (data : Word) (size : Size)
    (hr : i.reset = false) (hd : i.ready = true)
    (hp : s.pending = some (.store raw address offset data))
    (hc : ByteAccess.access raw offset = .ok size) :
    byte ((step i s).memory.contents address) lane =
      if Touched size offset lane then byte data (lane - offset) else byte (s.memory.contents address) lane := by
  rw [store_word_result i s raw address offset data size hr hd hp hc]
  have hq := hs (.store raw address offset data) size hp hc
  simp only [Request.address] at hq
  simp [storeCore, hq]

theorem store_readback (i : Input a) (s : State a)
    (raw : BitVec 2) (address : BitVec a) (offset : Offset) (data : Word) (size : Size) (signed : Bool)
    (hr : i.reset = false) (hd : i.ready = true)
    (hp : s.pending = some (.store raw address offset data))
    (hc : ByteAccess.access raw offset = .ok size) :
    ByteAccess.load raw signed offset ((step i s).memory.contents address) =
      .ok (loadCore size signed 0 data) := by
  rw [store_word_result i s raw address offset data size hr hd hp hc]
  simp [ByteAccess.load, hc, storeCore_readback size signed offset s.memory.q data
    ((access_ok_iff raw offset size).mp hc).2]

/-- Once a response retires, any next edge can only be idle or sample a new
request. It cannot repeat the completed store, even if readiness stays high. -/
theorem no_repeat (i next : Input a) (s : State a) (request : Request a)
    (hr : i.reset = false) (hd : i.ready = true) (hp : s.pending = some request) :
    (step next (step i s)).memory.contents = (step i s).memory.contents :=
  idle_preserves_contents next (step i s) (completion i s request hr hd hp).2.2.1

theorem no_stale_after_reset (i next : Input a) (s : State a) (hr : i.reset = true) :
    (step next (step i s)).memory.contents = s.memory.contents := by
  rw [reset_state i s hr, idle_preserves_contents next (resetState s) rfl]
  rfl

theorem pending_bound (s : State a) : (pendingResponses s).length ≤ 1 := by
  cases hp : s.pending <;> simp [pendingResponses, offer, hp]

theorem reset_empty (i : Input a) (s : State a) (hr : i.reset = true) :
    (step i s).pending = none ∧ pendingResponses (step i s) = [] := by
  rw [reset_state i s hr]
  simp [resetState, pendingResponses, offer]

/-- Ordered request identities and acceptance-time response snapshots are
recorded per reset epoch. No eventual-ready assumption is needed. -/
structure History (a : Nat) where
  requests : List (Request a) := []
  completed : List (Request a) := []
  snapshots : List Response := []
  responses : List Response := []

def History.advance (h : History a) (i : Input a) (s : State a) : History a :=
  if i.reset then {} else
  ⟨h.requests ++ acceptedRequests i s, h.completed ++ completedRequests i s,
    h.snapshots ++ acceptedResponses i s, h.responses ++ emittedResponses i s⟩

def runHistory : State a → History a → List (Input a) → State a × History a
  | s, h, [] => (s, h)
  | s, h, i :: rest => runHistory (step i s) (h.advance i s) rest

theorem history_balance (s : State a) (h : History a)
    (hreq : h.requests = h.completed ++ s.pending.toList)
    (hresp : h.snapshots = h.responses ++ pendingResponses s) (inputs : List (Input a)) :
    let result := runHistory s h inputs
    result.2.requests = result.2.completed ++ result.1.pending.toList ∧
      result.2.snapshots = result.2.responses ++ pendingResponses result.1 := by
  induction inputs generalizing s h with
  | nil => exact ⟨hreq, hresp⟩
  | cons i rest ih =>
    apply ih
    · cases hr : i.reset <;>
        simp [History.advance, hr, hreq, List.append_assoc, request_balance i s, reset_empty i s]
    · cases hr : i.reset <;>
        simp [History.advance, hr, hresp, List.append_assoc, response_balance i s, reset_empty i s]

theorem history_after_reset (i : Input a) (s : State a) (hr : i.reset = true)
    (inputs : List (Input a)) :
    let result := runHistory (step i s) {} inputs
    result.2.requests = result.2.completed ++ result.1.pending.toList ∧
      result.2.snapshots = result.2.responses ++ pendingResponses result.1 :=
  history_balance (step i s) {} (by simp [(reset_empty i s hr).1])
    (by simp [(reset_empty i s hr).2]) inputs

theorem idle_without_request (i : Input a) (s : State a)
    (hp : s.pending = none) (ho : i.offered = none) : step i s = s := by
  cases hr : i.reset <;> simp [step, command, hr, hp, ho, SinglePort.step] <;> rw [← hp]

theorem quiet_run (s : State a) (hp : s.pending = none) (inputs : List (Input a))
    (quiet : ∀ i ∈ inputs, i.offered = none) : (component a).run s inputs = s := by
  induction inputs generalizing s with
  | nil => rfl
  | cons i rest ih =>
    change (component a).run (step i s) rest = s
    rw [idle_without_request i s hp (quiet i (by simp))]
    exact ih s hp (fun j hj => quiet j (by simp [hj]))

theorem quiet_after_reset (i : Input a) (s : State a) (hr : i.reset = true)
    (inputs : List (Input a)) (quiet : ∀ j ∈ inputs, j.offered = none) :
    (component a).run (step i s) inputs = resetState s := by
  rw [reset_state i s hr]
  exact quiet_run (resetState s) rfl inputs quiet

theorem run_valid (s : State a) (hs : Valid s) (inputs : List (Input a)) :
    Valid ((component a).run s inputs) := by
  induction inputs generalizing s with
  | nil => exact hs
  | cons i rest ih => exact ih (step i s) (valid_preserved i s hs)

end Pinwheel.Hardware.Memory.ByteAdapterModel
