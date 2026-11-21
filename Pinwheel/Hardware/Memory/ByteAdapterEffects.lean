import Pinwheel.Hardware.Memory.ByteAdapterModel
import Pinwheel.Hardware.Timed.Events

/-! Architectural completion events for the exclusively owned pure RAM byte
adapter. The command-time read into Q is internal; the event occurs when the
response is accepted. This interpretation is unsuitable for MMIO. Reset drops
pending work without a completion event and never rolls back earlier stores.
All statements are finite-prefix safety, not an eventual-ready assumption.
-/
namespace Pinwheel.Hardware.Memory.ByteAdapterEffects

open ByteAccess ByteAdapterModel Timed

structure Event (a : Nat) where
  request : ByteAdapterModel.Request a
  response : ByteAdapterModel.Response
  deriving DecidableEq, Repr

/-- Every completion, including faults, appears exactly once. Its response is
the adapter's offered response on that acceptance edge. -/
def events (i : Input a) (s : ByteAdapterModel.State a) : List (Event a) :=
  (completedRequests i s).map (fun r => ⟨r, r.response s.memory.q⟩)

theorem events_responses (i : Input a) (s : ByteAdapterModel.State a) :
    (events i s).map Event.response = emittedResponses i s := by
  simp [events, emitted_eq_completed, List.map_map]

theorem events_requests (i : Input a) (s : ByteAdapterModel.State a) :
    (events i s).map Event.request = completedRequests i s := by
  simp [events, List.map_map, Function.comp_def]

def interpret (contents : Contents a 32) (event : Event a) : Option (Contents a 32) :=
  match event.request, event.response with
  | .read signed raw address offset, .read data =>
      match ByteAccess.load raw signed offset (contents address) with
      | .ok expected => if expected = data then some contents else none
      | .error _ => none
  | .store raw address offset data, .stored =>
      let result := ByteAccess.store raw offset (contents address) data
      if result.fault.isNone then some (contents.write ⟨true, address, result.word⟩) else none
  | request, .fault error =>
      match request.check with
      | .error expected => if expected = error then some contents else none
      | .ok _ => none
  | _, _ => none

def atomic (a : Nat) : EventSpec (Contents a 32) (Event a) :=
  ⟨fun before event after => interpret before event = some after⟩

theorem atomic_read_iff (before after : Contents a 32) (signed : Bool)
    (raw : BitVec 2) (address : BitVec a) (offset : Offset) (data : Word) :
    (atomic a).step before ⟨.read signed raw address offset, .read data⟩ after ↔
      ByteAccess.load raw signed offset (before address) = .ok data ∧ before = after := by
  cases h : ByteAccess.load raw signed offset (before address) with
  | error error => simp [atomic, interpret, h]
  | ok expected =>
    by_cases he : expected = data <;> simp [atomic, interpret, h, he]

theorem atomic_store_iff (before after : Contents a 32)
    (raw : BitVec 2) (address : BitVec a) (offset : Offset) (data : Word) :
    (atomic a).step before ⟨.store raw address offset data, .stored⟩ after ↔
      (ByteAccess.store raw offset (before address) data).fault = none ∧
        before.write ⟨true, address, (ByteAccess.store raw offset (before address) data).word⟩ = after := by
  cases h : (ByteAccess.store raw offset (before address) data).fault <;>
    simp [atomic, interpret, h]

theorem atomic_fault_iff (before after : Contents a 32)
    (request : ByteAdapterModel.Request a) (error : Fault) :
    (atomic a).step before ⟨request, .fault error⟩ after ↔
      request.check = .error error ∧ before = after := by
  cases request <;>
    simp only [atomic, interpret]
  all_goals split <;> rename_i hc
  all_goals simp [hc]
  all_goals split <;> simp_all

theorem interpret_response (request : ByteAdapterModel.Request a) (memory : Sram.State a 32)
    (snapshot : ∀ size, request.check = .ok size → memory.q = memory.contents request.address) :
    interpret memory.contents ⟨request, request.response memory.q⟩ =
      some (SinglePort.step memory (request.finishCommand memory.q)).contents := by
  cases request with
  | read signed raw address offset =>
    cases hc : ByteAccess.access raw offset <;>
      simp_all [interpret, ByteAdapterModel.Request.response, ByteAdapterModel.Request.check,
        ByteAdapterModel.Request.size, ByteAdapterModel.Request.offset, ByteAdapterModel.Request.address,
        ByteAdapterModel.Request.finishCommand, ByteAdapterModel.Request.write,
        ByteAccess.load, SinglePort.step]
  | store raw address offset data =>
    cases hc : ByteAccess.access raw offset <;>
      simp_all [interpret, ByteAdapterModel.Request.response, ByteAdapterModel.Request.check,
        ByteAdapterModel.Request.size, ByteAdapterModel.Request.offset, ByteAdapterModel.Request.address,
        ByteAdapterModel.Request.finishCommand, ByteAdapterModel.Request.write,
        ByteAccess.store, SinglePort.step, Sram.State.step]

/-- All actual full-word writes, in edge order, without clearing at reset. -/
def committedHistory (s : ByteAdapterModel.State a) (inputs : List (Input a)) :
    List (BitVec a × Word) := (ByteAdapterModel.component a).eventTrace committedWrites s inputs

def applyWrites (contents : Contents a 32) (writes : List (BitVec a × Word)) : Contents a 32 :=
  writes.foldl (fun c write => c.write ⟨true, write.1, write.2⟩) contents

theorem applyWrites_append (contents : Contents a 32) (first rest : List (BitVec a × Word)) :
    applyWrites contents (first ++ rest) = applyWrites (applyWrites contents first) rest := by
  simp [applyWrites, List.foldl_append]

/-- No validity, reset exclusion, or initialization premise is required for
the exact physical write fold. Snapshot validity is needed only to interpret
these full-word writes as byte-store completions below. -/
theorem contents_history (s : ByteAdapterModel.State a) (inputs : List (Input a)) :
    ((ByteAdapterModel.component a).run s inputs).memory.contents =
      applyWrites s.memory.contents (committedHistory s inputs) := by
  induction inputs generalizing s with
  | nil => rfl
  | cons i rest ih =>
    change ((ByteAdapterModel.component a).run (step i s) rest).memory.contents =
      applyWrites s.memory.contents (committedWrites i s ++ committedHistory (step i s) rest)
    rw [ih, applyWrites_append, contents_step]
    rfl

theorem edge_path (i : Input a) (s : ByteAdapterModel.State a) (hs : Valid s) :
    (atomic a).Path s.memory.contents (events i s) (step i s).memory.contents := by
  cases hr : i.reset
  · cases hp : s.pending with
    | none =>
      rw [idle_preserves_contents i s hp]
      simpa [events, completedRequests, hr, hp] using (EventSpec.Path.nil (spec := atomic a) s.memory.contents)
    | some request =>
      cases hd : i.ready
      · rw [stalled_holds i s request hr hd hp]
        simpa [events, completedRequests, hr, hd] using (EventSpec.Path.nil (spec := atomic a) s.memory.contents)
      · have hmem : (step i s).memory = SinglePort.step s.memory (request.finishCommand s.memory.q) := by
          simp [step, command, hr, hd, hp]
        have hevent := interpret_response request s.memory (fun size hc => hs request size hp hc)
        rw [← hmem] at hevent
        simpa [events, completedRequests, hr, hd, hp] using
          (EventSpec.Path.cons (spec := atomic a) hevent (EventSpec.Path.nil (step i s).memory.contents))
  · rw [reset_state i s hr]
    simpa [events, completedRequests, hr, resetState] using
      (EventSpec.Path.nil (spec := atomic a) s.memory.contents)

def refinement (a : Nat) : EventRefinement (ByteAdapterModel.component a) (atomic a) events
    (fun _ _ => True) where
  Rel s contents := Valid s ∧ s.memory.contents = contents
  edge := by
    intro i s contents ⟨hs, hc⟩ _
    subst contents
    exact ⟨(step i s).memory.contents, edge_path i s hs, valid_preserved i s hs, rfl⟩

/-- An empty adapter is admitted for every RAM contents function and every Q
value. This assumes no data initialization and excludes incoherent fabricated
pending transactions until reset establishes the snapshot invariant. -/
def initial (s : ByteAdapterModel.State a) : Prop := s.pending = none

theorem coverage (a : Nat) :
    (refinement a).InitialCoverage initial (fun _ => True) where
  nonempty := ⟨⟨⟨fun _ => 0, 0⟩, none⟩, rfl⟩
  covered s hs := ⟨s.memory.contents, trivial,
    by simp [refinement, Valid, show s.pending = none from hs]⟩

theorem every_memory_image (memory : Sram.State a 32) :
    initial ⟨memory, none⟩ ∧ (refinement a).Rel ⟨memory, none⟩ memory.contents := by
  simp [initial, refinement, Valid]

theorem all_legal (s : ByteAdapterModel.State a) (inputs : List (Input a)) :
    (ByteAdapterModel.component a).Legal (fun _ _ => True) s inputs := by
  induction inputs generalizing s with
  | nil => trivial
  | cons i rest ih => exact ⟨trivial, ih _⟩

theorem trace_path (s : ByteAdapterModel.State a) (hs : Valid s) (inputs : List (Input a)) :
    (atomic a).Path s.memory.contents ((ByteAdapterModel.component a).eventTrace events s inputs)
      ((ByteAdapterModel.component a).run s inputs).memory.contents := by
  obtain ⟨last, path, _, heq⟩ :=
    (refinement a).trace s s.memory.contents inputs ⟨hs, rfl⟩ (all_legal s inputs)
  exact heq ▸ path

theorem reset_events (i : Input a) (s : ByteAdapterModel.State a) (hr : i.reset = true) :
    events i s = [] ∧ (step i s).memory = s.memory := by
  simp [events, completedRequests, hr, reset_state i s hr, resetState]

theorem reset_trace (i : Input a) (s : ByteAdapterModel.State a) (hr : i.reset = true)
    (inputs : List (Input a)) :
    (atomic a).Path s.memory.contents
      ((ByteAdapterModel.component a).eventTrace events (step i s) inputs)
      ((ByteAdapterModel.component a).run (step i s) inputs).memory.contents := by
  simpa only [(reset_events i s hr).2] using
    trace_path (step i s) (by rw [reset_state i s hr]; exact reset_valid s) inputs

/-- Readiness is an explicit premise. No progress is asserted during a stall
or across cancellation by reset. Faults count as real completed responses. -/
theorem completion_event (i : Input a) (s : ByteAdapterModel.State a)
    (request : ByteAdapterModel.Request a) (hr : i.reset = false) (hd : i.ready = true)
    (hp : s.pending = some request) :
    events i s = [⟨request, request.response s.memory.q⟩] := by
  simp [events, completedRequests, hr, hd, hp]

def replay (contents : Contents a 32) : List (Event a) → Option (Contents a 32)
  | [] => some contents
  | event :: rest => (interpret contents event).bind (fun next => replay next rest)

theorem replay_of_path {first last : Contents a 32} {es : List (Event a)}
    (h : (atomic a).Path first es last) : replay first es = some last := by
  induction h with
  | nil => rfl
  | cons he _ ih => simpa [replay, show interpret _ _ = some _ from he] using ih

theorem replay_trace (s : ByteAdapterModel.State a) (hs : Valid s) (inputs : List (Input a)) :
    replay s.memory.contents ((ByteAdapterModel.component a).eventTrace events s inputs) =
      some ((ByteAdapterModel.component a).run s inputs).memory.contents :=
  replay_of_path (trace_path s hs inputs)

end Pinwheel.Hardware.Memory.ByteAdapterEffects
