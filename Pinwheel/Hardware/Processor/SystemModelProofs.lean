import Pinwheel.Hardware.Processor.SystemModel
import Pinwheel.Hardware.Memory.ByteAdapterEffects

/-! Ownership and provider correspondence for the closed processor model.
The ROM image is fixed explicitly. RAM words and Q may start arbitrarily;
reset cancels ownership without initializing memory. Autonomous MMIO events
remain visible on every edge, including edges without retirement. -/
namespace Pinwheel.Hardware.Processor.SystemModel


def FetchOwned (layout : AddressMap.Layout rw aw) (rom : Rom rw) (s : State aw) : Prop :=
  s.fetch = match s.core.phase with
    | .fetchResponse => some (fetchReply layout rom s.core.arch.pc)
    | _ => none

def RamOwned (layout : AddressMap.Layout rw aw) (rom : Rom rw) (s : State aw) : Prop :=
  match s.core.phase with
  | .dataResponse request => ∃ physical, plan layout rom request.intent = .ram physical ∧
      s.ram.pending = some physical
  | _ => s.ram.pending = none

structure Valid (layout : AddressMap.Layout rw aw) (rom : Rom rw) (s : State aw) : Prop where
  core : CoreModel.Valid s.core
  snapshot : Memory.ByteAdapterModel.Valid s.ram
  fetch : FetchOwned layout rom s
  ram : RamOwned layout rom s

theorem initial_valid (layout : AddressMap.Layout rw aw) (rom : Rom rw)
    (contents : BitVec aw → Word) (q : Word) : Valid layout rom (initial contents q) := by
  exact ⟨CoreModel.initial_valid, by simp [Memory.ByteAdapterModel.Valid, initial], rfl, rfl⟩

theorem reset_fetch (layout : AddressMap.Layout rw aw) (rom : Rom rw) (i : Input)
    (s : State aw) (h : i.reset = true) : (step layout rom i s).fetch = none := by
  simp [step, fetchStep, h]

theorem reset_valid (layout : AddressMap.Layout rw aw) (rom : Rom rw) (i : Input)
    (s : State aw) (h : i.reset = true) : Valid layout rom (step layout rom i s) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [reset_core _ _ _ _ h]; exact CoreModel.initial_valid
  · change Memory.ByteAdapterModel.Valid (Memory.ByteAdapterModel.step _ _)
    rw [Memory.ByteAdapterModel.reset_state _ _ h]
    exact Memory.ByteAdapterModel.reset_valid _
  · simp [FetchOwned, reset_core _ _ _ _ h, reset_fetch _ _ _ _ h, CoreModel.initial]
  · simp [RamOwned, reset_core _ _ _ _ h, (reset_ram _ _ _ _ h).2, CoreModel.initial]

theorem ownership_preserved (layout : AddressMap.Layout rw aw) (rom : Rom rw)
    (i : Input) (s : State aw) (hf : FetchOwned layout rom s) (hr : RamOwned layout rom s) :
    FetchOwned layout rom (step layout rom i s) ∧ RamOwned layout rom (step layout rom i s) := by
  by_cases reset : i.reset = true
  · exact ⟨(reset_valid _ _ _ _ reset).fetch, (reset_valid _ _ _ _ reset).ram⟩
  have reset' : i.reset = false := by simpa using reset
  rcases s with ⟨⟨arch, phase⟩, ram, mmio, fetch⟩
  cases phase <;> simp only [FetchOwned, RamOwned] at hf hr
  all_goals simp only [step, FetchOwned, RamOwned, CoreModel.step, CoreModel.tick,
    coreInput, ramInput, mmioInput, pendingPlan, Memory.ByteAdapterModel.step,
    fetchStep, reset', Bool.false_eq_true, if_false]
  all_goals try simp only [hf]
  case fetchRequest =>
    split <;> simp_all
  case fetchResponse =>
    cases fetchReply layout rom arch.pc <;> simp_all
  case execute word =>
    cases hs : RV32I.Semantics.step arch word <;> simp_all [CoreModel.acceptOutcome]
    rename_i pending
    cases pending <;> simp
  case dataRequest request =>
    cases hp : plan layout rom request.intent <;>
      simp_all [Memory.ByteAdapterModel.ready, CoreModel.acceptOutcome]
    case atomic reply =>
      cases request.finish reply <;> try simp
      rename_i pending
      cases pending <;> simp
    case mmio operation =>
      simp only [MmioModel.observe, Bool.false_eq_true, if_false, Option.map_some]
      cases request.finish (mmioReply (MmioModel.access i.gpio operation mmio).1) <;> try simp
      rename_i pending
      cases pending <;> simp
  case dataResponse request =>
    obtain ⟨physical, route, pending⟩ := hr
    simp only [Memory.ByteAdapterModel.offer, pending, Option.map_some]
    obtain ⟨c, a, terminal⟩ | ⟨c, w, reason, terminal⟩ :=
      CoreModel.data_finish_terminal request (ramReply (physical.response ram.memory.q))
    all_goals simp [terminal, CoreModel.acceptOutcome]
  case fence context =>
    simp_all [RV32I.Semantics.finish, CoreModel.acceptOutcome]
  case terminal fault => simp_all

theorem preserved (layout : AddressMap.Layout rw aw) (rom : Rom rw) (i : Input)
    (s : State aw) (h : Valid layout rom s) : Valid layout rom (step layout rom i s) := by
  have owners := ownership_preserved layout rom i s h.fetch h.ram
  exact ⟨CoreModel.preserved _ _ h.core, Memory.ByteAdapterModel.valid_preserved _ _ h.snapshot,
    owners.1, owners.2⟩

theorem run_valid (layout : AddressMap.Layout rw aw) (rom : Rom rw) (s : State aw)
    (inputs : List Input) (h : Valid layout rom s) :
    Valid layout rom ((component layout rom).run s inputs) := by
  induction inputs generalizing s with
  | nil => exact h
  | cons i rest ih => exact ih _ (preserved _ _ _ _ h)

theorem fetch_response (layout : AddressMap.Layout rw aw) (rom : Rom rw) (s : State aw)
    (h : Valid layout rom s) (phase : s.core.phase = .fetchResponse) :
    s.fetch = some (fetchReply layout rom s.core.arch.pc) := by
  simpa [FetchOwned, phase] using h.fetch

theorem ram_response (layout : AddressMap.Layout rw aw) (rom : Rom rw) (s : State aw)
    (h : Valid layout rom s) (request : CoreModel.DataRequest)
    (phase : s.core.phase = .dataResponse request) :
    ∃ physical, plan layout rom request.intent = .ram physical ∧ s.ram.pending = some physical ∧
      Memory.ByteAdapterModel.offer s.ram =
        some (physical.response (s.ram.memory.contents physical.address)) := by
  obtain ⟨physical, route, pending⟩ := (show ∃ physical,
    plan layout rom request.intent = .ram physical ∧ s.ram.pending = some physical from
      by simpa [RamOwned, phase] using h.ram)
  refine ⟨physical, route, pending, ?_⟩
  simp only [Memory.ByteAdapterModel.offer, pending, Option.map_some]
  cases check : physical.check with
  | error fault => simp [Memory.ByteAdapterModel.Request.response, check]
  | ok size => rw [h.snapshot physical size pending check]

theorem ram_plan_checked (layout : AddressMap.Layout rw aw) (rom : Rom rw)
    (intent : RV32I.Semantics.Intent) (physical : Memory.ByteAdapterModel.Request aw)
    (route : plan layout rom intent = .ram physical) :
    ∃ size, physical.check = .ok size := by
  cases intent with
  | fenceAll => simp [plan] at route
  | load address size signed =>
    simp only [plan] at route
    split at route
    · cases route
    · rename_i hit routed
      cases region : hit.region <;> simp only [region] at route
      all_goals try cases route
      refine ⟨size, ?_⟩
      apply Memory.ByteAccess.access_ok_iff _ _ _ |>.mpr
      exact ⟨by cases size <;> rfl, hit.byteAccess_aligned⟩
  | store address size data =>
    simp only [plan] at route
    split at route
    · cases route
    · rename_i hit routed
      cases region : hit.region <;> simp only [region] at route
      all_goals try cases route
      refine ⟨size, ?_⟩
      apply Memory.ByteAccess.access_ok_iff _ _ _ |>.mpr
      exact ⟨by cases size <;> rfl, hit.byteAccess_aligned⟩

/-- A completed RAM operation and the corresponding architectural completion
share one edge. The supplied response is calculated from the actual RAM word,
not an unconstrained environment reply. Stores and loads to x0 are included. -/
theorem ram_completion (layout : AddressMap.Layout rw aw) (rom : Rom rw)
    (i : Input) (s : State aw) (h : Valid layout rom s) (reset : i.reset = false)
    (request : CoreModel.DataRequest) (phase : s.core.phase = .dataResponse request) :
    ∃ physical, plan layout rom request.intent = .ram physical ∧
      Memory.ByteAdapterModel.completedRequests (ramInput layout rom i s) s.ram = [physical] ∧
      Memory.ByteAdapterEffects.events (ramInput layout rom i s) s.ram =
        [⟨physical, physical.response (s.ram.memory.contents physical.address)⟩] ∧
      ((step layout rom i s).core, (observe layout rom i s).core.event) =
        CoreModel.acceptOutcome s.core
          (.data .deferred request.intent (ramReply (physical.response (s.ram.memory.contents physical.address))))
          (request.finish (ramReply (physical.response (s.ram.memory.contents physical.address)))) := by
  obtain ⟨physical, route, pending, response⟩ := ram_response layout rom s h request phase
  refine ⟨physical, route, ?_, ?_, ?_⟩
  · simp [Memory.ByteAdapterModel.completedRequests, ramInput, reset, phase, pending]
  · have same : physical.response s.ram.memory.q =
        physical.response (s.ram.memory.contents physical.address) := by
      simpa [Memory.ByteAdapterModel.offer, pending] using response
    simp [Memory.ByteAdapterEffects.events, Memory.ByteAdapterModel.completedRequests,
      ramInput, reset, phase, pending, same]
  · simp [step, observe, CoreModel.observe, CoreModel.step, CoreModel.event, CoreModel.tick,
      coreInput, reset, phase, response]

/-- Atomic device effects use the same actual request and pre-edge response as
the core completion. Autonomous changes are then applied separately. -/
theorem mmio_completion (layout : AddressMap.Layout rw aw) (rom : Rom rw)
    (i : Input) (s : State aw) (reset : i.reset = false)
    (request : CoreModel.DataRequest) (physical : MmioModel.Request)
    (phase : s.core.phase = .dataRequest request)
    (route : plan layout rom request.intent = .mmio physical) :
    let response := (MmioModel.access i.gpio physical s.mmio).1
    ((step layout rom i s).core, (observe layout rom i s).core.event) =
      CoreModel.acceptOutcome s.core (.data .atomic request.intent (mmioReply response))
        (request.finish (mmioReply response)) ∧
    (step layout rom i s).mmio = MmioModel.autonomous (mmioInput layout rom i s) s.mmio
      (MmioModel.access i.gpio physical s.mmio).2 ∧
    MmioModel.events (mmioInput layout rom i s) s.mmio =
      .cpu physical i.gpio response :: MmioModel.autonomousEvents (mmioInput layout rom i s)
        s.mmio (MmioModel.access i.gpio physical s.mmio).2 := by
  simp [step, observe, CoreModel.observe, CoreModel.step, CoreModel.event, CoreModel.tick,
    coreInput, mmioInput, pendingPlan, reset, phase, route, MmioModel.observe,
    MmioModel.step, MmioModel.events, MmioModel.cpuState]

/-- Provider events preserve autonomous timer/serial changes even when the
core emits no retirement. Reset remains an explicit event in each projection. -/
structure Events (aw : Nat) where
  core : List CoreModel.Event
  ram : List (Memory.ByteAdapterEffects.Event aw)
  mmio : List MmioModel.Event

def events (layout : AddressMap.Layout rw aw) (rom : Rom rw) (i : Input) (s : State aw) : Events aw :=
  ⟨CoreModel.events (coreInput layout rom i s) s.core,
   Memory.ByteAdapterEffects.events (ramInput layout rom i s) s.ram,
   MmioModel.events (mmioInput layout rom i s) s.mmio⟩

theorem ram_edge_path (layout : AddressMap.Layout rw aw) (rom : Rom rw) (i : Input)
    (s : State aw) (h : Valid layout rom s) :
    (Memory.ByteAdapterEffects.atomic aw).Path s.ram.memory.contents
      (events layout rom i s).ram (step layout rom i s).ram.memory.contents :=
  Memory.ByteAdapterEffects.edge_path _ _ h.snapshot

theorem mmio_replay (layout : AddressMap.Layout rw aw) (rom : Rom rw) (i : Input) (s : State aw) :
    MmioModel.replay s.mmio (events layout rom i s).mmio = some (step layout rom i s).mmio :=
  MmioModel.replay_events _ _

def committedWrites (layout : AddressMap.Layout rw aw) (rom : Rom rw) (i : Input) (s : State aw) :=
  Memory.ByteAdapterModel.committedWrites (ramInput layout rom i s) s.ram

theorem ram_contents_history (layout : AddressMap.Layout rw aw) (rom : Rom rw)
    (s : State aw) (inputs : List Input) :
    ((component layout rom).run s inputs).ram.memory.contents =
      Memory.ByteAdapterEffects.applyWrites s.ram.memory.contents
        ((component layout rom).eventTrace (committedWrites layout rom) s inputs) := by
  induction inputs generalizing s with
  | nil => rfl
  | cons i rest ih =>
    change ((component layout rom).run (step layout rom i s) rest).ram.memory.contents =
      Memory.ByteAdapterEffects.applyWrites s.ram.memory.contents
        (committedWrites layout rom i s ++
          (component layout rom).eventTrace (committedWrites layout rom) (step layout rom i s) rest)
    rw [ih, Memory.ByteAdapterEffects.applyWrites_append]
    congr 1
    exact Memory.ByteAdapterModel.contents_step _ _

theorem core_edge_path (layout : AddressMap.Layout rw aw) (rom : Rom rw) (i : Input)
    (s : State aw) (h : Valid layout rom s) :
    CoreModel.architecture.Path (CoreModel.snapshot s.core) (events layout rom i s).core
      (CoreModel.snapshot (step layout rom i s).core) :=
  CoreModel.edge_path _ _ h.core

theorem core_trace_path (layout : AddressMap.Layout rw aw) (rom : Rom rw) (s : State aw)
    (inputs : List Input) (h : Valid layout rom s) :
    CoreModel.architecture.Path (CoreModel.snapshot s.core)
      ((component layout rom).eventTrace (fun i s => (events layout rom i s).core) s inputs)
      (CoreModel.snapshot ((component layout rom).run s inputs).core) := by
  induction inputs generalizing s with
  | nil => exact .nil _
  | cons i rest ih => exact (core_edge_path _ _ _ _ h).append (ih _ (preserved _ _ _ _ h))

theorem ram_trace_path (layout : AddressMap.Layout rw aw) (rom : Rom rw) (s : State aw)
    (inputs : List Input) (h : Valid layout rom s) :
    (Memory.ByteAdapterEffects.atomic aw).Path s.ram.memory.contents
      ((component layout rom).eventTrace (fun i s => (events layout rom i s).ram) s inputs)
      ((component layout rom).run s inputs).ram.memory.contents := by
  induction inputs generalizing s with
  | nil => exact .nil _
  | cons i rest ih => exact (ram_edge_path _ _ _ _ h).append (ih _ (preserved _ _ _ _ h))

theorem mmio_trace_replay (layout : AddressMap.Layout rw aw) (rom : Rom rw) (s : State aw)
    (inputs : List Input) :
    MmioModel.replay s.mmio
      ((component layout rom).eventTrace (fun i s => (events layout rom i s).mmio) s inputs) =
      some ((component layout rom).run s inputs).mmio := by
  induction inputs generalizing s with
  | nil => rfl
  | cons i rest ih =>
    change MmioModel.replay s.mmio ((events layout rom i s).mmio ++ _) = _
    rw [MmioModel.replay_append, mmio_replay, Option.bind_some]
    exact ih _

theorem reset_events (layout : AddressMap.Layout rw aw) (rom : Rom rw) (i : Input)
    (s : State aw) (h : i.reset = true) :
    (events layout rom i s).core = [.reset] ∧ (events layout rom i s).ram = [] ∧
      (events layout rom i s).mmio = [.reset] := by
  simp [events, CoreModel.events, CoreModel.observe, CoreModel.event, CoreModel.tick,
    coreInput, Memory.ByteAdapterEffects.events, Memory.ByteAdapterModel.completedRequests,
    ramInput, MmioModel.events, mmioInput, h]

/-- No orphan RAM completion is hidden by the architectural trace. Conversely,
every deferred architectural completion is this edge's actual RAM event. -/
theorem ram_completion_count (layout : AddressMap.Layout rw aw) (rom : Rom rw)
    (i : Input) (s : State aw) (h : Valid layout rom s) :
    (events layout rom i s).ram.length =
      CoreModel.dataEventCount .deferred (observe layout rom i s).core.event := by
  change _ = CoreModel.dataEventCount .deferred (CoreModel.event (coreInput layout rom i s) s.core)
  rw [(CoreModel.data_event_edges _ _).2]
  have owned := h.ram
  cases phase : s.core.phase <;>
    simp only [RamOwned, phase] at owned
  all_goals try simp [events, Memory.ByteAdapterEffects.events,
    Memory.ByteAdapterModel.completedRequests, ramInput, CoreModel.deferredCompleted,
    CoreModel.observe, coreInput, phase]
  obtain ⟨physical, route, pending⟩ := owned
  cases i.reset <;> simp [Memory.ByteAdapterModel.offer, pending]

end Pinwheel.Hardware.Processor.SystemModel
