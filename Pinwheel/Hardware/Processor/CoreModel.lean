import Pinwheel.Hardware.Processor.RV32I.Semantics
import Pinwheel.Hardware.Timed.Events

/-! A pure, serialized RV32I controller. This is neither a circuit nor a memory
implementation. Instruction fetch and RAM use separate request/response edges;
an atomic data service permits MMIO effects and retirement on the same edge.
Only a response to an owned deferred request is consumed. Reset cancels local
ownership and must synchronously cancel the provider's outstanding responses:
untagged replies cannot distinguish a stale reply after a subsequent request.
The provider owns memory preservation, access policy, and effects. In particular
an atomic service must perform its effect on this edge, and a deferred service
must perform its acknowledged effect on the later response edge.

The default boot PC is zero. Fetch alignment is checked before an offer; access
permission/range is a provider obligation represented by a precise fetch fault.
FENCE has local service after the serialized prior accesses have completed. It
does not await unrelated device activity such as UART physical transmission.
-/
namespace Pinwheel.Hardware.Processor.CoreModel

open RV32I

inductive FetchReply where
  | instruction (word : Word)
  | accessFault
  deriving DecidableEq, Repr

inductive DataReply where
  | success (data : Word)
  | fault (reason : Semantics.MemoryFault)
  deriving DecidableEq, Repr

inductive DataService where
  | deferred
  | atomic (reply : DataReply)
  deriving DecidableEq, Repr

/-- Only load/store requests cross the data interface. FENCE is local. -/
inductive DataRequest where
  | load (context : Semantics.Context) (op : LoadOp) (dest : Register) (address : Word)
  | store (context : Semantics.Context) (op : StoreOp) (address operand : Word)

def DataRequest.pending : DataRequest → Semantics.Pending
  | .load c op d a => .load c op d a
  | .store c op a v => .store c op a v

def DataRequest.context (request : DataRequest) : Semantics.Context := request.pending.context
def DataRequest.intent (request : DataRequest) : Semantics.Intent := request.pending.intent

def DataRequest.reply : (request : DataRequest) → DataReply → Semantics.Reply request.pending
  | .load _ _ _ _, .success data => .loaded data
  | .store _ _ _ _, .success _ => .stored
  | .load _ _ _ _, .fault reason => .loadFault reason
  | .store _ _ _ _, .fault reason => .storeFault reason

def DataRequest.finish (request : DataRequest) (reply : DataReply) : Semantics.Outcome :=
  Semantics.finish request.pending (request.reply reply)

inductive Cause where
  | fetchMisaligned
  | fetchAccessFault
  | instruction (reason : Semantics.Trap)
  deriving DecidableEq, Repr

structure Fault where
  pc : Word
  word : Option Word
  cause : Cause
  deriving DecidableEq, Repr

inductive Phase where
  | fetchRequest
  | fetchResponse
  | execute (word : Word)
  | dataRequest (request : DataRequest)
  | dataResponse (request : DataRequest)
  | fence (context : Semantics.Context)
  | terminal (fault : Fault)

structure State where
  arch : Semantics.State
  phase : Phase

def boot : Semantics.State := ⟨0, fun _ => 0⟩
def initial : State := ⟨boot, .fetchRequest⟩

structure Input where
  reset : Bool := false
  fetchReady : Bool := false
  fetchResponse : Option FetchReply := none
  dataService : Option DataService := none
  dataResponse : Option DataReply := none

/-- The actual completion path and reply are retained in the event. A store's
ignored success payload is retained too, rather than fabricated from a model. -/
inductive DataPath where
  | atomic | deferred
  deriving DecidableEq, Repr

inductive Completion where
  | execute
  | data (path : DataPath) (intent : Semantics.Intent) (reply : DataReply)
  | fence
  deriving DecidableEq, Repr

inductive Event where
  | reset
  | retired (word : Word) (completion : Completion) (after : Semantics.State)
  | trapped (fault : Fault) (completion : Option Completion)

structure Output where
  cancel : Bool
  fetch : Option Word
  fetchResponseReady : Bool
  data : Option Semantics.Intent
  dataResponseReady : Bool
  event : Option Event
  terminal : Option Fault

def aligned (state : Semantics.State) : Prop := state.pc.toNat % 4 = 0
instance (state : Semantics.State) : Decidable (aligned state) := inferInstanceAs (Decidable (_ = _))

def terminal : State → Option Fault
  | ⟨_, .terminal fault⟩ => some fault
  | _ => none

/-- Invariants concern issued/captured operands and their unchanged origin.
They impose no value restriction on registers or legal memory replies. -/
def Valid (state : State) : Prop :=
  match state.phase with
  | .fetchRequest => True
  | .fetchResponse | .execute _ => aligned state.arch
  | .dataRequest request | .dataResponse request =>
      aligned state.arch ∧ request.context.state = state.arch ∧ request.pending.Issued
  | .fence context =>
      aligned state.arch ∧ context.state = state.arch ∧ (Semantics.Pending.fence context).Issued
  | .terminal fault => fault.pc = state.arch.pc

def acceptOutcome (state : State) (completion : Completion) (outcome : Semantics.Outcome) : State × Option Event :=
  match outcome with
  | .retired context after => (⟨after, .fetchRequest⟩, some (.retired context.word completion after))
  | .trapped _ word reason =>
      let fault := Fault.mk state.arch.pc (some word) (.instruction reason)
      (⟨state.arch, .terminal fault⟩, some (.trapped fault (some completion)))
  | .pending (.load c op d a) => (⟨state.arch, .dataRequest (.load c op d a)⟩, none)
  | .pending (.store c op a v) => (⟨state.arch, .dataRequest (.store c op a v)⟩, none)
  | .pending (.fence context) => (⟨state.arch, .fence context⟩, none)

def tick (input : Input) (state : State) : State × Option Event :=
  if input.reset then (initial, some .reset) else
  match state.phase with
  | .fetchRequest =>
      if aligned state.arch then
        (if input.fetchReady then ⟨state.arch, .fetchResponse⟩ else state, none)
      else
        let fault := Fault.mk state.arch.pc none .fetchMisaligned
        (⟨state.arch, .terminal fault⟩, some (.trapped fault none))
  | .fetchResponse =>
      match input.fetchResponse with
      | none => (state, none)
      | some (.instruction word) => (⟨state.arch, .execute word⟩, none)
      | some .accessFault =>
          let fault := Fault.mk state.arch.pc none .fetchAccessFault
          (⟨state.arch, .terminal fault⟩, some (.trapped fault none))
  | .execute word => acceptOutcome state .execute (Semantics.step state.arch word)
  | .dataRequest request =>
      match input.dataService with
      | none => (state, none)
      | some .deferred => (⟨state.arch, .dataResponse request⟩, none)
      | some (.atomic reply) => acceptOutcome state (.data .atomic request.intent reply) (request.finish reply)
  | .dataResponse request =>
      match input.dataResponse with
      | none => (state, none)
      | some reply => acceptOutcome state (.data .deferred request.intent reply) (request.finish reply)
  | .fence context => acceptOutcome state .fence (Semantics.finish (.fence context) .fenced)
  | .terminal _ => (state, none)

def step (input : Input) (state : State) : State := (tick input state).1
def event (input : Input) (state : State) : Option Event := (tick input state).2

def observe (input : Input) (state : State) : Output :=
  { cancel := input.reset
    fetch := if input.reset then none else
      match state.phase with | .fetchRequest => if aligned state.arch then some state.arch.pc else none | _ => none
    fetchResponseReady := !input.reset && match state.phase with | .fetchResponse => true | _ => false
    data := if input.reset then none else
      match state.phase with | .dataRequest request => some request.intent | _ => none
    dataResponseReady := !input.reset && match state.phase with | .dataResponse _ => true | _ => false
    event := event input state
    terminal := if input.reset then none else terminal state }

def component : Timed.Component Input State Output := ⟨step, observe⟩
def events (input : Input) (state : State) : List Event := (observe input state).event.toList

@[simp] theorem initial_valid : Valid initial := trivial

theorem reset_step (input : Input) (state : State) (h : input.reset = true) : step input state = initial := by
  simp [step, tick, h]

theorem reset_outputs (input : Input) (state : State) (h : input.reset = true) :
    (observe input state).fetch = none ∧ (observe input state).data = none ∧
    (observe input state).fetchResponseReady = false ∧
    (observe input state).dataResponseReady = false ∧ events input state = [.reset] := by
  simp [observe, events, event, tick, h]

theorem data_finish_terminal (request : DataRequest) (reply : DataReply) :
    (∃ context after, request.finish reply = .retired context after) ∨
    (∃ origin word reason, request.finish reply = .trapped origin word reason) := by
  cases request <;> cases reply <;> simp [DataRequest.finish, DataRequest.reply, DataRequest.pending, Semantics.finish]

theorem acceptOutcome_valid (state : State) (completion : Completion) (outcome : Semantics.Outcome)
    (ha : aligned state.arch) (ho : outcome.origin = state.arch)
    (hp : ∀ pending, outcome = .pending pending → pending.Issued) :
    Valid (acceptOutcome state completion outcome).1 := by
  cases outcome with
  | retired context after => trivial
  | trapped origin word reason => rfl
  | pending pending =>
      have hi := hp pending rfl
      cases pending <;> exact ⟨ha, ho, hi⟩

theorem preserved (input : Input) (state : State) (h : Valid state) : Valid (step input state) := by
  rcases state with ⟨arch, phase⟩
  unfold step tick
  split
  · exact initial_valid
  · cases phase <;> simp only [Valid] at h <;> dsimp only
    case fetchRequest =>
        split
        · split
          · assumption
          · exact h
        · rfl
    case fetchResponse =>
        cases input.fetchResponse with
        | none => exact h
        | some reply => cases reply with
          | instruction word => exact h
          | accessFault => rfl
    case execute word =>
        exact acceptOutcome_valid _ _ _ h (Semantics.step_origin _ _) (Semantics.step_pending_issued _ _)
    case dataRequest request =>
        cases input.dataService with
        | none => exact h
        | some service => cases service with
          | deferred => exact h
          | atomic reply =>
              apply acceptOutcome_valid _ _ _ h.1
              · exact (Semantics.finish_origin _ _).trans h.2.1
              · intro p he
                obtain ⟨c, a, ht⟩ | ⟨s, w, r, ht⟩ := data_finish_terminal request reply <;> rw [ht] at he <;> cases he
    case dataResponse request =>
        cases input.dataResponse with
        | none => exact h
        | some reply =>
            apply acceptOutcome_valid _ _ _ h.1
            · exact (Semantics.finish_origin _ _).trans h.2.1
            · intro p he
              obtain ⟨c, a, ht⟩ | ⟨s, w, r, ht⟩ := data_finish_terminal request reply <;> rw [ht] at he <;> cases he
    case fence context => trivial
    case terminal fault => exact h

/-- Independent architectural meaning of a concrete completion. In particular
the actual data reply, intent, origin, and issued instruction must agree. -/
def Meaning (origin : Semantics.State) (word : Word) (completion : Completion)
    (outcome : Semantics.Outcome) : Prop :=
  match completion with
  | .execute => Semantics.step origin word = outcome
  | .data _ intent reply => ∃ request : DataRequest,
      request.context.state = origin ∧ request.context.word = word ∧
      request.pending.Issued ∧ request.intent = intent ∧ request.finish reply = outcome
  | .fence => ∃ context : Semantics.Context,
      context.state = origin ∧ context.word = word ∧
      (Semantics.Pending.fence context).Issued ∧
      Semantics.finish (.fence context) .fenced = outcome

structure Architectural where
  arch : Semantics.State
  terminal : Option Fault

def snapshot (state : State) : Architectural := ⟨state.arch, terminal state⟩

/-- Architectural event rules do not refer to the controller transition.
Fetch faults have no fetched instruction; execution/data faults retain it.
Once trapped, only reset is an allowed architectural event. -/
inductive Rule : Architectural → Event → Architectural → Prop where
  | reset (before : Architectural) : Rule before .reset ⟨boot, none⟩
  | retire (before : Semantics.State) (word : Word) (completion : Completion)
      (context : Semantics.Context) (after : Semantics.State)
      (alignment : aligned before)
      (meaning : Meaning before word completion (.retired context after)) :
      Rule ⟨before, none⟩ (.retired word completion after) ⟨after, none⟩
  | trap (before : Semantics.State) (word : Word) (completion : Completion) (reason : Semantics.Trap)
      (alignment : aligned before)
      (meaning : Meaning before word completion (.trapped before word reason)) :
      Rule ⟨before, none⟩ (.trapped ⟨before.pc, some word, .instruction reason⟩ (some completion))
        ⟨before, some ⟨before.pc, some word, .instruction reason⟩⟩
  | fetchMisaligned (before : Semantics.State) (alignment : ¬ aligned before) :
      Rule ⟨before, none⟩ (.trapped ⟨before.pc, none, .fetchMisaligned⟩ none)
        ⟨before, some ⟨before.pc, none, .fetchMisaligned⟩⟩
  | fetchAccess (before : Semantics.State) (alignment : aligned before) :
      Rule ⟨before, none⟩ (.trapped ⟨before.pc, none, .fetchAccessFault⟩ none)
        ⟨before, some ⟨before.pc, none, .fetchAccessFault⟩⟩

def architecture : Timed.EventSpec Architectural Event := ⟨Rule⟩

theorem acceptOutcome_path (state : State) (completion : Completion) (outcome : Semantics.Outcome)
    (ht : terminal state = none) (ha : aligned state.arch) (ho : outcome.origin = state.arch)
    (hm : Meaning state.arch outcome.word completion outcome) :
    architecture.Path (snapshot state) (acceptOutcome state completion outcome).2.toList
      (snapshot (acceptOutcome state completion outcome).1) := by
  change architecture.Path ⟨state.arch, terminal state⟩ _ _
  rw [ht]
  cases outcome with
  | retired context after =>
      exact .cons (Rule.retire state.arch context.word completion context after ha hm) (.nil _)
  | trapped origin word reason =>
      change origin = state.arch at ho
      subst origin
      exact .cons (Rule.trap state.arch word completion reason ha hm) (.nil _)
  | pending pending =>
      cases pending <;> exact .nil _

theorem edge_path (input : Input) (state : State) (h : Valid state) :
    architecture.Path (snapshot state) (events input state) (snapshot (step input state)) := by
  rcases state with ⟨arch, phase⟩
  unfold events observe event step tick
  split
  · exact .cons (Rule.reset _) (.nil _)
  · cases phase <;> simp only [Valid] at h <;> dsimp only
    case fetchRequest =>
      split
      · split <;> exact .nil _
      · exact .cons (Rule.fetchMisaligned _ (by assumption)) (.nil _)
    case fetchResponse =>
      cases input.fetchResponse with
      | none => exact .nil _
      | some reply => cases reply with
        | instruction word => exact .nil _
        | accessFault => exact .cons (Rule.fetchAccess _ h) (.nil _)
    case execute word =>
      apply acceptOutcome_path _ _ _ rfl h (Semantics.step_origin _ _)
      simp only [Semantics.step_word, Meaning]
    case dataRequest request =>
      cases input.dataService with
      | none => exact .nil _
      | some service => cases service with
        | deferred => exact .nil _
        | atomic reply =>
            apply acceptOutcome_path _ _ _ rfl h.1
            · exact (Semantics.finish_origin request.pending (request.reply reply)).trans h.2.1
            · exact ⟨request, h.2.1, (Semantics.finish_word request.pending (request.reply reply)).symm, h.2.2, rfl, rfl⟩
    case dataResponse request =>
      cases input.dataResponse with
      | none => exact .nil _
      | some reply =>
          apply acceptOutcome_path _ _ _ rfl h.1
          · exact (Semantics.finish_origin request.pending (request.reply reply)).trans h.2.1
          · exact ⟨request, h.2.1, (Semantics.finish_word request.pending (request.reply reply)).symm, h.2.2, rfl, rfl⟩
    case fence context =>
      apply acceptOutcome_path _ _ _ rfl h.1
      · exact h.2.1
      · exact ⟨context, h.2.1, rfl, h.2.2, rfl⟩
    case terminal fault => exact .nil _

def refinement : Timed.EventRefinement component architecture events (fun _ _ => True) where
  Rel state abstract := Valid state ∧ snapshot state = abstract
  edge := by
    intro input state abstract h _
    rcases h with ⟨hv, rfl⟩
    exact ⟨snapshot (step input state), edge_path input state hv, preserved input state hv, rfl⟩

theorem run_valid (state : State) (inputs : List Input) (h : Valid state) :
    Valid (component.run state inputs) := by
  induction inputs generalizing state with
  | nil => exact h
  | cons input rest ih => exact ih _ (preserved input state h)

theorem trace_path (state : State) (inputs : List Input) (h : Valid state) :
    architecture.Path (snapshot state) (component.eventTrace events state inputs)
      (snapshot (component.run state inputs)) := by
  induction inputs generalizing state with
  | nil => exact .nil _
  | cons input rest ih => exact (edge_path input state h).append (ih _ (preserved input state h))

/-- Replay is of the actual after-state records. `trace_path` additionally
checks those records against instruction semantics and issued actual replies. -/
def applyEvent (before : Architectural) : Event → Architectural
  | .reset => ⟨boot, none⟩
  | .retired _ _ after => ⟨after, none⟩
  | .trapped fault _ => ⟨before.arch, some fault⟩

def replay (before : Architectural) (trace : List Event) : Architectural := trace.foldl applyEvent before

theorem rule_replay (before after : Architectural) (event : Event) (h : Rule before event after) :
    applyEvent before event = after := by cases h <;> rfl

theorem path_replay (before after : Architectural) (trace : List Event)
    (h : architecture.Path before trace after) : replay before trace = after := by
  induction h with
  | nil => rfl
  | cons edge rest ih =>
      change replay (applyEvent _ _) _ = _
      rw [rule_replay _ _ _ edge]
      exact ih

theorem trace_replay (state : State) (inputs : List Input) (h : Valid state) :
    replay (snapshot state) (component.eventTrace events state inputs) = snapshot (component.run state inputs) :=
  path_replay _ _ _ (trace_path state inputs h)

theorem no_event_no_update (input : Input) (state : State) (h : Valid state)
    (he : event input state = none) : snapshot (step input state) = snapshot state := by
  have path := edge_path input state h
  change architecture.Path _ (event input state).toList _ at path
  rw [he] at path
  exact (Timed.EventSpec.Path.nil_iff.mp path).symm

theorem terminal_quiet (input : Input) (arch : Semantics.State) (fault : Fault)
    (h : input.reset = false) :
    step input ⟨arch, .terminal fault⟩ = ⟨arch, .terminal fault⟩ ∧
    event input ⟨arch, .terminal fault⟩ = none := by simp [step, event, tick, h]

theorem fetch_stalled (input : Input) (arch : Semantics.State)
    (hr : input.reset = false) (hi : input.fetchResponse = none) :
    step input ⟨arch, .fetchResponse⟩ = ⟨arch, .fetchResponse⟩ := by simp [step, tick, hr, hi]

theorem data_offer_stalled (input : Input) (arch : Semantics.State) (request : DataRequest)
    (hr : input.reset = false) (hi : input.dataService = none) :
    step input ⟨arch, .dataRequest request⟩ = ⟨arch, .dataRequest request⟩ := by simp [step, tick, hr, hi]

theorem data_reply_stalled (input : Input) (arch : Semantics.State) (request : DataRequest)
    (hr : input.reset = false) (hi : input.dataResponse = none) :
    step input ⟨arch, .dataResponse request⟩ = ⟨arch, .dataResponse request⟩ := by simp [step, tick, hr, hi]

/-- No reply is consumed on the same edge that establishes deferred ownership. -/
theorem deferred_edge (input : Input) (arch : Semantics.State) (request : DataRequest)
    (hr : input.reset = false) (hi : input.dataService = some .deferred) :
    tick input ⟨arch, .dataRequest request⟩ = (⟨arch, .dataResponse request⟩, none) := by simp [tick, hr, hi]

theorem atomic_edge (input : Input) (arch : Semantics.State) (request : DataRequest) (reply : DataReply)
    (hr : input.reset = false) (hi : input.dataService = some (.atomic reply)) :
    tick input ⟨arch, .dataRequest request⟩ =
      acceptOutcome ⟨arch, .dataRequest request⟩ (.data .atomic request.intent reply) (request.finish reply) := by
  simp [tick, hr, hi]

def fetchOwned (state : State) : Nat := match state.phase with | .fetchResponse => 1 | _ => 0
def dataOwned (state : State) : Nat := match state.phase with | .dataResponse _ => 1 | _ => 0
def heldInstruction (state : State) : Nat :=
  match state.phase with | .execute _ | .dataRequest _ | .dataResponse _ | .fence _ => 1 | _ => 0

def fetchAccepted (input : Input) (state : State) : Nat :=
  if (observe input state).fetch.isSome && input.fetchReady then 1 else 0
def fetchCompleted (input : Input) (state : State) : Nat :=
  if (observe input state).fetchResponseReady && input.fetchResponse.isSome then 1 else 0
def deferredAccepted (input : Input) (state : State) : Nat :=
  if (observe input state).data.isSome && input.dataService == some .deferred then 1 else 0
def deferredCompleted (input : Input) (state : State) : Nat :=
  if (observe input state).dataResponseReady && input.dataResponse.isSome then 1 else 0
def atomicCompleted (input : Input) (state : State) : Nat :=
  match (observe input state).data, input.dataService with
  | some _, some (.atomic _) => 1
  | _, _ => 0
def fetchedInstruction (input : Input) (state : State) : Nat :=
  match (observe input state).fetchResponseReady, input.fetchResponse with
  | true, some (.instruction _) => 1
  | _, _ => 0
def finishedInstruction (input : Input) (state : State) : Nat :=
  match (observe input state).event with
  | some (.retired _ _ _) | some (.trapped ⟨_, some _, _⟩ _) => 1
  | _ => 0

theorem acceptOutcome_not_owned (state : State) (completion : Completion) (outcome : Semantics.Outcome) :
    fetchOwned (acceptOutcome state completion outcome).1 = 0 ∧
    dataOwned (acceptOutcome state completion outcome).1 = 0 := by
  cases outcome with
  | pending request => cases request <;> exact ⟨rfl, rfl⟩
  | retired _ _ => exact ⟨rfl, rfl⟩
  | trapped _ _ _ => exact ⟨rfl, rfl⟩

/-- Edge conservation includes cancellation separately from completion.
Atomic service is deliberately absent from the deferred ownership ledger. -/
theorem ownership_edge (input : Input) (state : State) :
    fetchOwned (step input state) + fetchCompleted input state +
      (if input.reset then fetchOwned state else 0) = fetchOwned state + fetchAccepted input state ∧
    dataOwned (step input state) + deferredCompleted input state +
      (if input.reset then dataOwned state else 0) = dataOwned state + deferredAccepted input state := by
  rcases state with ⟨arch, phase⟩
  cases hr : input.reset
  · cases phase <;> simp only [step, tick, hr, Bool.false_eq_true, ↓reduceIte]
    case fetchRequest =>
      by_cases ha : aligned arch <;> cases hi : input.fetchReady <;>
        simp [fetchOwned, dataOwned, observe, fetchCompleted, fetchAccepted, deferredCompleted, deferredAccepted, hr, ha, hi]
    case fetchResponse =>
      cases hi : input.fetchResponse with
      | none => simp [fetchOwned, dataOwned, observe, fetchCompleted, fetchAccepted, deferredCompleted, deferredAccepted, hr, hi]
      | some reply => cases reply <;> simp [fetchOwned, dataOwned, observe, fetchCompleted, fetchAccepted, deferredCompleted, deferredAccepted, hr, hi]
    case execute word =>
      have h := acceptOutcome_not_owned ⟨arch, .execute word⟩ .execute (Semantics.step arch word)
      simpa [fetchOwned, dataOwned, observe, fetchCompleted, fetchAccepted, deferredCompleted, deferredAccepted, hr] using h
    case dataRequest request =>
      cases hi : input.dataService with
      | none => simp [fetchOwned, dataOwned, observe, fetchCompleted, fetchAccepted, deferredCompleted, deferredAccepted, hr, hi]
      | some service => cases service with
        | deferred => simp [fetchOwned, dataOwned, observe, fetchCompleted, fetchAccepted, deferredCompleted, deferredAccepted, hr, hi]
        | atomic reply =>
            have h := acceptOutcome_not_owned ⟨arch, .dataRequest request⟩ (.data .atomic request.intent reply) (request.finish reply)
            simpa [fetchOwned, dataOwned, observe, fetchCompleted, fetchAccepted, deferredCompleted, deferredAccepted, hr, hi] using h
    case dataResponse request =>
      cases hi : input.dataResponse with
      | none => simp [fetchOwned, dataOwned, observe, fetchCompleted, fetchAccepted, deferredCompleted, deferredAccepted, hr, hi]
      | some reply =>
          have h := acceptOutcome_not_owned ⟨arch, .dataResponse request⟩ (.data .deferred request.intent reply) (request.finish reply)
          simpa [fetchOwned, dataOwned, observe, fetchCompleted, fetchAccepted, deferredCompleted, deferredAccepted, hr, hi] using h
    case fence context =>
      simp [Semantics.finish, acceptOutcome, fetchOwned, dataOwned, observe, fetchCompleted, fetchAccepted, deferredCompleted, deferredAccepted, hr]
    case terminal fault =>
      simp [fetchOwned, dataOwned, observe, fetchCompleted, fetchAccepted, deferredCompleted, deferredAccepted, hr]
  · simp [step, tick, hr, initial, fetchOwned, dataOwned, fetchAccepted, fetchCompleted, deferredAccepted, deferredCompleted, observe]

theorem acceptOutcome_instruction (state : State) (completion : Completion) (outcome : Semantics.Outcome) :
    heldInstruction (acceptOutcome state completion outcome).1 +
      (match (acceptOutcome state completion outcome).2 with
       | some (.retired _ _ _) | some (.trapped ⟨_, some _, _⟩ _) => 1
       | _ => 0) = 1 := by
  cases outcome with
  | pending request => cases request <;> rfl
  | retired _ _ => rfl
  | trapped _ _ _ => rfl

/-- Every fetched instruction has one outstanding token until a single
retirement/trap or reset cancellation. Fetch faults do not invent a token. -/
theorem instruction_edge (input : Input) (state : State) :
    heldInstruction (step input state) + finishedInstruction input state +
      (if input.reset then heldInstruction state else 0) =
      heldInstruction state + fetchedInstruction input state := by
  rcases state with ⟨arch, phase⟩
  cases hr : input.reset
  · cases phase <;> simp only [step, tick, hr, Bool.false_eq_true, ↓reduceIte]
    case fetchRequest =>
      by_cases ha : aligned arch <;> cases hi : input.fetchReady <;>
        simp [heldInstruction, finishedInstruction, fetchedInstruction, observe, event, tick, hr, ha, hi]
    case fetchResponse =>
      cases hi : input.fetchResponse with
      | none => simp [heldInstruction, finishedInstruction, fetchedInstruction, observe, event, tick, hr, hi]
      | some reply => cases reply <;> simp [heldInstruction, finishedInstruction, fetchedInstruction, observe, event, tick, hr, hi]
    case execute word =>
      simpa [heldInstruction, finishedInstruction, fetchedInstruction, observe, event, tick, hr] using
        acceptOutcome_instruction ⟨arch, .execute word⟩ .execute (Semantics.step arch word)
    case dataRequest request =>
      cases hi : input.dataService with
      | none => simp [heldInstruction, finishedInstruction, fetchedInstruction, observe, event, tick, hr, hi]
      | some ds => cases ds with
        | deferred => simp [heldInstruction, finishedInstruction, fetchedInstruction, observe, event, tick, hr, hi]
        | atomic reply =>
            simpa [heldInstruction, finishedInstruction, fetchedInstruction, observe, event, tick, hr, hi] using
              acceptOutcome_instruction ⟨arch, .dataRequest request⟩ (.data .atomic request.intent reply) (request.finish reply)
    case dataResponse request =>
      cases hi : input.dataResponse with
      | none => simp [heldInstruction, finishedInstruction, fetchedInstruction, observe, event, tick, hr, hi]
      | some reply =>
          simpa [heldInstruction, finishedInstruction, fetchedInstruction, observe, event, tick, hr, hi] using
            acceptOutcome_instruction ⟨arch, .dataResponse request⟩ (.data .deferred request.intent reply) (request.finish reply)
    case fence context =>
      simp [Semantics.finish, acceptOutcome, heldInstruction, finishedInstruction, fetchedInstruction, observe, event, tick, hr]
    case terminal fault => simp [heldInstruction, finishedInstruction, fetchedInstruction, observe, event, tick, hr]
  · simp [step, tick, hr, initial, heldInstruction, finishedInstruction, fetchedInstruction, observe, event]

def count (measure : Input → State → Nat) (state : State) : List Input → Nat
  | [] => 0
  | input :: rest => measure input state + count measure (step input state) rest

def canceled (owned : State → Nat) (input : Input) (state : State) : Nat :=
  if input.reset then owned state else 0

theorem conservation (owned : State → Nat) (accepted completed : Input → State → Nat)
    (edge : ∀ input state, owned (step input state) + completed input state + canceled owned input state =
      owned state + accepted input state) (state : State) (inputs : List Input) :
    owned (component.run state inputs) + count completed state inputs + count (canceled owned) state inputs =
      owned state + count accepted state inputs := by
  induction inputs generalizing state with
  | nil => simp [Timed.Component.run, count]
  | cons input rest ih =>
      have he := edge input state
      have tail := ih (step input state)
      change owned (component.run (step input state) rest) +
        (completed input state + count completed (step input state) rest) +
        (canceled owned input state + count (canceled owned) (step input state) rest) =
        owned state + (accepted input state + count accepted (step input state) rest)
      omega

theorem fetch_conservation (state : State) (inputs : List Input) :
    fetchOwned (component.run state inputs) + count fetchCompleted state inputs + count (canceled fetchOwned) state inputs =
      fetchOwned state + count fetchAccepted state inputs :=
  conservation _ _ _ (fun i s => (ownership_edge i s).1) state inputs

theorem data_conservation (state : State) (inputs : List Input) :
    dataOwned (component.run state inputs) + count deferredCompleted state inputs + count (canceled dataOwned) state inputs =
      dataOwned state + count deferredAccepted state inputs :=
  conservation _ _ _ (fun i s => (ownership_edge i s).2) state inputs

theorem instruction_conservation (state : State) (inputs : List Input) :
    heldInstruction (component.run state inputs) + count finishedInstruction state inputs + count (canceled heldInstruction) state inputs =
      heldInstruction state + count fetchedInstruction state inputs :=
  conservation _ _ _ instruction_edge state inputs

def dataEventCount (path : DataPath) : Option Event → Nat
  | some (.retired _ (.data actual _ _) _) | some (.trapped _ (some (.data actual _ _))) =>
      if actual = path then 1 else 0
  | _ => 0

/-- The actual path-tagged architectural event occurs on precisely the
provider's completion edge, including faults and loads whose destination is x0. -/
theorem data_event_edges (input : Input) (state : State) :
    dataEventCount .atomic (event input state) = atomicCompleted input state ∧
    dataEventCount .deferred (event input state) = deferredCompleted input state := by
  rcases state with ⟨arch, phase⟩
  cases hr : input.reset
  · cases phase
    case fetchRequest =>
      by_cases ha : aligned arch <;> cases hi : input.fetchReady <;>
        simp [dataEventCount, event, tick, atomicCompleted, deferredCompleted, observe, hr, ha, hi]
    case fetchResponse =>
      cases hi : input.fetchResponse with
      | none => simp [dataEventCount, event, tick, atomicCompleted, deferredCompleted, observe, hr, hi]
      | some reply => cases reply <;> simp [dataEventCount, event, tick, atomicCompleted, deferredCompleted, observe, hr, hi]
    case execute word =>
      cases he : Semantics.step arch word with
      | retired _ _ => simp [dataEventCount, event, tick, acceptOutcome, atomicCompleted, deferredCompleted, observe, hr, he]
      | trapped _ _ _ => simp [dataEventCount, event, tick, acceptOutcome, atomicCompleted, deferredCompleted, observe, hr, he]
      | pending p => cases p <;> simp [dataEventCount, event, tick, acceptOutcome, atomicCompleted, deferredCompleted, observe, hr, he]
    case dataRequest request =>
      cases hi : input.dataService with
      | none => simp [dataEventCount, event, tick, atomicCompleted, deferredCompleted, observe, hr, hi]
      | some ds => cases ds with
        | deferred => simp [dataEventCount, event, tick, atomicCompleted, deferredCompleted, observe, hr, hi]
        | atomic reply => cases request <;> cases reply <;>
            simp [dataEventCount, event, tick, atomicCompleted, deferredCompleted, observe, hr, hi,
              DataRequest.finish, DataRequest.reply, DataRequest.pending, Semantics.finish, acceptOutcome]
    case dataResponse request =>
      cases hi : input.dataResponse with
      | none => simp [dataEventCount, event, tick, atomicCompleted, deferredCompleted, observe, hr, hi]
      | some reply => cases request <;> cases reply <;>
          simp [dataEventCount, event, tick, atomicCompleted, deferredCompleted, observe, hr, hi,
            DataRequest.finish, DataRequest.reply, DataRequest.pending, Semantics.finish, acceptOutcome]
    case fence context => simp [dataEventCount, event, tick, atomicCompleted, deferredCompleted, observe, hr, Semantics.finish, acceptOutcome]
    case terminal fault => simp [dataEventCount, event, tick, atomicCompleted, deferredCompleted, observe, hr]
  · simp [dataEventCount, event, tick, atomicCompleted, deferredCompleted, observe, hr]

theorem reset_recovery (input : Input) (state : State) (hr : input.reset = true) (rest : List Input) :
    architecture.Path (snapshot initial) (component.eventTrace events (step input state) rest)
      (snapshot (component.run (step input state) rest)) := by
  rw [reset_step input state hr]
  exact trace_path initial rest initial_valid

def heldWord (state : State) : Option Word :=
  match state.phase with
  | .execute word => some word
  | .dataRequest request | .dataResponse request => some request.context.word
  | .fence context => some context.word
  | _ => none

def finishedWord : Option Event → Option Word
  | some (.retired word _ _) => some word
  | some (.trapped fault _) => fault.word
  | _ => none

def enteredWords (input : Input) (state : State) : List Word :=
  match (observe input state).fetchResponseReady, input.fetchResponse with
  | true, some (.instruction word) => [word]
  | _, _ => []

/-- Canceled instructions remain in the ordered accounting history without
inventing a retirement or a provider effect. -/
def exitedWords (input : Input) (state : State) : List Word :=
  if input.reset then (heldWord state).toList else (finishedWord (event input state)).toList

theorem acceptOutcome_word (state : State) (completion : Completion) (outcome : Semantics.Outcome) :
    (finishedWord (acceptOutcome state completion outcome).2).toList ++
      (heldWord (acceptOutcome state completion outcome).1).toList = [outcome.word] := by
  cases outcome with
  | pending p => cases p <;> rfl
  | retired _ _ => rfl
  | trapped _ _ _ => rfl

theorem word_edge (input : Input) (state : State) :
    exitedWords input state ++ (heldWord (step input state)).toList =
      (heldWord state).toList ++ enteredWords input state := by
  rcases state with ⟨arch, phase⟩
  cases hr : input.reset
  · cases phase
    case fetchRequest =>
      by_cases ha : aligned arch <;> cases hi : input.fetchReady <;>
        simp [exitedWords, enteredWords, heldWord, finishedWord, observe, event, step, tick, hr, ha, hi]
    case fetchResponse =>
      cases hi : input.fetchResponse with
      | none => simp [exitedWords, enteredWords, heldWord, finishedWord, observe, event, step, tick, hr, hi]
      | some reply => cases reply <;> simp [exitedWords, enteredWords, heldWord, finishedWord, observe, event, step, tick, hr, hi]
    case execute word =>
      simpa [exitedWords, enteredWords, heldWord, observe, event, step, tick, hr, Semantics.step_word] using
        acceptOutcome_word ⟨arch, .execute word⟩ .execute (Semantics.step arch word)
    case dataRequest request =>
      cases hi : input.dataService with
      | none => simp [exitedWords, enteredWords, heldWord, finishedWord, observe, event, step, tick, hr, hi]
      | some ds => cases ds with
        | deferred => simp [exitedWords, enteredWords, heldWord, finishedWord, observe, event, step, tick, hr, hi]
        | atomic reply =>
            simpa [exitedWords, enteredWords, heldWord, observe, event, step, tick, hr, hi, DataRequest.finish, DataRequest.context] using
              acceptOutcome_word ⟨arch, .dataRequest request⟩ (.data .atomic request.intent reply) (request.finish reply)
    case dataResponse request =>
      cases hi : input.dataResponse with
      | none => simp [exitedWords, enteredWords, heldWord, finishedWord, observe, event, step, tick, hr, hi]
      | some reply =>
          simpa [exitedWords, enteredWords, heldWord, observe, event, step, tick, hr, hi, DataRequest.finish, DataRequest.context] using
            acceptOutcome_word ⟨arch, .dataResponse request⟩ (.data .deferred request.intent reply) (request.finish reply)
    case fence context =>
      simp [exitedWords, enteredWords, heldWord, finishedWord, observe, event, step, tick, hr, Semantics.finish, acceptOutcome]
    case terminal fault => simp [exitedWords, enteredWords, heldWord, finishedWord, observe, event, step, tick, hr]
  · simp [exitedWords, enteredWords, heldWord, observe, step, tick, hr, initial]

def wordTrace (extract : Input → State → List Word) (state : State) : List Input → List Word
  | [] => []
  | input :: rest => extract input state ++ wordTrace extract (step input state) rest

/-- Exact order, including repeated identical words: every accepted fetched
instruction exits once (completion or cancellation), or remains the one held
instruction. The provider's assertion that a fetched word is the ROM content
is a separate integration obligation. -/
theorem word_conservation (state : State) (inputs : List Input) :
    wordTrace exitedWords state inputs ++ (heldWord (component.run state inputs)).toList =
      (heldWord state).toList ++ wordTrace enteredWords state inputs := by
  induction inputs generalizing state with
  | nil => simp [wordTrace, Timed.Component.run]
  | cons input rest ih =>
      change (exitedWords input state ++ wordTrace exitedWords (step input state) rest) ++ (heldWord (component.run (step input state) rest)).toList =
        (heldWord state).toList ++ (enteredWords input state ++ wordTrace enteredWords (step input state) rest)
      rw [List.append_assoc, ih, ← List.append_assoc, word_edge, List.append_assoc]

def rank (state : State) : Nat :=
  match state.phase with
  | .fetchRequest => 4 | .fetchResponse => 3 | .execute _ => 2
  | .dataRequest _ => 1 | .dataResponse _ | .fence _ | .terminal _ => 0

def finished (input : Input) (state : State) : Prop :=
  match event input state with | some (.retired _ _ _) | some (.trapped _ _) => True | _ => False

def service (input : Input) (state : State) : Bool :=
  if input.reset then false else match state.phase with
  | .fetchRequest => input.fetchReady
  | .fetchResponse => input.fetchResponse.isSome
  | .execute _ | .fence _ => true
  | .dataRequest _ => input.dataService.isSome
  | .dataResponse _ => input.dataResponse.isSome
  | .terminal _ => false

theorem progress_edge (input : Input) (state : State) (hr : input.reset = false)
    (hf : ¬ finished input state) :
    rank (step input state) + (if service input state then 1 else 0) ≤ rank state := by
  rcases state with ⟨arch, phase⟩
  cases phase <;> simp only [step, tick, hr, Bool.false_eq_true, ↓reduceIte]
  case fetchRequest =>
    by_cases ha : aligned arch <;> cases hi : input.fetchReady <;>
      simp_all [finished, event, tick, service, rank]
  case fetchResponse =>
    cases hi : input.fetchResponse with
    | none => simp [service, rank, hr, hi]
    | some reply => cases reply <;> simp_all [finished, event, tick, service, rank]
  case execute word =>
    cases he : Semantics.step arch word with
    | retired c after => simp_all [finished, event, tick, acceptOutcome]
    | trapped s w reason => simp_all [finished, event, tick, acceptOutcome]
    | pending p => cases p <;> simp [service, rank, acceptOutcome, hr]
  case dataRequest request =>
    cases hi : input.dataService with
    | none => simp [service, rank, hr, hi]
    | some ds => cases ds with
      | deferred => simp [service, rank, hr, hi]
      | atomic reply => cases request <;> cases reply <;>
          simp_all [finished, event, tick, acceptOutcome, DataRequest.finish, DataRequest.reply, DataRequest.pending, Semantics.finish]
  case dataResponse request =>
    cases hi : input.dataResponse with
    | none => simp [service, rank, hr, hi]
    | some reply => cases request <;> cases reply <;>
        simp_all [finished, event, tick, acceptOutcome, DataRequest.finish, DataRequest.reply, DataRequest.pending, Semantics.finish]
  case fence context => simp_all [finished, event, tick, acceptOutcome, Semantics.finish]
  case terminal fault => simp [service, rank, hr]

/-- At most five service edges from fetch request to retirement/trap. Stalls
do not count; reset is excluded. This asserts no eventual external service. -/
def progress : Timed.ProgressBound component (fun input _ => input.reset = false) finished service where
  rank := rank
  step := progress_edge

theorem completion_of_service (state : State) (inputs : List Input)
    (hr : component.Legal (fun input _ => input.reset = false) state inputs)
    (hs : rank state < component.serviceCount service state inputs) :
    component.Occurs finished state inputs := progress.occurs_of_service_count state inputs hr hs

end Pinwheel.Hardware.Processor.CoreModel
