import Pinwheel.Hardware.Processor.CoreCertified
import Pinwheel.Hardware.Processor.CoreCircuitRequests
import Pinwheel.Hardware.Processor.CoreEventFacts

/-! Architectural events extracted from actual core ports. The retirement
record applies the physical writeback pins to the pre-edge register file and
uses the physical next-PC output. Trap records decode actual trap fields.
Completion identity comes from raw phase/held instruction/RF and actual reply
pins. Valid proves issuance and ownership; the extractor does not call the
model's event function or use an expected architectural result.
-/
namespace Pinwheel.Hardware.Processor.CoreCircuit.Events

open CoreInterface
set_option backward.isDefEq.respectTransparency false

/-- Reconstruct the architectural update reported by the retirement interface,
including intrinsic x0 behavior and every unmodified pre-edge register. -/
def committed (raw : Values Register) (out : Values Output) : RV32I.Semantics.State :=
  ⟨out retireNextPC, if out retireWriteEnable = 1 then
    RV32I.Semantics.write (arch raw).registers (out retireWriteRd) (out retireWriteData)
    else (arch raw).registers⟩

def trapped (out : Values Output) : CoreModel.Fault :=
  ⟨out trapPC, if out trapInstructionValid = 1 then some (out trapInstruction) else none,
    decodeCause (out trapCause) (out trapAddress)⟩

/-- The issued request is reconstructed from the actual held IR and pre-edge
RF by the existing representation. Raw provider reply fields are retained,
including a store success payload that is architecturally ignored. -/
def completion (i : Values Input) (raw : Values Register) : Option CoreModel.Completion :=
  if raw phase = 2 then some .execute
  else if raw phase = 3 then match (decode i).dataService, request raw with
    | some (.atomic reply), some req => some (.data .atomic req.intent reply)
    | _, _ => none
  else if raw phase = 4 then match (decode i).dataResponse, request raw with
    | some reply, some req => some (.data .deferred req.intent reply)
    | _, _ => none
  else if raw phase = 5 then some .fence else none

/-- The raw extractor is total. Its invalid-state fallbacks have no refinement
claim; existing Valid, rather than a new invariant, excludes them. -/
def extract (i : Values Input) (raw : Values Register) (out : Values Output) : List CoreModel.Event :=
  if out cancel = 1 then [.reset]
  else if out retireValid = 1 then
    [.retired (out retireInstruction) ((completion i raw).getD .execute) (committed raw out)]
  else if out trapValid = 1 then [.trapped (trapped out) (completion i raw)] else []

def events (i : Values Input) (raw : Values Register) : List CoreModel.Event :=
  extract i raw (circuit.observe i raw)

/-- This checks the retirement record against the actual next register file
and PC, independently of the ISA/model event agreement theorem. -/
theorem committed_next (i : Values Input) (raw : Values Register)
    (resetLow : i reset = 0) (retire : circuit.observe i raw retireValid = 1) :
    committed raw (circuit.observe i raw) = arch (circuit.step i raw) := by
  have retiring : retiring.eval i raw = 1 := retire
  rw [arch_step]
  simp only [resetLow, show (0 : BitVec 1) ≠ 1 by decide, ↓reduceIte, retiring]
  simp only [committed, Circuit.observe, circuit, retireNextPC, retireWriteEnable, retireWriteRd,
    retireWriteData, gated_eval, retiring, ↓reduceIte]

theorem completion_represents (i : Values Input) (raw : Values Register) (state : CoreModel.State)
    (rep : Represents raw state) : completion i raw = CoreEventFacts.completion (decode i) state := by
  rcases state with ⟨a,p⟩
  rcases rep with ⟨ha,hp⟩
  cases p with
  | fetchRequest =>
    change raw phase = 0 at hp
    simp [completion, hp, CoreEventFacts.completion]
  | fetchResponse =>
    change raw phase = 1 at hp
    simp [completion, hp, CoreEventFacts.completion]
  | execute word => simp [completion, hp.1, CoreEventFacts.completion]
  | dataRequest q =>
    have req := represented_request raw ⟨a,.dataRequest q⟩ q ha hp.2.1 hp.2.2.1 hp.2.2.2
    simp only [completion, hp.1, ↓reduceIte, req, CoreEventFacts.completion]
    cases (decode i).dataService with
    | none => rfl
    | some service => cases service <;> rfl
  | dataResponse q =>
    have req := represented_request raw ⟨a,.dataResponse q⟩ q ha hp.2.1 hp.2.2.1 hp.2.2.2
    simp only [completion, hp.1,
      ↓reduceIte, req, CoreEventFacts.completion]
    cases (decode i).dataResponse <;> rfl
  | fence c => simp [completion, hp.1, CoreEventFacts.completion]
  | terminal f => simp [completion, hp.1, CoreEventFacts.completion]

theorem completion_eq (i : Values Input) (raw : Values Register) (valid : Valid raw) :
    completion i raw = CoreEventFacts.completion (decode i) (view raw) := by
  obtain ⟨state,_,rep⟩ := valid
  rw [view_of_represents raw state rep]
  exact completion_represents i raw state rep

theorem trapped_encoded (i : Values Input) (state : CoreModel.State) (fault : CoreModel.Fault)
    (path : Option CoreModel.Completion)
    (he : CoreModel.event (decode i) state = some (.trapped fault path)) :
    trapped (CoreInterface.outputValues i state) = fault := by
  simp only [trapped, CoreInterface.outputValues, CoreModel.observe, trapPC, trapInstructionValid,
    trapInstruction, trapCause, trapAddress, he, CoreInterface.trapped, Option.map_some,
    Option.bind_some, Option.getD_some, decode_cause]
  cases fault with
  | mk pc word cause => cases word <;> rfl

/-- Exact event agreement is proved after extraction from real ports; no event
is chosen by the refinement witness or constructed from an expected after-state. -/
theorem events_eq (i : Values Input) (raw : Values Register) (valid : Valid raw) :
    events i raw = CoreModel.events (decode i) (view raw) := by
  have cancel_eq : circuit.observe i raw cancel = i reset := rfl
  have model_valid := valid_model raw valid
  rcases BitVec.eq_zero_or_eq_one (i reset) with hr | hr
  · have resetLow : (decode i).reset = false := by simp [decode, hr]
    cases he : CoreModel.event (decode i) (view raw) with
    | none =>
      simp [events, extract, cancel_eq, hr, output_eq i raw valid,
        CoreInterface.spec, CoreInterface.outputValues, CoreModel.events, CoreModel.observe,
        he, CoreInterface.retired, CoreInterface.trapped, retireValid, trapValid]
    | some event => cases event with
      | reset => exact False.elim (CoreEventFacts.event_not_reset _ _ resetLow he)
      | retired word path after =>
        have retiring : circuit.observe i raw retireValid = 1 := by
          rw [output_eq i raw valid]
          simp [CoreInterface.spec, CoreInterface.outputValues, CoreModel.observe, he,
            retireValid, CoreInterface.retired]
        have committed_eq : committed raw (circuit.observe i raw) = after := by
          rw [committed_next i raw hr retiring]
          change (view (circuit.step i raw)).arch = after
          rw [step_eq i raw valid]
          exact CoreEventFacts.retired_next _ _ model_valid word path after he
        have completion_value : completion i raw = some path := by
          rw [completion_eq i raw valid]
          have shape := CoreEventFacts.event_completion (decode i) (view raw)
          simpa only [he] using shape
        simp only [events, extract, cancel_eq, hr,
          ↓reduceIte, retiring, committed_eq, completion_value, Option.getD_some]
        rw [output_eq i raw valid]
        simp [CoreInterface.spec, CoreInterface.outputValues, CoreModel.events, CoreModel.observe,
          he, retireInstruction]
      | trapped fault path =>
        have completion_value : completion i raw = path := by
          rw [completion_eq i raw valid]
          have shape := CoreEventFacts.event_completion (decode i) (view raw)
          simpa only [he] using shape
        have observations : @Eq (Values Output) (circuit.observe i raw) (CoreInterface.outputValues i (view raw)) := by
          funext b o
          exact output_eq i raw valid o
        unfold events extract
        rw [observations, trapped_encoded i (view raw) fault path he, completion_value]
        simp [CoreInterface.outputValues, CoreModel.events, CoreModel.observe, he, resetLow,
          CoreInterface.retired, CoreInterface.trapped, cancel, retireValid, trapValid]
  · simp [events, extract, cancel_eq, hr, CoreModel.events, CoreModel.observe,
      CoreModel.event, CoreModel.tick, decode]

def snapshot (raw : Values Register) : CoreModel.Architectural := CoreModel.snapshot (view raw)

/-- A real retire pulse reports the held instruction, the pre-edge PC and the
actual whole next architectural state. No proof validity premise is needed for
this physical register/port identity; ISA legality is supplied by events_eq. -/
theorem retirement_fields (i : Values Input) (raw : Values Register)
    (resetLow : i reset = 0) (retire : circuit.observe i raw retireValid = 1) :
    events i raw = [.retired (raw instruction) ((completion i raw).getD .execute) (arch (circuit.step i raw))] ∧
      circuit.observe i raw retirePC = raw pc := by
  have pulse : retiring.eval i raw = 1 := retire
  have cancel_eq : circuit.observe i raw cancel = 0 := resetLow
  have word_eq : circuit.observe i raw retireInstruction = raw instruction := by
    change (if retiring.eval i raw = 1 then raw instruction else 0) = raw instruction
    rw [if_pos pulse]
  constructor
  · simp only [events, extract, cancel_eq, ↓reduceIte, retire, word_eq,
      committed_next i raw resetLow retire]
    rfl
  · change (if retiring.eval i raw = 1 then raw pc else 0) = raw pc
    rw [if_pos pulse]

theorem edge_path (i : Values Input) (raw : Values Register) (valid : Valid raw) :
    CoreModel.architecture.Path (snapshot raw) (events i raw) (snapshot (circuit.step i raw)) := by
  rw [events_eq i raw valid]
  unfold snapshot
  rw [step_eq i raw valid]
  exact CoreModel.edge_path (decode i) (view raw) (valid_model raw valid)

def refinement : Timed.EventRefinement circuit.component CoreModel.architecture events (fun _ _ => True) where
  Rel raw logical := Valid raw ∧ snapshot raw = logical
  edge i raw logical related _ := by
    rcases related with ⟨valid,rfl⟩
    exact ⟨snapshot (circuit.step i raw), edge_path i raw valid, preserved i raw valid, rfl⟩

theorem initialCoverage : refinement.InitialCoverage Valid (fun _ => True) where
  nonempty := ⟨zeroValues,zero_valid⟩
  covered raw valid := ⟨snapshot raw,trivial,valid,rfl⟩

/-- Every model-valid architecture/controller state is represented, including
arbitrary RF contents and every issued pending load/store/fence phase. -/
theorem logical_coverage (state : CoreModel.State) (valid : CoreModel.Valid state) :
    ∃ raw : Values Register, Valid raw ∧ snapshot raw = CoreModel.snapshot state := by
  refine ⟨encode state,valid_encode state valid,?_⟩
  simp only [snapshot, view_encode state valid]

theorem trace_path (raw : Values Register) (valid : Valid raw) (traffic : List (Values Input)) :
    CoreModel.architecture.Path (snapshot raw) (circuit.component.eventTrace events raw traffic)
      (snapshot (circuit.component.run raw traffic)) := by
  induction traffic generalizing raw with
  | nil => exact .nil _
  | cons i rest ih => exact (edge_path i raw valid).append (ih _ (preserved i raw valid))

theorem trace_replay (raw : Values Register) (valid : Valid raw) (traffic : List (Values Input)) :
    CoreModel.replay (snapshot raw) (circuit.component.eventTrace events raw traffic) =
      snapshot (circuit.component.run raw traffic) :=
  CoreModel.path_replay _ _ _ (trace_path raw valid traffic)

theorem trace_after_reset (i : Values Input) (raw : Values Register) (resetHigh : i reset = 1)
    (traffic : List (Values Input)) :
    CoreModel.architecture.Path (CoreModel.snapshot CoreModel.initial)
      (circuit.component.eventTrace events (circuit.step i raw) traffic)
      (snapshot (circuit.component.run (circuit.step i raw) traffic)) := by
  have path := trace_path (circuit.step i raw) (reset_recovery i raw resetHigh).1 traffic
  simpa only [snapshot, (reset_recovery i raw resetHigh).2] using path

variable {rtl : Timed.Component (Values Input) (Values Register) (Values Output)}

/-- The same fixed extraction applied to actual imported RTL observations.
No expected observation is substituted into this definition. -/
def artifactEvents (rtl : Timed.Component (Values Input) (Values Register) (Values Output))
    (i : Values Input) (raw : Values Register) : List CoreModel.Event := extract i raw (rtl.observe i raw)

theorem artifact_events_eq (artifact : Artifact.Correspondence circuit rtl) (i : Values Input)
    (raw : Values Register) : artifactEvents rtl i raw = events i raw := by
  simp only [artifactEvents, artifact.output_eq, events]

theorem artifact_trace_eq (artifact : Artifact.Correspondence circuit rtl)
    (raw : Values Register) (traffic : List (Values Input)) :
    rtl.eventTrace (artifactEvents rtl) raw traffic = circuit.component.eventTrace events raw traffic := by
  induction traffic generalizing raw with
  | nil => rfl
  | cons i rest ih =>
    change artifactEvents rtl i raw ++ rtl.eventTrace (artifactEvents rtl) (rtl.step i raw) rest = _
    rw [artifact_events_eq artifact, artifact.step_eq, ih]
    rfl

theorem artifact_trace_path (artifact : Artifact.Correspondence circuit rtl)
    (raw : Values Register) (valid : Valid raw) (traffic : List (Values Input)) :
    CoreModel.architecture.Path (snapshot raw) (rtl.eventTrace (artifactEvents rtl) raw traffic)
      (snapshot (rtl.run raw traffic)) := by
  rw [artifact_trace_eq artifact, artifact.run_eq]
  exact trace_path raw valid traffic

theorem artifact_trace_replay (artifact : Artifact.Correspondence circuit rtl)
    (raw : Values Register) (valid : Valid raw) (traffic : List (Values Input)) :
    CoreModel.replay (snapshot raw) (rtl.eventTrace (artifactEvents rtl) raw traffic) = snapshot (rtl.run raw traffic) :=
  CoreModel.path_replay _ _ _ (artifact_trace_path artifact raw valid traffic)

end Pinwheel.Hardware.Processor.CoreCircuit.Events
