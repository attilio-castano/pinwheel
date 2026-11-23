import Pinwheel.Hardware.Processor.CoreModel

/-! Phase/reply provenance of architectural events, independent of the circuit.
The helper only identifies the completion path; it does not produce events or
architectural after-states. -/
namespace Pinwheel.Hardware.Processor.CoreEventFacts

def completion (i : CoreModel.Input) (s : CoreModel.State) : Option CoreModel.Completion :=
  match s.phase with
  | .execute _ => some .execute
  | .dataRequest req => match i.dataService with
    | some (.atomic reply) => some (.data .atomic req.intent reply)
    | _ => none
  | .dataResponse req => i.dataResponse.map (fun reply => .data .deferred req.intent reply)
  | .fence _ => some .fence
  | _ => none

theorem event_completion (i : CoreModel.Input) (s : CoreModel.State) :
    match CoreModel.event i s with
    | some (.retired _ path _) => completion i s = some path
    | some (.trapped _ path) => completion i s = path
    | _ => True := by
  by_cases reset : i.reset = true
  · simp [CoreModel.event, CoreModel.tick, reset]
  rcases s with ⟨arch,phase⟩
  cases phase with
  | fetchRequest =>
    by_cases aligned : CoreModel.aligned arch <;>
      simp [CoreModel.event, CoreModel.tick, reset, aligned, completion]
  | fetchResponse =>
    cases hr : i.fetchResponse with
    | none => simp [CoreModel.event, CoreModel.tick, reset, hr]
    | some reply => cases reply <;> simp [CoreModel.event, CoreModel.tick, reset, hr, completion]
  | execute word =>
    cases he : RV32I.Semantics.step arch word with
    | retired context after => simp [CoreModel.event, CoreModel.tick, reset, he, CoreModel.acceptOutcome, completion]
    | trapped origin word reason => simp [CoreModel.event, CoreModel.tick, reset, he, CoreModel.acceptOutcome, completion]
    | pending pending => cases pending <;> simp [CoreModel.event, CoreModel.tick, reset, he, CoreModel.acceptOutcome]
  | dataRequest req =>
    cases hs : i.dataService with
    | none => simp [CoreModel.event, CoreModel.tick, reset, hs]
    | some service => cases service with
      | deferred => simp [CoreModel.event, CoreModel.tick, reset, hs]
      | atomic reply =>
        cases he : req.finish reply with
        | retired context after => simp [CoreModel.event, CoreModel.tick, reset, hs, he, CoreModel.acceptOutcome, completion]
        | trapped origin word reason => simp [CoreModel.event, CoreModel.tick, reset, hs, he, CoreModel.acceptOutcome, completion]
        | pending pending => cases pending <;> simp [CoreModel.event, CoreModel.tick, reset, hs, he, CoreModel.acceptOutcome]
  | dataResponse req =>
    cases hs : i.dataResponse with
    | none => simp [CoreModel.event, CoreModel.tick, reset, hs]
    | some reply =>
      cases he : req.finish reply with
      | retired context after => simp [CoreModel.event, CoreModel.tick, reset, hs, he, CoreModel.acceptOutcome, completion]
      | trapped origin word reason => simp [CoreModel.event, CoreModel.tick, reset, hs, he, CoreModel.acceptOutcome, completion]
      | pending pending => cases pending <;> simp [CoreModel.event, CoreModel.tick, reset, hs, he, CoreModel.acceptOutcome]
  | fence context => simp [CoreModel.event, CoreModel.tick, reset, RV32I.Semantics.finish, CoreModel.acceptOutcome, completion]
  | terminal _ => simp [CoreModel.event, CoreModel.tick, reset]

theorem retired_next (i : CoreModel.Input) (s : CoreModel.State) (valid : CoreModel.Valid s)
    (word : RV32I.Word) (path : CoreModel.Completion) (after : RV32I.Semantics.State)
    (event : CoreModel.event i s = some (.retired word path after)) :
    (CoreModel.step i s).arch = after := by
  have chain := CoreModel.edge_path i s valid
  change CoreModel.architecture.Path _ (CoreModel.event i s).toList _ at chain
  rw [event] at chain
  have replay := CoreModel.path_replay _ _ _ chain
  change CoreModel.Architectural.mk after none = CoreModel.snapshot (CoreModel.step i s) at replay
  exact (congrArg CoreModel.Architectural.arch replay).symm

private theorem acceptOutcome_not_reset (s : CoreModel.State) (c : CoreModel.Completion)
    (outcome : RV32I.Semantics.Outcome) : (CoreModel.acceptOutcome s c outcome).2 ≠ some .reset := by
  cases outcome with
  | retired _ _ | trapped _ _ _ => simp [CoreModel.acceptOutcome]
  | pending p => cases p <;> simp [CoreModel.acceptOutcome]

theorem event_not_reset (i : CoreModel.Input) (s : CoreModel.State) (reset : i.reset = false) :
    CoreModel.event i s ≠ some .reset := by
  rcases s with ⟨arch,phase⟩
  cases phase with
  | fetchRequest => by_cases ha : CoreModel.aligned arch <;> simp [CoreModel.event, CoreModel.tick, reset, ha]
  | fetchResponse => cases hr : i.fetchResponse with
    | none => simp [CoreModel.event, CoreModel.tick, reset, hr]
    | some reply => cases reply <;> simp [CoreModel.event, CoreModel.tick, reset, hr]
  | execute word => simpa [CoreModel.event, CoreModel.tick, reset] using
      acceptOutcome_not_reset ⟨arch,.execute word⟩ .execute (RV32I.Semantics.step arch word)
  | dataRequest req => cases hr : i.dataService with
    | none => simp [CoreModel.event, CoreModel.tick, reset, hr]
    | some service => cases service with
      | deferred => simp [CoreModel.event, CoreModel.tick, reset, hr]
      | atomic reply => simpa [CoreModel.event, CoreModel.tick, reset, hr] using
          acceptOutcome_not_reset ⟨arch,.dataRequest req⟩ (.data .atomic req.intent reply) (req.finish reply)
  | dataResponse req => cases hr : i.dataResponse with
    | none => simp [CoreModel.event, CoreModel.tick, reset, hr]
    | some reply => simpa [CoreModel.event, CoreModel.tick, reset, hr] using
        acceptOutcome_not_reset ⟨arch,.dataResponse req⟩ (.data .deferred req.intent reply) (req.finish reply)
  | fence _ => simp [CoreModel.event, CoreModel.tick, reset, CoreModel.acceptOutcome, RV32I.Semantics.finish]
  | terminal _ => simp [CoreModel.event, CoreModel.tick, reset]

end Pinwheel.Hardware.Processor.CoreEventFacts
