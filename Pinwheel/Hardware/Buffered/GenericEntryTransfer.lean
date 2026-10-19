import Pinwheel.Hardware.Buffered.GenericEntryCore
import Pinwheel.Hardware.Buffered.GenericEffects
import Pinwheel.Hardware.Buffered.GenericEffectFacts
import Pinwheel.Hardware.Buffered.GenericDatapath

/-! The source entry event is the existing fetch interpreter followed by the
existing owned buffer effects and settlement. The summaries below are derived
equations for that event. -/
namespace Pinwheel.Hardware.Buffered.GenericEntry
open Pinwheel.Hardware Pinwheel.Program Pinwheel.Engine.Reactive

def coreState (p : Program.Buffered.Program) (s : Program.Buffered.State)
    (pc : Program.Buffered.PC) (instruction : Program.Buffered.Instruction)
    (slots : Vector Bool 16) (sampled : Inputs) : Program.Buffered.State :=
  {s with core := core instruction p.idle s.core.pins pc (Program.Buffered.txBit s) slots sampled}

def entered (p : Program.Buffered.Program) (s : Program.Buffered.State)
    (pc : Program.Buffered.PC) (slots : Vector Bool 16) (sampled : Inputs) : Program.Buffered.State :=
  Program.Buffered.settle p Refinement.capacity
    (Program.Buffered.entryEffects p Refinement.capacity
      {s with core := Fetch.enter (Program.Buffered.lower p s) pc slots sampled} pc sampled)

theorem entered_eq (p : Program.Buffered.Program) (layout : GenericCertificate.Layout p)
    (s : Program.Buffered.State) (e : Transfer.Execution) (pc : Program.Buffered.PC)
    (within : pc.val < p.code.span) (instruction : Program.Buffered.Instruction)
    (fetch : p.fetch pc = some instruction) (slots : Vector Bool 16) (sampled : Inputs)
    (running : s.buffers.slot = .running e) (owner : e.request.identity = s.owner) :
    entered p s pc slots sampled =
      Program.Buffered.settle p Refinement.capacity
        (GenericEffects.applyResult p Refinement.capacity
          (coreState p s pc instruction slots sampled) e
          (GenericEffects.result instruction e sampled)) := by
  unfold entered
  rw [source_enter p layout s pc within instruction fetch slots sampled]
  exact congrArg (Program.Buffered.settle p Refinement.capacity)
    (GenericEffects.entryEffects_result p Refinement.capacity
      (coreState p s pc instruction slots sampled) e pc instruction sampled
      (core_not_fault instruction p.idle s.core.pins pc (Program.Buffered.txBit s) slots sampled)
      fetch running owner)

theorem settle_applyResult_busy (p : Program.Buffered.Program) (s : Program.Buffered.State)
    (e : Transfer.Execution) (result : GenericEffects.Result)
    (active : busy s.core = true) (owner : e.request.identity = s.owner) :
    Program.Buffered.settle p Refinement.capacity
      (GenericEffects.applyResult p Refinement.capacity s e result) =
      GenericEffects.applyResult p Refinement.capacity s e result := by
  cases equality : result.outcome
  case none =>
    simp only [GenericEffects.applyResult, equality]
    exact GenericEffects.settle_busy p Refinement.capacity _ active
  case some outcome =>
    simp only [GenericEffects.applyResult, equality]
    exact GenericEffects.settle_terminal_running p Refinement.capacity _
      (result.execution e) outcome rfl owner

def finalState (p : Program.Buffered.Program) (s : Program.Buffered.State)
    (e : Transfer.Execution) (pc : Program.Buffered.PC) (instruction : Program.Buffered.Instruction)
    (slots : Vector Bool 16) (sampled : Inputs) : Program.Buffered.State :=
  let updated := GenericEffects.replaceExecution (coreState p s pc instruction slots sampled)
    ((GenericEffects.result instruction e sampled).execution e)
  match GenericEffects.finalOutcome instruction e sampled with
  | none => updated
  | some outcome => Program.Buffered.terminal p Refinement.capacity updated outcome

theorem entered_final (p : Program.Buffered.Program) (layout : GenericCertificate.Layout p)
    (s : Program.Buffered.State) (e : Transfer.Execution) (pc : Program.Buffered.PC)
    (within : pc.val < p.code.span) (instruction : Program.Buffered.Instruction)
    (fetch : p.fetch pc = some instruction) (slots : Vector Bool 16) (sampled : Inputs)
    (running : s.buffers.slot = .running e) (owner : e.request.identity = s.owner) :
    entered p s pc slots sampled = finalState p s e pc instruction slots sampled := by
  rw [entered_eq p layout s e pc within instruction fetch slots sampled running owner]
  cases operation : instruction.operation
  case halt =>
    simp [GenericEffects.applyResult, GenericEffects.result, GenericEffects.finalOutcome,
      operation, finalState, Program.Buffered.settle, GenericEffects.replaceExecution,
      coreState, core, control]
  case fault reason =>
    simp only [GenericEffects.applyResult, GenericEffects.result, GenericEffects.finalOutcome,
      operation, finalState]
    exact GenericEffects.settle_terminal_running p Refinement.capacity _ _
      reason.outcome rfl owner
  all_goals rw [settle_applyResult_busy p (coreState p s pc instruction slots sampled) e _
    (by simp [coreState, core, control, busy, operation]) owner]
  all_goals simp only [GenericEffects.applyResult, finalState,
    GenericEffects.finalOutcome, operation]
  all_goals rfl


end Pinwheel.Hardware.Buffered.GenericEntry

namespace Pinwheel.Hardware.Buffered.Refinement
open Pinwheel.Hardware Pinwheel.Program

theorem Datapath.entryResult {payload : BitVec 32} {r : Values Reactive.Register}
    {e : Transfer.Execution} (h : Datapath payload r e)
    (i : Values Reactive.Input) (quiet : SpiCircuit.Quiet i)
    (instruction : Program.Buffered.Instruction)
    (consuming : Reactive.consuming.eval i r =
      BitVec.ofBool (GenericEffects.result instruction e (r .stage2)).consume)
    (appending : Reactive.appending.eval i r =
      BitVec.ofBool (GenericEffects.result instruction e (r .stage2)).receive)
    (sample : (Reactive.sampled.eval i r).getLsbD 0 =
      (GenericEffects.result instruction e (r .stage2)).sample) :
    Datapath payload (GenericPhase.runEntryTick i r)
      ((GenericEffects.result instruction e (r .stage2)).execution e) := by
  have updated := h.runEntryTick i quiet _ _ consuming appending
    (GenericEffects.result_bounds instruction e (r .stage2)).1
    (GenericEffects.result_bounds instruction e (r .stage2)).2
  simpa only [entryExecution, sample, GenericEffects.Result.execution] using updated

theorem Common.entryResult {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {payload : BitVec 32} {r : Values Reactive.Register} {s : Program.Buffered.State}
    {e : Transfer.Execution} (h : Common p layout payload r s e)
    (i : Values Reactive.Input) (quiet : SpiCircuit.Quiet i)
    (pc : Program.Buffered.PC) (instruction : Program.Buffered.Instruction) (slots : Vector Bool 16)
    (slot : s.buffers.slot = .running e)
    (word : Reactive.entryWord.eval i r = GenericEncoding.encode instruction)
    (running : Reactive.runEntry.eval i r = 1)
    (scratch : GenericPhase.Scratch (Reactive.exitScratch.eval i r) slots)
    (nonterminal : (GenericEncoding.instruction instruction).kind ≠ 3 ∧
      (GenericEncoding.instruction instruction).kind ≠ 4)
    (available : ∀ pin enable invert action,
      instruction.operation = .shift pin enable invert action → e.txConsumed < e.request.tx.length)
    (consuming : Reactive.consuming.eval i r =
      BitVec.ofBool (GenericEffects.result instruction e (r .stage2)).consume)
    (appending : Reactive.appending.eval i r =
      BitVec.ofBool (GenericEffects.result instruction e (r .stage2)).receive)
    (sample : (Reactive.sampled.eval i r).getLsbD 0 =
      (GenericEffects.result instruction e (r .stage2)).sample) :
    Common p layout payload (GenericPhase.runEntryTick i r)
      (GenericEffects.replaceExecution
        (GenericEntry.coreState p s pc instruction slots (r .stage2))
        ((GenericEffects.result instruction e (r .stage2)).execution e))
      ((GenericEffects.result instruction e (r .stage2)).execution e) := by
  have notStarting := (SpiCircuit.quiet_controls i r quiet).2.2.1
  refine ⟨h.count, h.span, h.idleLevels, h.idleEnabled, h.image, h.valid,
    h.data.entryResult i quiet instruction consuming appending sample, h.owner, ?_, ?_⟩
  · change (GenericEntry.core instruction p.idle s.core.pins pc
      (Program.Buffered.txBit s) slots (r .stage2)).pins = _
    rw [GenericEntry.core_pins instruction p.idle s.core.pins pc
      (Program.Buffered.txBit s) slots (r .stage2) nonterminal]
    exact (entry_pins_source h slot i instruction word notStarting available).symm
  · exact entry_scratch i r instruction slots word running notStarting scratch

theorem Datapath.entryStopResult {payload : BitVec 32} {r : Values Reactive.Register}
    {e : Transfer.Execution} (h : Datapath payload r e)
    (i : Values Reactive.Input) (quiet : SpiCircuit.Quiet i)
    (instruction : Program.Buffered.Instruction)
    (consuming : Reactive.consuming.eval i r =
      BitVec.ofBool (GenericEffects.result instruction e (r .stage2)).consume)
    (appending : Reactive.appending.eval i r =
      BitVec.ofBool (GenericEffects.result instruction e (r .stage2)).receive)
    (sample : (GenericEffects.result instruction e (r .stage2)).receive = true →
      (Reactive.sampled.eval i r).getLsbD 0 =
      (GenericEffects.result instruction e (r .stage2)).sample) :
    Datapath payload (GenericPhase.entryStopTick i r)
      ((GenericEffects.result instruction e (r .stage2)).execution e) := by
  have updated := h.entryStopTick i quiet _ _ consuming appending
    (GenericEffects.result_bounds instruction e (r .stage2)).1
    (GenericEffects.result_bounds instruction e (r .stage2)).2
  cases receive : (GenericEffects.result instruction e (r .stage2)).receive
  · simpa only [entryExecution, GenericEffects.Result.execution, receive, Bool.false_eq_true,
      ↓reduceIte] using updated
  · simpa only [entryExecution, sample receive, GenericEffects.Result.execution] using updated

theorem Common.entryStopResult {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {payload : BitVec 32} {r : Values Reactive.Register} {s : Program.Buffered.State}
    {e : Transfer.Execution} (h : Common p layout payload r s e)
    (i : Values Reactive.Input) (quiet : SpiCircuit.Quiet i)
    (pc : Program.Buffered.PC) (instruction : Program.Buffered.Instruction) (slots : Vector Bool 16)
    (outcome : Transfer.Outcome)
    (scratch : GenericPhase.Scratch (Reactive.entryScratch.eval i r)
      (Engine.Reactive.capture slots (GenericEntry.capture instruction) (r .stage2)))
    (consuming : Reactive.consuming.eval i r =
      BitVec.ofBool (GenericEffects.result instruction e (r .stage2)).consume)
    (appending : Reactive.appending.eval i r =
      BitVec.ofBool (GenericEffects.result instruction e (r .stage2)).receive)
    (sample : (GenericEffects.result instruction e (r .stage2)).receive = true →
      (Reactive.sampled.eval i r).getLsbD 0 =
      (GenericEffects.result instruction e (r .stage2)).sample) :
    Common p layout payload (GenericPhase.entryStopTick i r)
      (Program.Buffered.terminal p capacity
        (GenericEffects.replaceExecution
          (GenericEntry.coreState p s pc instruction slots (r .stage2))
          ((GenericEffects.result instruction e (r .stage2)).execution e)) outcome)
      ((GenericEffects.result instruction e (r .stage2)).execution e) := by
  refine ⟨h.count, h.span, h.idleLevels, h.idleEnabled, h.image, h.valid,
    h.data.entryStopResult i quiet instruction consuming appending sample, h.owner, ?_, scratch⟩
  change p.idle = ⟨r .idleLevels, r .idleEnabled⟩
  rw [h.idleLevels, h.idleEnabled]

end Pinwheel.Hardware.Buffered.Refinement
