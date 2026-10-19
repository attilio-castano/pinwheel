import Pinwheel.Hardware.Buffered.GenericEntryTransfer

/-! Terminal entry preserves the computed partial transfer and clears every
packed execution cursor/cache field, for completion, timeout and fault. -/
namespace Pinwheel.Hardware.Buffered.Refinement
open Pinwheel.Hardware Pinwheel.Program

theorem entry_stopped {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {payload : BitVec 32} {r : Values Reactive.Register} {s : Program.Buffered.State}
    {e : Transfer.Execution} (h : Common p layout payload r s e)
    (i : Values Reactive.Input) (quiet : SpiCircuit.Quiet i)
    (pc : Program.Buffered.PC) (instruction : Program.Buffered.Instruction) (slots : Vector Bool 16)
    (within : pc.val < p.code.span) (fetch : p.fetch pc = some instruction)
    (slot : s.buffers.slot = .running e) (outcome : Transfer.Outcome)
    (stops : GenericEffects.finalOutcome instruction e (r .stage2) = some outcome)
    (phase : (if Reactive.entryTimeout.eval i r = 1 then 6
      else if Reactive.entryComplete.eval i r = 1 then 5 else 7) = stopPhase outcome)
    (scratch : GenericPhase.Scratch (Reactive.entryScratch.eval i r)
      (Engine.Reactive.capture slots (GenericEntry.capture instruction) (r .stage2)))
    (consuming : Reactive.consuming.eval i r =
      BitVec.ofBool (GenericEffects.result instruction e (r .stage2)).consume)
    (appending : Reactive.appending.eval i r =
      BitVec.ofBool (GenericEffects.result instruction e (r .stage2)).receive)
    (sample : (GenericEffects.result instruction e (r .stage2)).receive = true →
      (Reactive.sampled.eval i r).getLsbD 0 =
      (GenericEffects.result instruction e (r .stage2)).sample) :
    Stopped p layout payload (GenericPhase.entryStopTick i r)
      (GenericEntry.entered p s pc slots (r .stage2))
      ((GenericEffects.result instruction e (r .stage2)).execution e) outcome := by
  rw [GenericEntry.entered_final p layout s e pc within instruction fetch slots
    (r .stage2) slot h.owner]
  simp only [GenericEntry.finalState, stops]
  have terminal := SpiInterpreter.terminal_running p capacity
    (GenericEffects.replaceExecution
      (GenericEntry.coreState p s pc instruction slots (r .stage2))
      ((GenericEffects.result instruction e (r .stage2)).execution e))
    ((GenericEffects.result instruction e (r .stage2)).execution e) outcome rfl h.owner
  refine ⟨h.entryStopResult i quiet pc instruction slots outcome scratch consuming appending sample,
    ?_, ?_, phase, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · rw [terminal]
  · rw [terminal]
    cases outcome <;> rfl

end Pinwheel.Hardware.Buffered.Refinement
