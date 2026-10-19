import Pinwheel.Hardware.Buffered.GenericEntryRunning
import Pinwheel.Hardware.Buffered.GenericEntryStopped
import Pinwheel.Hardware.Buffered.GenericEntryFlags
import Pinwheel.Hardware.Buffered.GenericSample
import Pinwheel.Hardware.Buffered.GenericEntryFacts

/-! All eight legal instruction entries preserve the complete execution
relation, including terminal instructions with ignored data operands. -/
namespace Pinwheel.Hardware.Buffered.Refinement
open Pinwheel.Hardware Pinwheel.Program

theorem entry_scratch_all (i : Values Reactive.Input) (r : Values Reactive.Register)
    (instruction : Program.Buffered.Instruction) (slots : Vector Bool 16)
    (word : Reactive.entryWord.eval i r = GenericEncoding.encode instruction)
    (running : Reactive.runEntry.eval i r = BitVec.ofBool (GenericEntryFlags.runs instruction))
    (notStarting : Reactive.starting.eval i r = 0)
    (scratch : GenericPhase.Scratch (Reactive.exitScratch.eval i r) slots) :
    GenericPhase.Scratch (Reactive.entryScratch.eval i r)
      (Engine.Reactive.capture slots (GenericEntry.capture instruction) (r .stage2)) := by
  cases active : GenericEntryFlags.runs instruction
  case false =>
    have noCapture : GenericEntry.capture instruction = none := by
      cases operation : instruction.operation
      all_goals simp [GenericEntryFlags.runs, operation] at active
      all_goals simp [GenericEntry.capture, operation]
    simpa only [Reactive.entryScratch, Expr.eval, running, active, BitVec.ofBool_false,
      notStarting, show (0 : BitVec 1) ≠ 1 from by decide, ↓reduceIte,
      noCapture, Engine.Reactive.capture] using scratch
  case true =>
    exact entry_scratch i r instruction slots word (by rw [running, active]; rfl)
      notStarting scratch

theorem valid_entry {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {payload : BitVec 32} {r : Values Reactive.Register} {s : Program.Buffered.State}
    {e : Transfer.Execution} (h : Common p layout payload r s e)
    (i : Values Reactive.Input) (quiet : SpiCircuit.Quiet i)
    (pc : Program.Buffered.PC) (instruction : Program.Buffered.Instruction) (slots : Vector Bool 16)
    (atEntry : EntryAt layout.map i r pc)
    (within : pc.val < p.code.span) (fetch : p.fetch pc = some instruction)
    (slot : s.buffers.slot = .running e) (retained : r .retained = 0)
    (first : s.samplerFirst = i .rawInputs) (second : s.samplerSecond = r .stage1)
    (scratch : GenericPhase.Scratch (Reactive.exitScratch.eval i r) slots) :
    Related p layout payload (Reactive.circuit.step i r)
      (GenericEntry.entered p s pc slots (r .stage2)) := by
  have controls := SpiCircuit.quiet_controls i r quiet
  have executing : SramExecution.ExecutingInput i := by
    simp [SramExecution.ExecutingInput, SharedBranches.Runtime, quiet.1, quiet.2]
  have word := atEntry.word within instruction fetch h.image
  have flags := GenericEntryFlags.flags instruction e (r .stage2) payload i r quiet
    atEntry.entering (atEntry.legal within h) word h.data
  have sampled := GenericSample.sampled_on_receive instruction e i r word
  cases stops : GenericEffects.finalOutcome instruction e (r .stage2)
  case none =>
    have success := GenericEntryFlags.final_none instruction e (r .stage2) stops
    have running : Reactive.runEntry.eval i r = 1 := by rw [flags.running, success.1]; rfl
    have stopping : Reactive.stopping.eval i r = 0 := by
      simpa only [stops, Option.isSome_none, BitVec.ofBool_false] using flags.stopping
    rw [GenericPhase.run_entry_step i r executing controls.2.2.2.2.2
      atEntry.entering stopping running]
    refine Or.inl ⟨(GenericEffects.result instruction e (r .stage2)).execution e,
      instruction, pc, ?_⟩
    exact entry_running h i quiet pc instruction slots atEntry within fetch slot retained
      first second running scratch ⟨success.2.1, success.2.2.1⟩ success.2.2.2
      flags.consuming flags.appending
      ((GenericSample.sampled instruction i r word success.1).trans
        (GenericEffects.result_sample instruction e (r .stage2)).symm)
  case some outcome =>
    have stopping : Reactive.stopping.eval i r = 1 := by
      simpa only [stops, Option.isSome_some, BitVec.ofBool_true] using flags.stopping
    rw [GenericPhase.entry_stop_step i r executing controls.2.2.2.2.2
      atEntry.entering stopping flags.heldTimeout]
    refine Or.inr ⟨(GenericEffects.result instruction e (r .stage2)).execution e, outcome, ?_⟩
    exact entry_stopped h i quiet pc instruction slots within fetch slot outcome stops
      (by rw [flags.timeout, flags.complete];
          exact GenericEntryFlags.final_some_phase instruction e (r .stage2) outcome stops)
      (entry_scratch_all i r instruction slots word flags.running controls.2.2.1 scratch)
      flags.consuming flags.appending sampled

end Pinwheel.Hardware.Buffered.Refinement
