import Pinwheel.Hardware.Buffered.GenericEntryTransfer
import Pinwheel.Hardware.Buffered.GenericEntryAt
import Pinwheel.Hardware.Buffered.GenericEffectFacts

/-! A successful entry constructs the full generic running invariant. Address,
cached operands, pins, scratch and owned data are all derived separately. -/
namespace Pinwheel.Hardware.Buffered.Refinement
open Pinwheel.Hardware Pinwheel.Program

theorem entry_running_tick {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {payload : BitVec 32} {r : Values Reactive.Register} {s : Program.Buffered.State}
    {e : Transfer.Execution} (h : Common p layout payload r s e)
    (i : Values Reactive.Input) (quiet : SpiCircuit.Quiet i)
    (pc : Program.Buffered.PC) (instruction : Program.Buffered.Instruction) (slots : Vector Bool 16)
    (atEntry : EntryAt layout.map i r pc)
    (within : pc.val < p.code.span) (fetch : p.fetch pc = some instruction)
    (slot : s.buffers.slot = .running e) (retained : r .retained = 0)
    (first : s.samplerFirst = i .rawInputs) (second : s.samplerSecond = r .stage1)
    (running : Reactive.runEntry.eval i r = 1)
    (scratch : GenericPhase.Scratch (Reactive.exitScratch.eval i r) slots)
    (nonterminal : (GenericEncoding.instruction instruction).kind ≠ 3 ∧
      (GenericEncoding.instruction instruction).kind ≠ 4)
    (success : (GenericEffects.result instruction e (r .stage2)).outcome = none)
    (consuming : Reactive.consuming.eval i r =
      BitVec.ofBool (GenericEffects.result instruction e (r .stage2)).consume)
    (appending : Reactive.appending.eval i r =
      BitVec.ofBool (GenericEffects.result instruction e (r .stage2)).receive)
    (sample : (Reactive.sampled.eval i r).getLsbD 0 =
      (GenericEffects.result instruction e (r .stage2)).sample) :
    Running p layout payload (GenericPhase.runEntryTick i r)
      (GenericEffects.replaceExecution
        (GenericEntry.coreState p s pc instruction slots (r .stage2))
        ((GenericEffects.result instruction e (r .stage2)).execution e))
      ((GenericEffects.result instruction e (r .stage2)).execution e) instruction pc := by
  have word := atEntry.word within instruction fetch h.image
  have branch := atEntry.branch within instruction fetch h.image
  have available := fun pin enable invert action operation =>
    GenericEffects.result_success_shift_available instruction e (r .stage2)
      pin enable invert action operation success
  refine ⟨h.entryResult i quiet pc instruction slots slot word running scratch nonterminal
      available consuming appending sample,
    rfl, within, fetch, ?_, ?_, ?_, Caches.runEntryTick p layout i r instruction word branch,
    entry_control i r instruction pc word nonterminal, retained, first, second⟩
  · exact atEntry.coordinates
  · change (Reactive.entryVirtual.eval i r).extractLsb' 0 10 = BitVec.ofNat 10 pc.val
    rw [atEntry.virtualPC, ← BitVec.setWidth_eq_extractLsb' (by decide : 10 ≤ 11),
      BitVec.setWidth_ofNat_of_le (by decide : 10 ≤ 11)]
  · change (Reactive.entryControl.eval i r).extractLsb' 0 22 = _
    simp only [Reactive.entryControl, Expr.eval,
      entryRecord layout i r pc atEntry.entering atEntry.address h.image]
    apply BitVec.eq_of_getLsbD_eq
    intro k bound
    simp [bound, show k < 24 by omega]
  done

theorem entry_running {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {payload : BitVec 32} {r : Values Reactive.Register} {s : Program.Buffered.State}
    {e : Transfer.Execution} (h : Common p layout payload r s e)
    (i : Values Reactive.Input) (quiet : SpiCircuit.Quiet i)
    (pc : Program.Buffered.PC) (instruction : Program.Buffered.Instruction) (slots : Vector Bool 16)
    (atEntry : EntryAt layout.map i r pc)
    (within : pc.val < p.code.span) (fetch : p.fetch pc = some instruction)
    (slot : s.buffers.slot = .running e) (retained : r .retained = 0)
    (first : s.samplerFirst = i .rawInputs) (second : s.samplerSecond = r .stage1)
    (running : Reactive.runEntry.eval i r = 1)
    (scratch : GenericPhase.Scratch (Reactive.exitScratch.eval i r) slots)
    (nonterminal : (GenericEncoding.instruction instruction).kind ≠ 3 ∧
      (GenericEncoding.instruction instruction).kind ≠ 4)
    (success : (GenericEffects.result instruction e (r .stage2)).outcome = none)
    (consuming : Reactive.consuming.eval i r =
      BitVec.ofBool (GenericEffects.result instruction e (r .stage2)).consume)
    (appending : Reactive.appending.eval i r =
      BitVec.ofBool (GenericEffects.result instruction e (r .stage2)).receive)
    (sample : (Reactive.sampled.eval i r).getLsbD 0 =
      (GenericEffects.result instruction e (r .stage2)).sample) :
    Running p layout payload (GenericPhase.runEntryTick i r)
      (GenericEntry.entered p s pc slots (r .stage2))
      ((GenericEffects.result instruction e (r .stage2)).execution e) instruction pc := by
  rw [GenericEntry.entered_eq p layout s e pc within instruction fetch slots (r .stage2)
    slot h.owner]
  simp only [GenericEffects.applyResult, success]
  rw [GenericEffects.settle_busy p capacity _
    (GenericEntry.core_busy instruction p.idle s.core.pins pc
      (Program.Buffered.txBit s) slots (r .stage2) nonterminal)]
  exact entry_running_tick h i quiet pc instruction slots atEntry within fetch slot retained
    first second running scratch nonterminal success consuming appending sample

end Pinwheel.Hardware.Buffered.Refinement
