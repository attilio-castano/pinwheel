import Pinwheel.Hardware.Buffered.GenericStartFrame

/-! Static installation, admitted operands, and the first instruction's actual
entry effects establish the generic common state representation. -/
namespace Pinwheel.Hardware.Buffered.GenericStart
open Pinwheel.Hardware Pinwheel.Program Pinwheel.Engine.Reactive

def updated (p : Program.Buffered.Program) (instruction : Program.Buffered.Instruction)
    (i : Values Reactive.Input) (r : Values Reactive.Register) : Program.Buffered.State :=
  GenericEffects.replaceExecution
    (GenericEntry.coreState p (base p r i) 0 instruction (Vector.replicate 16 false) (r .stage2))
    ((GenericEffects.result instruction (execution r i) (r .stage2)).execution (execution r i))

theorem common_running {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    (instruction : Program.Buffered.Instruction)
    (i : Values Reactive.Input) (r : Values Reactive.Register)
    (installed : Installed p layout r)
    (starting : Reactive.starting.eval i r = 1)
    (word : Reactive.entryWord.eval i r = GenericEncoding.encode instruction)
    (flags : GenericEntryFlags.Flags instruction (execution r i) (r .stage2) i r)
    (nonterminal : (GenericEncoding.instruction instruction).kind ≠ 3 ∧
      (GenericEncoding.instruction instruction).kind ≠ 4)
    (success : (GenericEffects.result instruction (execution r i) (r .stage2)).outcome = none) :
    Refinement.Common p layout (i .txData) (GenericPhase.runEntryTick i r)
      (updated p instruction i r)
      ((GenericEffects.result instruction (execution r i) (r .stage2)).execution (execution r i)) := by
  have available : ∀ pin enable invert action,
      instruction.operation = .shift pin enable invert action → 0 < (i .txLength).toNat := by
    intro pin enable invert action operation
    simpa [execution, SpiStart.request] using
      GenericEffects.result_success_shift_available instruction (execution r i) (r .stage2)
        pin enable invert action operation success
  refine ⟨installed.count, installed.span, installed.idleLevels, installed.idleEnabled,
    installed.image, (SpiCircuit.starting_facts i r starting).valid,
    datapath_result instruction i r starting word flags.consuming flags.appending, rfl, ?_, ?_⟩
  · change (GenericEntry.core instruction p.idle (base p r i).core.pins 0
      (Program.Buffered.txBit (base p r i)) (Vector.replicate 16 false) (r .stage2)).pins = _
    rw [GenericEntry.core_pins instruction p.idle (base p r i).core.pins 0
      (Program.Buffered.txBit (base p r i)) (Vector.replicate 16 false) (r .stage2) nonterminal]
    exact (entry_pins p instruction i r starting word available).symm
  · exact scratch instruction i r starting word flags.running

theorem common_stopped {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    (instruction : Program.Buffered.Instruction)
    (i : Values Reactive.Input) (r : Values Reactive.Register)
    (installed : Installed p layout r)
    (starting : Reactive.starting.eval i r = 1)
    (word : Reactive.entryWord.eval i r = GenericEncoding.encode instruction)
    (flags : GenericEntryFlags.Flags instruction (execution r i) (r .stage2) i r)
    (outcome : Transfer.Outcome) :
    Refinement.Common p layout (i .txData) (GenericPhase.entryStopTick i r)
      (Program.Buffered.terminal p Refinement.capacity (updated p instruction i r) outcome)
      ((GenericEffects.result instruction (execution r i) (r .stage2)).execution (execution r i)) := by
  refine ⟨installed.count, installed.span, installed.idleLevels, installed.idleEnabled,
    installed.image, (SpiCircuit.starting_facts i r starting).valid,
    stop_datapath_result instruction i r starting word flags.consuming flags.appending,
    rfl, ?_, scratch instruction i r starting word flags.running⟩
  change p.idle = ⟨r .idleLevels, r .idleEnabled⟩
  rw [installed.idleLevels, installed.idleEnabled]

end Pinwheel.Hardware.Buffered.GenericStart
