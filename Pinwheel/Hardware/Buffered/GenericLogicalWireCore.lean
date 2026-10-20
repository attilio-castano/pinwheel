import Pinwheel.Hardware.Buffered.LogicalWireCore

/-! A carried logical owner and allocation are preserved over every raw clock.
The sequence offset translates only the observable finite wire sequence; epoch
and the ordinary transfer storage remain in the same logical state. -/
namespace Pinwheel.Hardware.Buffered.GenericLogicalWire
open Pinwheel.Hardware Pinwheel.Program Refinement
open LogicalWire (quiet_history sourceRun_rename sourceRun_allocation aligned_quiet_run)

variable {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}

structure Owned (actual : SramState.State) (payload : BitVec 32)
    (source : Program.Buffered.State) (offset : Nat) : Prop where
  related : RelatedSram p layout payload actual (Lifecycle.IdentityView.buffered offset source)
  sequence : offset + source.buffers.nextSequence = (actual.core .transfer).toNat + 1

theorem Owned.run_inputs {actual : SramState.State} {payload : BitVec 32}
    {source : Program.Buffered.State} {offset : Nat} (owned : Owned (p := p) (layout := layout) actual payload source offset)
    (inputs : List (Values Reactive.Input)) (history : AdministrativeHistory actual inputs) :
    Owned (p := p) (layout := layout) (actual.run inputs) payload (sourceCommands p source inputs) offset := by
  have related := owned.related.run_administrative inputs history
  rw [LogicalSession.sourceCommands_rename] at related
  have allocation := LogicalSession.sourceCommands_allocation p source inputs
  have counters := LogicalSession.administrative_counters owned.related inputs history
  refine ⟨related,?_⟩
  rw [allocation.2,counters.2]
  exact owned.sequence

theorem Owned.step {actual : SramState.State} {payload : BitVec 32}
    {source : Program.Buffered.State} {offset : Nat} (owned : Owned (p := p) (layout := layout) actual payload source offset)
    (input : Values Reactive.Input) (admitted : Administrative actual input) :
    Owned (p := p) (layout := layout) (actual.step input) payload (Program.Buffered.advance p capacity source (input .rawInputs)) offset :=
  owned.run_inputs [input] ⟨admitted,True.intro⟩

theorem Owned.quiet_step {actual : SramState.State} {payload : BitVec 32}
    {source : Program.Buffered.State} {offset : Nat} (owned : Owned (p := p) (layout := layout) actual payload source offset)
    (input : Values Reactive.Input) (quiet : SpiCircuit.Quiet input) :
    Owned (p := p) (layout := layout) (actual.step input) payload (Program.Buffered.advance p capacity source (input .rawInputs)) offset :=
  owned.step input (quiet_history actual [input] (by intro i member; rcases List.mem_singleton.mp member with rfl; exact quiet)).1

theorem Owned.quiet_run {before : SerialPackage.State} {payload : BitVec 32}
    {source : Program.Buffered.State} {offset : Nat} (owned : Owned (p := p) (layout := layout) before.controller payload source offset)
    (pins : List SerialPackage.Pins)
    (quiet : ∀ i ∈ before.commands pins, SpiCircuit.Quiet i) :
    Owned (p := p) (layout := layout) (before.run pins).controller payload (SerialSourceRead.sourceRun p source pins) offset := by
  have result := owned.run_inputs (before.commands pins) (quiet_history before.controller _ quiet)
  rw [← before.run_controller] at result
  have commands := SerialSourceRead.commands_sourceRun p before source pins
  change sourceCommands p source (before.commands pins) = SerialSourceRead.sourceRun p source pins at commands
  rw [commands] at result
  exact result

theorem aligned_quiet_run {actual : SramState.State} {logical : Transfer.State} {offset : Nat}
    (aligned : LogicalSession.Aligned actual logical offset) (inputs : List (Values Reactive.Input))
    (quiet : ∀ i ∈ inputs, SpiCircuit.Quiet i) : LogicalSession.Aligned (actual.run inputs) logical offset := by
  have free := SerialSourceRelease.free_run actual inputs ⟨aligned.phase,aligned.retained⟩ quiet
  have transfer := SerialUpload.loader_transfer_run actual inputs (by
    intro i member
    have q := quiet i member
    exact ⟨q.1,by simp [q.2],by simp [q.2]⟩)
  exact ⟨aligned.free,free.1,free.2,by rw [transfer]; exact aligned.sequence⟩

theorem free_quiet_run {before : SerialPackage.State} {logical : Transfer.State} {offset : Nat}
    (installed : InstalledSram p layout before.controller)
    (aligned : LogicalSession.Aligned before.controller logical offset)
    (pins : List SerialPackage.Pins) (quiet : ∀ i ∈ before.commands pins, SpiCircuit.Quiet i) :
    InstalledSram p layout (before.run pins).controller ∧
      LogicalSession.Aligned (before.run pins).controller logical offset := by
  rw [before.run_controller]
  exact ⟨installed.run (before.commands pins) (by
    intro i member
    have q := quiet i member
    simp [SramExecution.ExecutingInput,SharedBranches.Runtime,q.1,q.2]),
    aligned_quiet_run aligned _ quiet⟩

theorem start_owned {actual : SramState.State} {logical : Transfer.State} {offset : Nat}
    (installed : InstalledSram p layout actual)
    (aligned : LogicalSession.Aligned actual logical offset) (input : Values Reactive.Input)
    (starting : Reactive.starting.eval input actual.core = 1) :
    Owned (p := p) (layout := layout) (actual.step input) (input .txData) (LogicalSession.started p actual input logical) offset := by
  have facts := SpiCircuit.starting_facts input actual.core starting
  have allocation := LogicalSession.started_allocation (p := p) aligned input facts.txLength facts.rxCapacity
  have accepted : Sram.starting.eval (actual.inputs input) actual.registers = 1 := by
    rw [Lifecycle.starting_effective,Lifecycle.starting_direct]
    exact starting
  have transfer := Lifecycle.start_transfer_sequence actual input accepted
  refine ⟨LogicalSession.start_related installed aligned input starting,?_⟩
  rw [allocation.2,transfer]
  have sequence := aligned.sequence
  omega

end Pinwheel.Hardware.Buffered.GenericLogicalWire
