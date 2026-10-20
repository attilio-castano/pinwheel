import Pinwheel.Hardware.Buffered.LogicalSessionTrace

/-! Abandoning any admitted execution prefix uses ordinary transfer reset at
the actual reset cut. No completion, retained bit or RELEASE is required.
Quiet free clocks preserve the carried logical owner allocator and wire offset. -/
namespace Pinwheel.Hardware.Buffered.LogicalSession
open Pinwheel.Hardware Pinwheel.Program Refinement

structure ExecutionPrefix where
  start : Values Reactive.Input
  body : List (Values Reactive.Input)

def ExecutionPrefix.finished (value : ExecutionPrefix) (actual : SramState.State) : SramState.State :=
  (actual.step value.start).run value.body

def ExecutionPrefix.source (value : ExecutionPrefix) (p : Program.Buffered.Program)
    (actual : SramState.State) (logical : Transfer.State) : Program.Buffered.State :=
  sourceCommands p (started p actual value.start logical) value.body

def ExecutionPrefix.inputs (value : ExecutionPrefix) : List (Values Reactive.Input) :=
  @value.start :: value.body

structure PrefixAdmitted (actual : SramState.State) (value : ExecutionPrefix) : Prop where
  starting : Reactive.starting.eval value.start actual.core = 1
  body : AdministrativeHistory (actual.step value.start) value.body

theorem prefix_related {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {actual : SramState.State} {logical : Transfer.State} {offset : Nat}
    (installed : InstalledSram p layout actual) (aligned : Aligned actual logical offset)
    {value : ExecutionPrefix} (admitted : PrefixAdmitted actual value) :
    RelatedSram p layout (value.start .txData) (value.finished actual)
      (Lifecycle.IdentityView.buffered offset (value.source p actual logical)) := by
  simpa only [sourceCommands_rename, ExecutionPrefix.finished, ExecutionPrefix.source] using
    (start_related installed aligned value.start admitted.starting).run_administrative value.body admitted.body

theorem prefix_allocation {p : Program.Buffered.Program} {actual : SramState.State}
    {logical : Transfer.State} {offset : Nat} (aligned : Aligned actual logical offset)
    {value : ExecutionPrefix} (admitted : PrefixAdmitted actual value) :
    (value.source p actual logical).buffers.epoch = logical.epoch ∧
      (value.source p actual logical).buffers.nextSequence = logical.nextSequence + 1 := by
  exact (sourceCommands_allocation p (started p actual value.start logical) value.body).imp
    (fun h => h.trans (started_allocation aligned value.start
      (SpiCircuit.starting_facts _ _ admitted.starting).txLength
      (SpiCircuit.starting_facts _ _ admitted.starting).rxCapacity).1)
    (fun h => h.trans (started_allocation aligned value.start
      (SpiCircuit.starting_facts _ _ admitted.starting).txLength
      (SpiCircuit.starting_facts _ _ admitted.starting).rxCapacity).2)

private theorem generation_executing (actual : SramState.State) (i : Values Reactive.Input)
    (executing : SramExecution.ExecutingInput i) :
    (actual.step i).core .generation = actual.core .generation := by
  have committing : Sram.committing.eval (actual.inputs i) actual.registers = 0 := by
    rw [Lifecycle.committing_effective, Lifecycle.effective_runtime actual i executing.1]
    simp [Reactive.committing, Reactive.both, Reactive.cmd, Expr.eval, executing.1.2.1]
  simp [Lifecycle.generation_step, executing.2.1, executing.2.2, committing]

theorem prefix_counters {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {actual : SramState.State} {logical : Transfer.State} {offset : Nat}
    (installed : InstalledSram p layout actual) (aligned : Aligned actual logical offset)
    {value : ExecutionPrefix} (admitted : PrefixAdmitted actual value) :
    (value.finished actual).core .generation = actual.core .generation ∧
      ((value.finished actual).core .transfer).toNat = (actual.core .transfer).toNat + 1 := by
  have body := administrative_counters
    (start_related installed aligned value.start admitted.starting) value.body admitted.body
  have accepted : Sram.starting.eval (actual.inputs value.start) actual.registers = 1 := by
    rw [Lifecycle.starting_effective, Lifecycle.starting_direct]
    exact admitted.starting
  exact ⟨body.1.trans (generation_executing actual value.start
      (SpiAdmission.starting_controls _ _ admitted.starting).executing),
    (congrArg BitVec.toNat body.2).trans (Lifecycle.start_transfer_sequence actual value.start accepted)⟩

theorem quiet_counters_step (actual : SramState.State) (i : Values Reactive.Input)
    (quiet : SpiCircuit.Quiet i) :
    (actual.step i).core .generation = actual.core .generation ∧
      (actual.step i).core .transfer = actual.core .transfer := by
  exact ⟨generation_executing actual i (by
      simp [SramExecution.ExecutingInput, SharedBranches.Runtime, quiet.1, quiet.2]),
    LifecycleUpload.transfer_step actual i ⟨quiet.1, by simp [quiet.2], by simp [quiet.2]⟩⟩

theorem quiet_counters_run (actual : SramState.State) (inputs : List (Values Reactive.Input))
    (quiet : ∀ i ∈ inputs, SpiCircuit.Quiet i) :
    (actual.run inputs).core .generation = actual.core .generation ∧
      (actual.run inputs).core .transfer = actual.core .transfer := by
  induction inputs generalizing actual
  case nil => exact ⟨rfl, rfl⟩
  case cons i rest ih =>
    have first := quiet_counters_step actual i (quiet i (by simp))
    have tail := ih (actual.step i) (fun j member => quiet j (List.mem_cons_of_mem _ member))
    exact ⟨tail.1.trans first.1, tail.2.trans first.2⟩

theorem Aligned.quiet_step {actual : SramState.State} {logical : Transfer.State} {offset : Nat}
    (aligned : Aligned actual logical offset) (i : Values Reactive.Input) (quiet : SpiCircuit.Quiet i) :
    Aligned (actual.step i) logical offset := by
  have idle := LifecycleUpload.idle_step actual i
    ⟨quiet.1, by simp [quiet.2], by simp [quiet.2]⟩ aligned.phase aligned.retained
  exact ⟨aligned.free, idle.1, idle.2, by rw [(quiet_counters_step actual i quiet).2]; exact aligned.sequence⟩

theorem Aligned.quiet_run {actual : SramState.State} {logical : Transfer.State} {offset : Nat}
    (aligned : Aligned actual logical offset) (inputs : List (Values Reactive.Input))
    (quiet : ∀ i ∈ inputs, SpiCircuit.Quiet i) : Aligned (actual.run inputs) logical offset := by
  induction inputs generalizing actual
  case nil => exact aligned
  case cons i rest ih =>
    exact ih (aligned.quiet_step i (quiet i (by simp)))
      (fun j member => quiet j (List.mem_cons_of_mem _ member))

structure AbortedRound where
  execution : ExecutionPrefix
  reload : I2cReloadSession.Batch

def AbortedRound.after (value : AbortedRound) (actual : SramState.State) : SramState.State :=
  value.reload.after (value.execution.finished actual)

def AbortedRound.logicalAfter (value : AbortedRound) (p : Program.Buffered.Program)
    (actual : SramState.State) (logical : Transfer.State) : Transfer.State :=
  (Transfer.step capacity (value.execution.source p actual logical).buffers .reset).state

def AbortedRound.inputs (value : AbortedRound) : List (Values Reactive.Input) :=
  value.execution.inputs ++ value.reload.inputs

structure AbortAdmitted (actual : SramState.State) (value : AbortedRound) : Prop where
  execution : PrefixAdmitted actual value.execution
  reload : I2cReloadSession.Admitted (value.execution.finished actual) value.reload

structure AbortResult (actual : SramState.State) (logical : Transfer.State) (offset : Nat)
    (value : AbortedRound) : Prop where
  related : RelatedSram I2cSource.source I2cCertificate.layout (value.execution.start .txData)
    (value.execution.finished actual)
    (Lifecycle.IdentityView.buffered offset (value.execution.source I2cSource.source actual logical))
  reset : Transfer.step capacity (value.execution.source I2cSource.source actual logical).buffers .reset =
    ⟨value.logicalAfter I2cSource.source actual logical, .reset⟩
  hardware : I2cReloadSession.Result (value.execution.finished actual) value.reload
  aligned : Aligned (value.after actual) (value.logicalAfter I2cSource.source actual logical)
    ((value.after actual).core .transfer).toNat
  epoch : (value.logicalAfter I2cSource.source actual logical).epoch = logical.epoch + 1
  sequence : (value.logicalAfter I2cSource.source actual logical).nextSequence = 1
  allocated : ((value.execution.finished actual).core .transfer).toNat = (actual.core .transfer).toNat + 1
  transfer : ((value.after actual).core .transfer).toNat =
    if value.reload.reset .initialize = 1#1 then 0 else (actual.core .transfer).toNat + 1
  generation : ((value.after actual).core .generation).toNat =
    (if value.reload.reset .initialize = 1#1 then 0 else min 65535 ((actual.core .generation).toNat + 1)) +
      LifecycleUpload.commitCount ((value.execution.finished actual).step value.reload.reset) value.reload.loading

theorem abort_result {actual : SramState.State} {logical : Transfer.State} {offset : Nat}
    (installed : InstalledSram I2cSource.source I2cCertificate.layout actual)
    (aligned : Aligned actual logical offset) {value : AbortedRound}
    (admitted : AbortAdmitted actual value) : AbortResult actual logical offset value := by
  have related := prefix_related installed aligned admitted.execution
  have allocation := prefix_allocation (p := I2cSource.source) aligned admitted.execution
  have counters := prefix_counters installed aligned admitted.execution
  have hardware := I2cReloadSession.result admitted.reload
  refine ⟨related, rfl, hardware, ⟨rfl, hardware.phase, hardware.retained, rfl⟩,
    ?_, rfl, counters.2, ?_, ?_⟩
  · exact congrArg (· + 1) allocation.1
  · simpa only [AbortedRound.after, apply_ite BitVec.toNat, show (0 : BitVec 16).toNat = 0 from rfl,
      counters.2] using congrArg BitVec.toNat hardware.transfer
  · simpa only [AbortedRound.after, counters.1] using hardware.generation

theorem prefix_take_related {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {actual : SramState.State} {logical : Transfer.State} {offset : Nat}
    (installed : InstalledSram p layout actual) (aligned : Aligned actual logical offset)
    {value : ExecutionPrefix} (admitted : PrefixAdmitted actual value) (count : Nat) :
    RelatedSram p layout (value.start .txData) ((actual.step value.start).run (value.body.take count))
      (Lifecycle.IdentityView.buffered offset
        (sourceCommands p (started p actual value.start logical) (value.body.take count))) :=
  prefix_related installed aligned
    (value := {value with body := value.body.take count})
    ⟨admitted.starting, administrative_take admitted.body count⟩

theorem abort_reset_eq {actual : SramState.State} {logical : Transfer.State} {offset : Nat}
    (aligned : Aligned actual logical offset) {value : AbortedRound}
    (admitted : AbortAdmitted actual value) :
    value.logicalAfter I2cSource.source actual logical = resetLogical logical := by
  exact congrArg (fun epoch => (⟨epoch + 1, 1, .free⟩ : Transfer.State))
    (prefix_allocation (p := I2cSource.source) aligned admitted.execution).1

theorem AbortedRound.after_eq_run (value : AbortedRound) (actual : SramState.State) :
    value.after actual = actual.run value.inputs := by
  simp [AbortedRound.after, AbortedRound.inputs, ExecutionPrefix.finished, ExecutionPrefix.inputs,
    I2cReloadSession.Batch.after_eq_run, SramState.State.run, List.foldl_append]

structure QuietResult (p : Program.Buffered.Program) (layout : GenericCertificate.Layout p)
    (actual : SramState.State) (logical : Transfer.State) (offset : Nat)
    (inputs : List (Values Reactive.Input)) : Prop where
  installed : InstalledSram p layout (actual.run inputs)
  aligned : Aligned (actual.run inputs) logical offset
  generation : (actual.run inputs).core .generation = actual.core .generation
  transfer : (actual.run inputs).core .transfer = actual.core .transfer

theorem quiet_result {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {actual : SramState.State} {logical : Transfer.State} {offset : Nat}
    (installed : InstalledSram p layout actual) (aligned : Aligned actual logical offset)
    (inputs : List (Values Reactive.Input)) (quiet : ∀ i ∈ inputs, SpiCircuit.Quiet i) :
    QuietResult p layout actual logical offset inputs := by
  exact ⟨installed.run inputs (fun i member => by
      have h := quiet i member
      simp [SramExecution.ExecutingInput, SharedBranches.Runtime, h.1, h.2]),
    aligned.quiet_run inputs quiet, (quiet_counters_run actual inputs quiet).1,
    (quiet_counters_run actual inputs quiet).2⟩

end Pinwheel.Hardware.Buffered.LogicalSession
