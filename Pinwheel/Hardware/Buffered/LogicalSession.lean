import Pinwheel.Hardware.Buffered.I2cSessionTrace
import Pinwheel.Hardware.Buffered.GenericCommandSimulation
import Pinwheel.Hardware.Buffered.GenericReadback
import Pinwheel.Hardware.Buffered.LifecycleRestart

/-! A continuous ordinary Transfer.State is carried through every session.
Warm reset starts a new logical sequence at one and rebases its wire offset.
Execution segments permit actual rejected commands and indexed observations. -/
namespace Pinwheel.Hardware.Buffered.LogicalSession
open Pinwheel.Hardware Pinwheel.Program

structure Aligned (actual : SramState.State) (logical : Transfer.State) (offset : Nat) : Prop where
  free : logical.slot = .free
  phase : actual.core .phase = 0
  retained : actual.core .retained = 0
  sequence : offset + logical.nextSequence = (actual.core .transfer).toNat + 1

def request (actual : SramState.State) (i : Values Reactive.Input)
    (logical : Transfer.State) : Transfer.Request :=
  ⟨⟨logical.epoch, logical.nextSequence⟩, (actual.core .generation).toNat,
    SpiPacking.txBits (i .txData) (i .txLength).toNat, (i .rxCapacity).toNat⟩

def allocate (actual : SramState.State) (i : Values Reactive.Input)
    (logical : Transfer.State) : Transfer.State :=
  (Transfer.run Refinement.capacity logical
    [.prepare (actual.core .generation).toNat
        (SpiPacking.txBits (i .txData) (i .txLength).toNat) (i .rxCapacity).toNat,
     .start (request actual i logical).identity (actual.core .generation).toNat]).state

theorem allocate_eq {actual : SramState.State} {i : Values Reactive.Input}
    {logical : Transfer.State} (free : logical.slot = .free)
    (tx : (i .txLength).toNat ≤ 32) (rx : (i .rxCapacity).toNat ≤ 32) :
    allocate actual i logical = ⟨logical.epoch, logical.nextSequence + 1,
      .running ⟨request actual i logical, 0, []⟩⟩ := by
  simp [allocate, Transfer.run, Transfer.step, Transfer.Command.identity,
    Transfer.Slot.identity, Transfer.admittedStep, free, request,
    Refinement.capacity, SpiRefinement.capacity, tx, rx]

def seed (p : Program.Buffered.Program) (actual : SramState.State)
    (i : Values Reactive.Input) (logical : Transfer.State) : Program.Buffered.State :=
  {GenericStart.seed p actual.core i with
    buffers := allocate actual i logical
    owner := (request actual i logical).identity}

def started (p : Program.Buffered.Program) (actual : SramState.State)
    (i : Values Reactive.Input) (logical : Transfer.State) : Program.Buffered.State :=
  GenericStart.resample (Program.Buffered.start p Refinement.capacity (seed p actual i logical))
    (i .rawInputs) (actual.core .stage1)

theorem wire_seed {p : Program.Buffered.Program} {actual : SramState.State}
    {logical : Transfer.State} {offset : Nat} (aligned : Aligned actual logical offset)
    (i : Values Reactive.Input) (tx : (i .txLength).toNat ≤ 32) (rx : (i .rxCapacity).toNat ≤ 32) :
    Lifecycle.IdentityView.buffered offset (seed p actual i logical) =
      Lifecycle.EpochView.buffered logical.epoch (GenericStart.seed p actual.core i) := by
  simp only [seed, allocate_eq aligned.free tx rx, Lifecycle.IdentityView.buffered,
    Lifecycle.IdentityView.state, Lifecycle.IdentityView.slot, Lifecycle.IdentityView.execution,
    Lifecycle.IdentityView.request, Lifecycle.IdentityView.identity,
    Lifecycle.EpochView.buffered, Lifecycle.EpochView.state, Lifecycle.EpochView.slot,
    Lifecycle.EpochView.execution, Lifecycle.EpochView.request, Lifecycle.EpochView.identity,
    GenericStart.seed, GenericStart.request, SpiStart.request, request, Nat.add_zero,
    ← Nat.add_assoc, aligned.sequence]
theorem wire_started {p : Program.Buffered.Program} {actual : SramState.State}
    {logical : Transfer.State} {offset : Nat} (aligned : Aligned actual logical offset)
    (i : Values Reactive.Input) (tx : (i .txLength).toNat ≤ 32) (rx : (i .rxCapacity).toNat ≤ 32) :
    Lifecycle.IdentityView.buffered offset (started p actual i logical) =
      Lifecycle.EpochView.buffered logical.epoch (GenericStart.started p actual.core i) := by
  have start : Lifecycle.IdentityView.buffered offset
      (Program.Buffered.start p Refinement.capacity (seed p actual i logical)) =
      Lifecycle.EpochView.buffered logical.epoch
        (Program.Buffered.start p Refinement.capacity (GenericStart.seed p actual.core i)) := by
    rw [← Lifecycle.IdentityView.start, wire_seed aligned i tx rx, Lifecycle.EpochView.start]
  exact congrArg (fun s => GenericStart.resample s (i .rawInputs) (actual.core .stage1)) start

theorem sourceCommands_rename (p : Program.Buffered.Program) (source : Program.Buffered.State)
    (inputs : List (Values Reactive.Input)) (offset : Nat) :
    Refinement.sourceCommands p (Lifecycle.IdentityView.buffered offset source) inputs =
      Lifecycle.IdentityView.buffered offset (Refinement.sourceCommands p source inputs) := by
  induction inputs generalizing source
  case nil => rfl
  case cons i rest ih =>
    change Refinement.sourceCommands p
      (Program.Buffered.advance p Refinement.capacity (Lifecycle.IdentityView.buffered offset source)
        (i .rawInputs)) rest = _
    rw [Lifecycle.IdentityView.advance, ih]
    rfl

theorem sourceCommands_allocation (p : Program.Buffered.Program) (source : Program.Buffered.State)
    (inputs : List (Values Reactive.Input)) :
    (Refinement.sourceCommands p source inputs).buffers.epoch = source.buffers.epoch ∧
      (Refinement.sourceCommands p source inputs).buffers.nextSequence = source.buffers.nextSequence := by
  induction inputs generalizing source
  case nil => exact ⟨rfl, rfl⟩
  case cons i rest ih =>
    have first := GenericSession.source_run_allocation p source (fun _ => i .rawInputs) 1
    have tail := ih (Program.Buffered.advance p Refinement.capacity source (i .rawInputs))
    exact ⟨tail.1.trans first.1, tail.2.trans first.2⟩

end Pinwheel.Hardware.Buffered.LogicalSession
