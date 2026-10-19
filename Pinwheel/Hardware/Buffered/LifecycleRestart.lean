import Pinwheel.Hardware.Buffered.LifecycleBuffered
import Pinwheel.Hardware.Buffered.LifecycleEpochRelation
import Pinwheel.Hardware.Buffered.GenericInstalledSram
import Pinwheel.Hardware.Buffered.GenericSramSimulation

/-! Restart after a logical reset uses epoch-local sequence one. A fresh
sequence offset accounts for the hardware transfer counter preserved by warm
reset. Both samplers are seeded from the actual START cut, even if an earlier
stopped source state had frozen its samplers. -/
namespace Pinwheel.Hardware.Buffered.LifecycleRestart
open Pinwheel.Hardware Pinwheel.Program

def request (r : Values Reactive.Register) (i : Values Reactive.Input) (epoch : Nat) : Transfer.Request :=
  {GenericStart.request r i with identity := ⟨epoch, 1⟩}

def seed (p : Program.Buffered.Program) (r : Values Reactive.Register)
    (i : Values Reactive.Input) (epoch : Nat) : Program.Buffered.State :=
  {GenericStart.seed p r i with
    buffers := ⟨epoch, 2, .running ⟨request r i epoch, 0, []⟩⟩
    owner := (request r i epoch).identity}

def started (p : Program.Buffered.Program) (r : Values Reactive.Register)
    (i : Values Reactive.Input) (epoch : Nat) : Program.Buffered.State :=
  GenericStart.resample (Program.Buffered.start p Refinement.capacity (seed p r i epoch))
    (i .rawInputs) (r .stage1)

theorem wire_seed (p : Program.Buffered.Program) (r : Values Reactive.Register)
    (i : Values Reactive.Input) (epoch : Nat) :
    Lifecycle.IdentityView.buffered (r .transfer).toNat (seed p r i epoch) =
      Lifecycle.EpochView.buffered epoch (GenericStart.seed p r i) := by
  rfl

theorem wire_started (p : Program.Buffered.Program) (r : Values Reactive.Register)
    (i : Values Reactive.Input) (epoch : Nat) :
    Lifecycle.IdentityView.buffered (r .transfer).toNat (started p r i epoch) =
      Lifecycle.EpochView.buffered epoch (GenericStart.started p r i) := by
  have start : Lifecycle.IdentityView.buffered (r .transfer).toNat
      (Program.Buffered.start p Refinement.capacity (seed p r i epoch)) =
      Lifecycle.EpochView.buffered epoch
        (Program.Buffered.start p Refinement.capacity (GenericStart.seed p r i)) := by
    rw [← Lifecycle.IdentityView.start, wire_seed, Lifecycle.EpochView.start]
  exact congrArg (fun s => GenericStart.resample s (i .rawInputs) (r .stage1)) start

theorem seed_after_reset (p : Program.Buffered.Program) (r : Values Reactive.Register)
    (i : Values Reactive.Input) (previous : Transfer.State)
    (tx : (i .txLength).toNat ≤ 32) (rx : (i .rxCapacity).toNat ≤ 32) :
    (Transfer.run Refinement.capacity (Transfer.step Refinement.capacity previous .reset).state
      [.prepare (r .generation).toNat
          (SpiPacking.txBits (i .txData) (i .txLength).toNat) (i .rxCapacity).toNat,
       .start (request r i (previous.epoch + 1)).identity (r .generation).toNat]).state =
      (seed p r i (previous.epoch + 1)).buffers := by
  simp [Transfer.run, Transfer.step, Transfer.Command.identity, Transfer.admittedStep,
    Transfer.Slot.identity, seed, request, GenericStart.request, SpiStart.request,
    Refinement.capacity, SpiRefinement.capacity, tx, rx]

theorem start_related {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {actual : SramState.State} (installed : Refinement.InstalledSram p layout actual)
    (i : Values Reactive.Input) (starting : Reactive.starting.eval i actual.core = 1)
    (epoch : Nat) :
    Refinement.RelatedSram p layout (i .txData) (actual.step i)
      (Lifecycle.IdentityView.buffered (actual.core .transfer).toNat (started p actual.core i epoch)) := by
  rw [wire_started]
  exact Lifecycle.EpochView.relatedSram epoch (installed.start i starting)

theorem run_related {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {actual : SramState.State} (installed : Refinement.InstalledSram p layout actual)
    (i : Values Reactive.Input) (starting : Reactive.starting.eval i actual.core = 1)
    (epoch : Nat) (incoming : Nat → BitVec 2) (edges : Nat) :
    Refinement.RelatedSram p layout (i .txData)
      ((actual.step i).run (SpiStart.clocks incoming edges))
      (Lifecycle.IdentityView.buffered (actual.core .transfer).toNat
        (Program.Buffered.run p Refinement.capacity (started p actual.core i epoch) incoming edges)) := by
  have result := (start_related installed i starting epoch).run incoming edges
  rw [Lifecycle.IdentityView.run] at result
  exact result

end Pinwheel.Hardware.Buffered.LifecycleRestart
