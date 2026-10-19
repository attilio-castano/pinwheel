import Pinwheel.Hardware.Buffered.GenericEntryTransfer
import Pinwheel.Hardware.Buffered.SpiStart

/-! An admitted generic START constructs its source request through the owned
prepare/start API. Instruction entry observes preedge stage2; the samplers then
advance on the same START edge. The original full payload remains available
even when the request declares a shorter TX list. -/
namespace Pinwheel.Hardware.Buffered.GenericStart
open Pinwheel.Hardware Pinwheel.Program Pinwheel.Engine.Reactive

abbrev request := SpiStart.request

def seed (_p : Program.Buffered.Program) (r : Values Reactive.Register)
    (i : Values Reactive.Input) : Program.Buffered.State :=
  { core := ⟨.stopped .ready, ⟨r .levels, r .enabled⟩, Vector.replicate 16 false⟩
    buffers := ⟨0, (r .transfer).toNat + 2, .running ⟨request r i, 0, []⟩⟩
    owner := (request r i).identity
    samplerFirst := r .stage1
    samplerSecond := r .stage2 }

def resample (s : Program.Buffered.State) (first second : Inputs) : Program.Buffered.State :=
  {s with samplerFirst := first, samplerSecond := second}

def base (p : Program.Buffered.Program) (r : Values Reactive.Register)
    (i : Values Reactive.Input) : Program.Buffered.State :=
  resample (seed p r i) (i .rawInputs) (r .stage1)

def started (p : Program.Buffered.Program) (r : Values Reactive.Register)
    (i : Values Reactive.Input) : Program.Buffered.State :=
  resample (Program.Buffered.start p Refinement.capacity (seed p r i))
    (i .rawInputs) (r .stage1)

theorem seed_admitted (p : Program.Buffered.Program) (r : Values Reactive.Register)
    (i : Values Reactive.Input) (tx : (i .txLength).toNat ≤ 32)
    (rx : (i .rxCapacity).toNat ≤ 32) :
    (Transfer.run Refinement.capacity ⟨0, (r .transfer).toNat + 1, .free⟩
      [.prepare (r .generation).toNat
          (SpiPacking.txBits (i .txData) (i .txLength).toNat) (i .rxCapacity).toNat,
       .start (request r i).identity (r .generation).toNat]).state =
      (seed p r i).buffers := by
  simp [Transfer.run, Transfer.step, Transfer.Command.identity, Transfer.admittedStep,
    Transfer.Slot.identity, SpiStart.request, seed, Refinement.capacity,
    SpiRefinement.capacity, tx, rx]

theorem start_seed (p : Program.Buffered.Program) (r : Values Reactive.Register)
    (i : Values Reactive.Input) :
    Program.Buffered.start p Refinement.capacity (seed p r i) =
      GenericEntry.entered p (seed p r i) 0 (Vector.replicate 16 false) (r .stage2) := by
  simp [Program.Buffered.start, Program.Buffered.owned, seed,
    GenericEntry.entered, Fetch.start]

theorem started_final (p : Program.Buffered.Program) (layout : GenericCertificate.Layout p)
    (r : Values Reactive.Register) (i : Values Reactive.Input)
    (instruction : Program.Buffered.Instruction) (fetch : p.fetch 0 = some instruction) :
    started p r i = GenericEntry.finalState p (base p r i) ⟨request r i, 0, []⟩ 0
      instruction (Vector.replicate 16 false) (r .stage2) := by
  unfold started
  rw [start_seed, GenericEntry.entered_final p layout (seed p r i) ⟨request r i, 0, []⟩
    0 (GenericLayout.span_positive p.code) instruction fetch (Vector.replicate 16 false)
    (r .stage2) rfl rfl]
  unfold GenericEntry.finalState
  cases GenericEffects.finalOutcome instruction ⟨request r i, 0, []⟩ (r .stage2) <;> rfl
  done

end Pinwheel.Hardware.Buffered.GenericStart
