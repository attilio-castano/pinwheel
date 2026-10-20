import Pinwheel.Hardware.Buffered.SpiPacking
import Pinwheel.Hardware.Buffered.SpiInterpreter
import Pinwheel.Hardware.Buffered.Reactive
import Pinwheel.Hardware.Buffered.SramExecution

/-! The logical request and source seed for one actual admitted SPI START.
The seed is constructed from START operands and the pre-edge owner counter;
its sampler values are the physical sampler values after that START edge. -/
namespace Pinwheel.Hardware.Buffered.SpiStart
open Pinwheel.Hardware Pinwheel.Program

def capacity : Transfer.Capacity := ⟨32, 32⟩

def request (r : Values Reactive.Register) (i : Values Reactive.Input) : Transfer.Request :=
  ⟨⟨0, (r .transfer).toNat + 1⟩, (r .generation).toNat,
    SpiPacking.txBits (i .txData) (i .txLength).toNat, (i .rxCapacity).toNat⟩

def seed (c : BufferedSPI.Config) (r : Values Reactive.Register)
    (i : Values Reactive.Input) : Program.Buffered.State :=
  { core := ⟨.stopped .ready, (BufferedSPI.program c).idle, Vector.replicate 16 false⟩
    buffers := ⟨0, (r .transfer).toNat + 2, .running ⟨request r i, 0, []⟩⟩
    owner := (request r i).identity
    samplerFirst := i .rawInputs
    samplerSecond := r .stage1 }

theorem request_bounded (r : Values Reactive.Register) (i : Values Reactive.Input)
    (tx : (i .txLength).toNat ≤ 32) (rx : (i .rxCapacity).toNat ≤ 32) :
    (request r i).Bounded capacity := by
  simp [Transfer.Request.Bounded, request, capacity, tx, rx]

/-- The source's running request is obtained by the ordinary ownership API.
It is not an arbitrary running slot assumed to match the circuit. -/
theorem seed_admitted (c : BufferedSPI.Config) (r : Values Reactive.Register)
    (i : Values Reactive.Input) (tx : (i .txLength).toNat ≤ 32)
    (rx : (i .rxCapacity).toNat ≤ 32) :
    (Transfer.run capacity ⟨0, (r .transfer).toNat + 1, .free⟩
      [.prepare (r .generation).toNat
          (SpiPacking.txBits (i .txData) (i .txLength).toNat) (i .rxCapacity).toNat,
       .start (request r i).identity (r .generation).toNat]).state =
      (seed c r i).buffers := by
  simp [Transfer.run, Transfer.step, Transfer.Command.identity, Transfer.admittedStep,
    Transfer.Slot.identity, request, seed, capacity, tx, rx]

def quietInput (raw : BitVec 2) : Values Reactive.Input
  | _, .rawInputs => raw
  | _, _ => 0

theorem quiet_executing (raw : BitVec 2) :
    SramExecution.ExecutingInput (quietInput raw) := by
  simp [SramExecution.ExecutingInput, SharedBranches.Runtime, quietInput]

/-- Prefix order matches Buffered.run: input n is consumed on clock n+1. -/
def clocks (incoming : Nat → BitVec 2) : Nat → List (Values Reactive.Input)
  | 0 => []
  | n + 1 => clocks incoming n ++ [@quietInput (incoming n)]

def packedRun (r : Values Reactive.Register) (incoming : Nat → BitVec 2)
    (edges : Nat) : Values Reactive.Register :=
  SramExecution.reactiveRun r (clocks incoming edges)

theorem packedRun_zero (r : Values Reactive.Register) (incoming : Nat → BitVec 2) :
    @packedRun r incoming 0 = @r := rfl

theorem packedRun_succ (r : Values Reactive.Register) (incoming : Nat → BitVec 2)
    (edges : Nat) :
    @packedRun r incoming (edges + 1) =
      (fun {w} (register : Reactive.Register w) =>
        Reactive.circuit.step (quietInput (incoming edges)) (packedRun r incoming edges) register) := by
  funext w register
  simp only [packedRun, clocks, SramExecution.reactiveRun, List.foldl_append,
    List.foldl_cons, List.foldl_nil]

theorem clocks_executing (incoming : Nat → BitVec 2) (edges : Nat) :
    ∀ i ∈ clocks incoming edges, SramExecution.ExecutingInput i := by
  induction edges
  all_goals simp_all [clocks]
  grind [quiet_executing]
  done

end Pinwheel.Hardware.Buffered.SpiStart
