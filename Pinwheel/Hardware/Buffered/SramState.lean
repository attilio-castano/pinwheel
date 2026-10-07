import Pinwheel.Hardware.Buffered.SramProofs

/-! Closed-loop digital state for the actual typed SRAM controller and both
single-port memory copies. Neither startup arrays nor registered Q are cleared
or identified by this definition. -/
namespace Pinwheel.Hardware.Buffered.SramState
open Pinwheel.Hardware

structure State where
  registers : Values Sram.Register
  arrays : Fin 2 → Memory.Sram.State 6 64

def port (b : Bool) : Fin 2 := if b then 1 else 0

def State.inputs (s : State) (i : Values Reactive.Input) : Values Sram.Input
  | _, .base p => i p
  | _, .q b => (s.arrays (port b)).q

def State.core (s : State) : Values Reactive.Register := fun r => s.registers (.core r)

def State.step (s : State) (i : Values Reactive.Input) : State :=
  ⟨Sram.circuit.step (s.inputs i) s.registers,
    Memory.Sram.step (Sram.arrayRequest (s.inputs i) s.registers) s.arrays⟩

def State.observe (s : State) (i : Values Reactive.Input) (o : Reactive.Output w) : BitVec w :=
  Sram.circuit.observe (s.inputs i) s.registers (.base o)

def State.run (s : State) (inputs : List (Values Reactive.Input)) : State :=
  inputs.foldl State.step s

end Pinwheel.Hardware.Buffered.SramState
