import Pinwheel.Hardware.Buffered.Sram
import Pinwheel.Hardware.Buffered.MemoEval

/-! Executable closed-loop digital SRAM/controller model. The arrays and Q may
start unrelated. Snapshotting prevents expression evaluation from retaining a
recursive history. Requests use the actual prospective core snapshot; the
controller schedule theorem identifies these with emitted request ports. -/
namespace Pinwheel.Hardware.Buffered.SramModel
open Pinwheel.Hardware
namespace C
abbrev Register := Sram.Register
end C

structure Snapshot where
  bank : Array Nat

def Snapshot.values (s : Snapshot) : Values Sram.Register := fun {w} r =>
  BitVec.ofNat w (s.bank[Sram.registerIndex r]?.getD 0)

def snapshot (s : Values Sram.Register) : Snapshot :=
  ⟨Sram.registers.map fun ⟨_,r⟩ => (s r).toNat⟩

def nextExpressions : Array (Sigma (Expr Sram.Input Sram.Register)) :=
  Sram.registers.map fun ⟨w,r⟩ => ⟨w,Sram.circuit.next r⟩

/-- The logical batch evaluates exactly the ordinary typed next-state equations.
Its native implementation caches shared nodes only within this one edge. -/
def nextSnapshot (i : Values Sram.Input) (s : Values Sram.Register) : Snapshot :=
  ⟨MemoEval.evalMany i s nextExpressions⟩

theorem nextSnapshot_eq (i : Values Sram.Input) (s : Values Sram.Register) :
    (nextSnapshot i s).bank = (snapshot (Sram.circuit.step i s)).bank := by
  simp only [nextSnapshot, MemoEval.evalMany_eq, nextExpressions, snapshot,
    Circuit.step, Array.map_map, Function.comp_def]

structure State where
  registers : Snapshot
  arrays : Array (Array Nat)
  q : Array Nat

def State.initial (seed : Nat := 0) : State :=
  ⟨⟨Sram.registers.mapIdx fun k ⟨w,_⟩ =>
      if seed = 0 then 0 else (seed*7919 + k*104729 + 23) % 2^w⟩,
    Array.ofFn fun p : Fin 2 => Array.ofFn fun k : Fin 64 =>
      (seed*65537 + (p.val+1)*104729 + k.val*7919 + 19) % 2^64,
    #[seed+0x12345678, seed+0xa5a5a5a5]⟩

def State.inputs (s : State) (i : Values Reactive.Input) : Values Sram.Input
  | _, .base p => i p
  | _, .q b => BitVec.ofNat 64 (s.q[if b then 1 else 0]?.getD 0)

def State.core (s : State) : Values Reactive.Register := fun r =>
  s.registers.values (.core r)

def State.contents (s : State) (port : Fin 2) : Memory.Contents 6 64 := fun address =>
  BitVec.ofNat 64 ((s.arrays[port.val]?.getD #[])[address.toNat]?.getD 0)

/-- The public execution state is advanced by the actual typed equations.
Request addresses use that materialized post-edge state, rather than evaluating
the same next-state expressions repeatedly through register closures. -/
def State.step (s : State) (i : Values Reactive.Input) : State := Id.run do
  let inputs : Values Sram.Input := s.inputs i
  let after := nextSnapshot inputs s.registers.values
  let writing := (Sram.rowWriting.eval inputs s.registers.values) == 1
  let address := (i .address).toNat
  let data := (i .word).toNat
  let core : Values Reactive.Register := fun r => after.values (.core r)
  let read (b : Bool) := ((SramCandidates.candidate b).eval (fun _ => 0) core).toNat % 64
  let arrays := if writing then s.arrays.map (fun cells => cells.set! address data) else s.arrays
  let q := if writing then s.q else
    #[(s.arrays[0]?.getD #[])[read false]?.getD 0,
      (s.arrays[1]?.getD #[])[read true]?.getD 0]
  return ⟨after, arrays, q⟩

def State.observe (s : State) (i : Values Reactive.Input) (o : Reactive.Output w) : BitVec w :=
  Sram.circuit.observe (s.inputs i) s.registers.values (.base o)

end Pinwheel.Hardware.Buffered.SramModel
