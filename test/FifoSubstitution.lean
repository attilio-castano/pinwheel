import Pinwheel.Hardware.Library

open Pinwheel.Hardware Stream BackendAPI

namespace FifoSubstitutionTest

private def sample (v : Option (BitVec 4)) (ready : Bool) (reset := false) : Values (In 4) :=
  inputValues ⟨reset,v,ready⟩

-- Materialize each clock edge once, including every register in the interface.
private structure Image (R : Nat → Type) where
  read : Values R

private def snapshot (ri : Interface R) (r : Values R) : Image R :=
  let values := ri.ports.map fun ⟨_,p⟩ => (r p).toNat
  ⟨fun {w} p => BitVec.ofNat w values[(ri.position p).val]!⟩

/-- Inspect all six physical registers: the two-bit illegal pointer encoding,
wraparound, retained idle data, and a full replacement at the read slot. -/
private def ringEdges : IO Unit := do
  let c := CircularFifo3.backend 4
  let ri := c.registers
  let mut raw : Image c.Register := ⟨fun {w} _ => BitVec.ofNat w 15⟩
  let edges : List (Bool × Option (BitVec 4) × Bool × List Nat) := [
    (true,some 8,true,[0,0,0,15,15,15]), (false,some 4,false,[0,1,1,4,15,15]),
    (false,some 5,false,[0,2,2,4,5,15]), (false,some 6,false,[0,0,3,4,5,6]),
    (false,some 9,false,[0,0,3,4,5,6]), (false,some 7,true,[1,1,3,7,5,6]),
    (false,none,true,[2,1,2,7,5,6]), (false,none,true,[0,1,1,7,5,6]),
    (true,some 8,true,[0,0,0,7,5,6])]
  for (rst,offered,rd,want) in edges do
    let next : Values c.Register := c.circuit.step (sample offered rd rst) raw.read
    let got := ri.ports.toList.map fun ⟨_,p⟩ => (next p).toNat
    unless got == want do throw (IO.userError s!"ring registers {got}, expected {want}")
    raw := snapshot ri next

private def laneHistory (fifo : Fifo 4 3) : IO Unit := do
  let c := (bufferedMap fifo (increment 4) 1).circuit
  let dirty : Values (bufferedMap fifo (increment 4) 1).Register := fun {w} _ => BitVec.ofNat w 15
  let offers : List (Values (In 4)) := [sample (some 9) false, sample (some 8) true true,
    sample (some 15) false, sample (some 2) false, sample (some 2) false]
  let drain : List (Values (In 4)) := List.replicate 10 (α := Values (In 4)) (sample none true)
  let traffic := offers ++ drain
  let ri := (bufferedMap fifo (increment 4) 1).registers
  let mut r := snapshot ri (c.step (sample none false true) dirty)
  let mut h : History (BitVec 4) (BitVec 4) := {}
  for i in traffic do
    h := h.advance (decodeInput i) (decodeOutput (c.observe i r.read))
    r := snapshot ri (c.step i r.read)
  unless h.inputs == [15,2,2] && h.outputs == [0,3,3] do
    throw (IO.userError s!"lane history {h.inputs} -> {h.outputs}")

end FifoSubstitutionTest

def main : IO Unit := do
  FifoSubstitutionTest.ringEdges
  FifoSubstitutionTest.laneHistory (shift 4 3 (by decide))
  FifoSubstitutionTest.laneHistory (CircularFifo3.backend 4)
  IO.println "Depth-three wrap, full replacement, reset retention and both lane histories passed."
