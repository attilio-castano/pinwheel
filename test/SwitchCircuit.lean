import Pinwheel.Hardware.Switch.CircuitProofs

open Pinwheel.Hardware
open Pinwheel.Hardware.Switch
open Pinwheel.Hardware.Switch.Physical

namespace SwitchCircuitTests

set_option backward.isDefEq.respectTransparency false

def snapshot (d : Interface P) (s : Values P) : Array Nat :=
  d.ports.map fun ⟨_, r⟩ => (s r).toNat

def restore (d : Interface P) (a : Array Nat) : Values P :=
  fun {w} r => BitVec.ofNat w (a[(d.position r).val]?.getD 0)

def compare (d : Interface P) (label : String) (cycle : Nat) (expected actual : Values P) : IO Unit := do
  let mismatches := d.differences cycle label .before expected actual
  match mismatches[0]? with
  | none => pure ()
  | some mismatch => throw (IO.userError mismatch.describe)

/-- Raw input generation deliberately includes invalid destinations, reset under
traffic, independent output stalls, idle garbage, and continuously offered load.
No canonical input encoding is used by the circuit under test. -/
def pins (n m dw w cycle : Nat) : Pins n m dw w where
  reset := BitVec.ofBool (cycle % 79 == 0)
  valid := fun k => BitVec.ofBool ((cycle + k.val * 3) % 7 != 0)
  destination := fun k => BitVec.ofNat dw (cycle / 5 + k.val * 7)
  payload := fun k => BitVec.ofNat w (cycle * 29 + k.val * 101)
  ready := fun o => BitVec.ofBool (cycle % 37 > 9 && (cycle + o.val * 3) % 5 != 0)

/-- Materialize every logical lane between cycles, avoiding repeated evaluation
of a chain of functional state updates in this runtime regression. -/
def materialize (s : Switch.State n (m+1) (BitVec w)) : Switch.State n (m+1) (BitVec w) :=
  let queues := Vector.ofFn s.queues
  let slots := Vector.ofFn s.slots
  let cursors := Vector.ofFn s.cursor
  ⟨fun k => queues[k.val], fun o => slots[o.val], fun o => cursors[o.val]⟩

def exercise (n m w depth : Nat) (e : DestinationEncoding (m+1)) : IO Nat := do
  let regs := Structural.registers n m e.width w depth
  let outs := outputInterface n m w
  let c := Structural.circuit e n w depth
  let mut logical : Switch.State n (m+1) (BitVec w) := Switch.initial
  let mut bank := snapshot regs (Structural.encode e logical)
  let label := s!"switch-{n+1}x{m+1}-w{w}-d{depth}"
  -- Reset must restore the encoding from malformed FIFO/slot/cursor bit patterns.
  for pattern in [0:4] do
    let dirty : Values (Structural.Register n m e.width w depth) := fun {b} r =>
      BitVec.ofNat b (if pattern == 0 then 0 else if pattern == 1 then 2^b-1
        else (regs.position r).val * 13 + pattern)
    let rst := { pins n m e.width w 1 with reset := 1 }
    compare regs (label ++ "-reset") pattern (Structural.encode e Switch.initial) (c.step rst.values dirty)
  for cycle in [0:240] do
    let p := pins n m e.width w cycle
    let physical : Values (Structural.Register n m e.width w depth) := restore regs bank
    compare outs label cycle (Physical.observe depth p logical) (c.observe p.values physical)
    let next : Values (Structural.Register n m e.width w depth) := c.step p.values physical
    let expected := materialize (Switch.step depth (decode p) logical)
    let captured := snapshot regs next
    compare regs label cycle (Structural.encode e expected) (restore regs captured)
    compare outs (label ++ "-after") cycle (Physical.observe depth p expected)
      (c.observe p.values (restore regs captured))
    logical := expected
    bank := captured
  pure 240

example (e : DestinationEncoding (m+1)) (i : Values (In n m e.width w))
    (s : Switch.State n (m+1) (BitVec w)) (hs : Switch.Valid depth s)
    (r : Structural.Register n m e.width w depth b) :
    (Structural.circuit e n w depth).step i (Structural.encode e s) r =
      Structural.encode e (Switch.step depth (decode (readPins i)) s) r :=
  Structural.step_eq e s hs i r

example (e : DestinationEncoding (m+1)) (i : Values (In n m e.width w))
    (s : Values (Structural.Register n m e.width w depth)) (hr : i reset = 1)
    (r : Structural.Register n m e.width w depth b) :
    (Structural.circuit e n w depth).step i s r = Structural.encode e Switch.initial r :=
  Structural.reset_eq e i s hr r

end SwitchCircuitTests

def main : IO Unit := do
  let mut cycles := 0
  cycles := cycles + (← SwitchCircuitTests.exercise 0 0 1 1 ⟨1, by decide, by decide⟩)
  cycles := cycles + (← SwitchCircuitTests.exercise 0 2 8 2 ⟨2, by decide, by decide⟩)
  cycles := cycles + (← SwitchCircuitTests.exercise 1 0 8 1 ⟨1, by decide, by decide⟩)
  cycles := cycles + (← SwitchCircuitTests.exercise 1 2 8 1 ⟨2, by decide, by decide⟩)
  cycles := cycles + (← SwitchCircuitTests.exercise 1 2 8 3 ⟨2, by decide, by decide⟩)
  cycles := cycles + (← SwitchCircuitTests.exercise 2 1 16 2 ⟨1, by decide, by decide⟩)
  cycles := cycles + (← SwitchCircuitTests.exercise 2 2 5 2 ⟨3, by decide, by decide⟩)
  cycles := cycles + (← SwitchCircuitTests.exercise 1 2 0 2 ⟨2, by decide, by decide⟩)
  IO.println s!"Switch circuit: {cycles} raw-input cycles; all registers and both edge observations agree; 32 malformed-state reset cases passed."
