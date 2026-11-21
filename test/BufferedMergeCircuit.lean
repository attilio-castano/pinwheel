import Lean
import Pinwheel.Hardware.Stream.BufferedMerge.Proofs

open Lean Elab Command
open Pinwheel.Hardware
open Pinwheel.Hardware.Stream.BufferedMerge

namespace BufferedMergeCircuitTests

set_option backward.isDefEq.respectTransparency false

def snapshot (d : Interface P) (s : Values P) : Array Nat :=
  d.ports.map (fun ⟨_, r⟩ => (s r).toNat)

def restore (d : Interface P) (a : Array Nat) : Values P :=
  fun {b} r => BitVec.ofNat b (a[(d.position r).val]?.getD 0)

def compare (d : Interface P) (label : String) (cycle : Nat) (expected actual : Values P) : IO Unit := do
  match (d.differences cycle label .before expected actual)[0]? with
  | none => pure ()
  | some mismatch => throw (IO.userError mismatch.describe)

def checkDescriptors (n w : Nat) : IO Unit := do
  let i := Physical.inputInterface n w
  let o := Physical.outputInterface n w
  let r := Structural.registers n w
  unless i.ports.map (fun p => p.1) == #[1,1] ++ Array.replicate (n+1) 1 ++ Array.replicate (n+1) w &&
      o.ports.map (fun p => p.1) == Array.replicate (n+1) 1 ++ #[1,w] &&
      r.ports.map (fun p => p.1) == #[1,w] ++ Array.replicate (n+1) 1 do
    throw (IO.userError "incorrect typed port/register enumeration")
  unless (i.position Physical.reset).val == 0 && (i.position Physical.outReady).val == 1 &&
      (o.position Physical.outValid).val == n+1 && (o.position Physical.outPayload).val == n+2 &&
      (r.position (Structural.slotReg (.valid 0))).val == 0 &&
      (r.position (Structural.slotReg (.data 0))).val == 1 do
    throw (IO.userError "incorrect scalar role positions")
  for k in List.finRange (n+1) do
    unless (i.position (Physical.inValid k)).val == 2+k.val &&
        (i.position (Physical.inPayload k)).val == n+3+k.val &&
        (o.position (Physical.inReady k)).val == k.val &&
        (r.position (Structural.cursorReg k)).val == 2+k.val do
      throw (IO.userError "incorrect indexed role positions")

def checkEdge (n w : Nat) (cycle : Nat) (p : Physical.Pins n w)
    (s : State n (BitVec w)) : IO Unit := do
  let c := Structural.circuit n w
  let ri := Structural.registers n w
  let oi := Physical.outputInterface n w
  let before : Values (Structural.Register n w) := Structural.encode s
  compare oi "merge-before" cycle ((Physical.component n w).observe p.values s) (c.observe p.values before)
  let expected := step (Physical.decode p) s
  let captured := snapshot ri (c.step p.values before)
  compare ri "merge-registers" cycle (Structural.encode expected) (restore ri captured)
  compare oi "merge-after" cycle ((Physical.component n w).observe p.values expected)
    (c.observe p.values (restore ri captured))

def exhaustive (n : Nat) : IO Nat := do
  checkDescriptors n 1
  let sources := List.finRange (n+1)
  let slots : List (Option (Delivery n (BitVec 1))) := none :: sources.flatMap
    (fun source => [some ⟨source, 0⟩, some ⟨source, 1⟩])
  let mut edges := 0
  for cursor in sources do
    for slot in slots do
      for controls in [0:4] do
        for valids in [0:2^(n+1)] do
          for payloads in [0:2^(n+1)] do
            let p : Physical.Pins n 1 :=
              ⟨BitVec.ofNat 1 controls, BitVec.ofNat 1 (controls/2),
                fun k => BitVec.ofNat 1 (valids/2^k.val), fun k => BitVec.ofNat 1 (payloads/2^k.val)⟩
            checkEdge n 1 edges p ⟨cursor, slot⟩
            edges := edges+1
  return edges

/-- Invalid input ports deliberately carry changing, nonzero payload garbage.
Repeating payload values across inputs tests the erased provenance boundary. -/
def pins (n w cycle : Nat) : Physical.Pins n w :=
  ⟨BitVec.ofBool (cycle % 61 == 0),
    BitVec.ofBool (cycle % 43 > 15 && cycle % 5 != 0),
    fun k => BitVec.ofBool ((cycle+k.val*3) % 7 != 0),
    fun k => BitVec.ofNat w (if cycle % 3 == 0 then cycle % 4 else cycle*29+k.val*101)⟩

def exercise (n w : Nat) : IO Nat := do
  checkDescriptors n w
  let c := Structural.circuit n w
  let ri := Structural.registers n w
  let oi := Physical.outputInterface n w
  for pattern in [0:4] do
    let dirty : Values (Structural.Register n w) := fun {b} r => BitVec.ofNat b
      (if pattern == 0 then 0 else if pattern == 1 then 2^b-1 else (ri.position r).val*13+pattern)
    let p := { pins n w 1 with reset := 1 }
    compare oi "merge-reset-outputs" pattern (fun _ => 0) (c.observe p.values dirty)
    compare ri "merge-reset-state" pattern (Structural.encode (initial : State n (BitVec w)))
      (c.step p.values dirty)
  let mut logical : State n (BitVec w) := initial
  let mut bank := snapshot ri (Structural.encode logical)
  for cycle in [0:240] do
    let p := pins n w cycle
    let physical : Values (Structural.Register n w) := restore ri bank
    compare oi "merge-raw-before" cycle ((Physical.component n w).observe p.values logical)
      (c.observe p.values physical)
    let next := snapshot ri (c.step p.values physical)
    logical := step (Physical.decode p) logical
    compare ri "merge-raw-registers" cycle (Structural.encode logical) (restore ri next)
    compare oi "merge-raw-after" cycle ((Physical.component n w).observe p.values logical)
      (c.observe p.values (restore ri next))
    bank := next
  return 240

def provenanceErasure : IO Unit := do
  let first : State 1 (BitVec 8) := ⟨0, some ⟨0, 7⟩⟩
  let second : State 1 (BitVec 8) := ⟨0, some ⟨1, 7⟩⟩
  compare (Structural.registers 1 8) "source-erasure" 0
    (Structural.encode first) (Structural.encode second)
  unless first.slot != second.slot do
    throw (IO.userError "source-erasure test did not use distinct logical origins")

example (i : Values (Physical.In n w)) (s : State n (BitVec w)) (r : Structural.Register n w b) :
    (Structural.circuit n w).step i (Structural.encode s) r =
      Structural.encode (step (Physical.decode (Physical.readPins i)) s) r :=
  Structural.step_eq i s r

example (i : Values (Physical.In n w)) (s : Values (Structural.Register n w))
    (h : i Physical.reset = 1) (inputs : List (Values (Physical.In n w))) :
    (Structural.circuit n w).component.trace ((Structural.circuit n w).step i s) inputs =
      (Physical.component n w).trace initial inputs := Structural.initialized_trace i s h inputs

end BufferedMergeCircuitTests

elab "#audit_buffered_merge_circuit" : command => do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "Pinwheel.Hardware.Stream.BufferedMerge." ||
        name.toString.startsWith "_private.Pinwheel.Hardware.Stream.BufferedMerge." then
      count := count+1
      let axioms ← collectAxioms name
      let bad := axioms.filter fun a => a != ``propext && a != ``Classical.choice && a != ``Quot.sound
      unless bad.isEmpty do throwError "Unapproved axioms in {name}: {bad}"
  if count == 0 then throwError "Empty buffered-merge circuit audit"
  logInfo m!"Buffered merge circuit audit: {count} declarations, standard axioms only."

#audit_buffered_merge_circuit

def main : IO Unit := do
  let mut exhaustive := 0
  for n in [0,1,2] do
    exhaustive := exhaustive + (← BufferedMergeCircuitTests.exhaustive n)
  let mut traces := 0
  for n in [0,1,2,4,7] do
    for w in [1,8,17] do
      traces := traces + (← BufferedMergeCircuitTests.exercise n w)
  traces := traces + (← BufferedMergeCircuitTests.exercise 1 0)
  BufferedMergeCircuitTests.provenanceErasure
  IO.println s!"Buffered merge circuit: {exhaustive} exhaustive encoded-state edges, {traces} raw-input trace edges, 64 malformed-state resets; all registers and pre/post outputs agree, including idle payload garbage and source-tag erasure."
