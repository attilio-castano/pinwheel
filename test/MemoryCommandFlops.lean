import Pinwheel.Hardware.Memory.CommandFlopsProofs

open Pinwheel.Hardware
open Pinwheel.Hardware.Memory
open Pinwheel.Hardware.Memory.CommandInterface

namespace MemoryCommandFlopsTests

set_option backward.isDefEq.respectTransparency false

/-- An independent integer/array oracle, without the command decoder or logical
memory step. Each physical edge is materialized to avoid deferred state chains. -/
structure Oracle where
  words : Array Nat
  q : Nat
  deriving BEq, Repr

structure Raw where
  enable : Bool
  write : Bool
  address : Nat
  data : Nat
  deriving Inhabited

def rawValues (a w : Nat) (p : Raw) : Values (Input a w)
  | _, .enable => BitVec.ofBool p.enable
  | _, .write => BitVec.ofBool p.write
  | _, .address => BitVec.ofNat a p.address
  | _, .data => BitVec.ofNat w p.data

def registerValues (a w : Nat) (s : Oracle) : Values (CommandFlops.Register a w)
  | _, .left (.word address) => BitVec.ofNat w (s.words[address.toNat]?.getD 0)
  | _, .right .q => BitVec.ofNat w s.q

def capture (a w : Nat) (s : Values (CommandFlops.Register a w)) : Oracle :=
  ⟨(Array.range (2^a)).map fun k => (s (CommandFlops.word (BitVec.ofNat a k))).toNat,
    (s CommandFlops.q).toNat⟩

def oracleStep (a w : Nat) (p : Raw) (s : Oracle) : Oracle :=
  if !p.enable then s
  else if p.write then { s with words := s.words.set! (p.address % 2^a) (p.data % 2^w) }
  else { s with q := s.words[p.address % 2^a]?.getD 0 }

def assertEq (label : String) (expected actual : Nat) : IO Unit :=
  unless expected == actual do
    throw (IO.userError s!"{label}: expected {expected}, got {actual}")

def checkEdge (a w : Nat) (label : String) (cycle : Nat) (p : Raw) (s : Oracle) : IO Oracle := do
  let i : Values (Input a w) := rawValues a w p
  let before : Values (CommandFlops.Register a w) := registerValues a w s
  let c := CommandFlops.circuit a w
  assertEq s!"{label} edge {cycle} Q before" s.q (c.observe i before .q).toNat
  let actual := capture a w (c.step i before)
  let expected := oracleStep a w p s
  unless expected == actual do
    throw (IO.userError s!"{label} edge {cycle}: expected {repr expected}, got {repr actual}")
  assertEq s!"{label} edge {cycle} Q after" expected.q
    (c.observe i (registerValues a w actual) .q).toNat
  return actual

def checkDescriptors (a w : Nat) : IO Unit := do
  let i := inputs a w
  let o := outputs w
  let r := CommandFlops.registers a w
  assertEq "input count" 4 i.ports.size
  assertEq "output count" 1 o.ports.size
  assertEq "register count" (2^a+1) r.ports.size
  let widths := i.ports.map fun p => p.1
  unless widths == #[1, 1, a, w] do
    throw (IO.userError s!"input width order: {widths}")
  for address in [0:2^a] do
    assertEq "register address order" address
      (r.position (CommandFlops.word (BitVec.ofNat a address))).val
  assertEq "Q register position" (2^a) (r.position CommandFlops.q).val

/-- Exhaustively enumerate every array, Q, mode, address, and data bit pattern. -/
def exhaustive (a w : Nat) : IO Nat := do
  checkDescriptors a w
  let words := 2^a
  let values := 2^w
  let states := values^(words+1)
  let mut edges := 0
  for seed in [0:states] do
    let s : Oracle := ⟨(Array.range words).map (fun k => seed / values^k % values),
      seed / values^words % values⟩
    for enable in [false, true] do
      for write in [false, true] do
        for address in [0:words] do
          for data in [0:values] do
            let _ ← checkEdge a w s!"exhaustive a{a} w{w}" edges
              ⟨enable, write, address, data⟩ s
            edges := edges + 1
  return edges

def directed : IO Nat := do
  checkDescriptors 2 8
  let initial : Oracle := ⟨#[17, 88, 33, 44], 123⟩
  -- Idle and disabled-write preserve both the arbitrary initial Q and array.
  -- Reads expose the old word at the edge; a same-address write preserves Q.
  let commands : Array (Raw × Nat) := #[
    (⟨false, false, 3, 221⟩, 123),
    (⟨false, true, 1, 99⟩, 123),
    (⟨true, false, 1, 207⟩, 88),
    (⟨true, false, 2, 234⟩, 33),
    (⟨true, true, 2, 157⟩, 33),
    (⟨true, false, 2, 101⟩, 157),
    (⟨true, false, 1, 0⟩, 88),
    (⟨false, true, 0, 255⟩, 88),
    (⟨true, false, 0, 0⟩, 17)]
  let mut s := initial
  for cycle in [0:commands.size] do
    let (p, expectedQ) := commands[cycle]!
    s ← checkEdge 2 8 "directed" cycle p s
    assertEq s!"directed edge {cycle} explicit Q" expectedQ s.q
  unless s.words == #[17, 88, 157, 44] do
    throw (IO.userError "directed: incorrect final array")
  return commands.size

def longTrace : IO Nat := do
  checkDescriptors 3 8
  let mut s : Oracle := ⟨#[5, 47, 169, 63, 213, 8, 71, 254], 137⟩
  for cycle in [0:240] do
    let p : Raw := ⟨cycle % 7 != 0, cycle % 5 < 2, cycle * 13 + 7, cycle * 41 + 129⟩
    s ← checkEdge 3 8 "long trace" cycle p s
  return 240

example (i : Values (Input a w)) (s : Values (CommandFlops.Register a w)) :
    CommandFlops.view ((CommandFlops.circuit a w).step i s) =
      SinglePort.step (CommandFlops.view s) (decode i) :=
  CommandFlops.step_view i s

example (s : Values (CommandFlops.Register a w)) (command : SinglePort.Command a w) :
    (CommandFlops.contract a w).view ((CommandFlops.contract a w).advance command s) =
      SinglePort.step ((CommandFlops.contract a w).view s) command :=
  (CommandFlops.contract a w).correct command s

end MemoryCommandFlopsTests

def main : IO Unit := do
  let mut exhaustive := 0
  exhaustive := exhaustive + (← MemoryCommandFlopsTests.exhaustive 1 2)
  exhaustive := exhaustive + (← MemoryCommandFlopsTests.exhaustive 0 3)
  exhaustive := exhaustive + (← MemoryCommandFlopsTests.exhaustive 0 0)
  let directed ← MemoryCommandFlopsTests.directed
  let trace ← MemoryCommandFlopsTests.longTrace
  IO.println s!"Command flop memory: {exhaustive} exhaustive state/input edges, {directed} directed edges, {trace} trace edges; all words and both Q edge observations agree."
