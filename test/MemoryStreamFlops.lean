import Pinwheel.Hardware.Memory.StreamFlopsProofs

open Pinwheel.Hardware
open Pinwheel.Hardware.Memory
open Pinwheel.Hardware.Memory.StreamInterface

namespace MemoryStreamFlopsTests

structure Oracle where
  words : Array Nat
  q : Nat
  pending : Bool
  deriving BEq, Repr

def registerValues (a w : Nat) (s : Oracle) : Values (StreamFlops.Register a w)
  | _, .left (.left (.word address)) => BitVec.ofNat w (s.words[address.toNat]?.getD 0)
  | _, .left (.right .q) => BitVec.ofNat w s.q
  | _, .right .valid => BitVec.ofBool s.pending

def capture (a w : Nat) (s : Values (StreamFlops.Register a w)) : Oracle :=
  ⟨(Array.range (2^a)).map (fun address =>
      (s (.left (CommandFlops.word (BitVec.ofNat a address)))).toNat),
    (s (.left CommandFlops.q)).toNat, s StreamFlops.pending == 1⟩

/-- Independent integer/array oracle for the physical pins. It uses neither the
logical adapter step nor its input decoder or state encoder. -/
def advance (p : Pins a w) (s : Oracle) : Oracle :=
  if p.reset == 1 then { s with pending := false }
  else if s.pending && p.ready == 0 then s
  else if p.valid == 0 then { s with pending := false }
  else if p.write == 1 then
    { s with words := s.words.set! p.address.toNat p.data.toNat, pending := false }
  else { s with q := s.words[p.address.toNat]?.getD 0, pending := true }

def checkOutput (w : Nat) (label : String) (p : Pins a w) (s : Oracle)
    (o : Values (Output w)) : IO Unit := do
  let expectedReady := p.reset == 0 && (!s.pending || p.ready == 1)
  let expectedValid := p.reset == 0 && s.pending
  let expectedData := if expectedValid then s.q else 0
  unless o inReady == BitVec.ofBool expectedReady &&
      o outValid == BitVec.ofBool expectedValid && (o outData).toNat == expectedData do
    throw (IO.userError s!"{label}: expected ready/valid/data {expectedReady}/{expectedValid}/{expectedData}, got {(o inReady).toNat}/{(o outValid).toNat}/{(o outData).toNat}")

def checkEdge (a w : Nat) (label : String) (cycle : Nat) (p : Pins a w) (s : Oracle) : IO Oracle := do
  let c := StreamFlops.circuit a w
  let initial : Values (StreamFlops.Register a w) := registerValues a w s
  checkOutput w s!"{label} edge {cycle} before" p s (c.observe p.values initial)
  let actual := capture a w (c.step p.values initial)
  let expected := advance p s
  unless actual == expected do
    throw (IO.userError s!"{label} edge {cycle}: expected {repr expected}, got {repr actual}")
  checkOutput w s!"{label} edge {cycle} after" p expected (c.observe p.values (registerValues a w actual))
  return actual

def checkDescriptors (a w : Nat) : IO Unit := do
  let i := inputs a w
  let o := outputs w
  let r := StreamFlops.registers a w
  unless i.ports.size == 6 && o.ports.size == 3 && r.ports.size == 2^a+2 do
    throw (IO.userError "incorrect interface size")
  unless i.ports.map (fun p => p.1) == #[1, 1, 1, a, w, 1] &&
      o.ports.map (fun p => p.1) == #[1, 1, w] do
    throw (IO.userError "incorrect port width order")
  for address in [0:2^a] do
    unless (r.position (.left (CommandFlops.word (BitVec.ofNat a address)))).val == address do
      throw (IO.userError "incorrect word register order")
  unless (r.position (.left CommandFlops.q)).val == 2^a &&
      (r.position StreamFlops.pending).val == 2^a+1 do
    throw (IO.userError "Q/pending order does not extend the command memory by exactly one bit")
  let widths := r.ports.map (fun p => p.1)
  unless widths == (Array.replicate (2^a+1) w).push 1 do
    throw (IO.userError "extra or incorrectly sized adapter registers")

/-- Every register/input bit pattern, including arbitrary initial Q and pending,
reset under offered writes, and all ignored invalid-request data bits. -/
def exhaustive (a w : Nat) : IO Nat := do
  checkDescriptors a w
  let words := 2^a
  let values := 2^w
  let mut edges := 0
  for seed in [0:values^(words+1)] do
    for pending in [false, true] do
      let s : Oracle := ⟨(Array.range words).map (fun k => seed / values^k % values),
        seed / values^words % values, pending⟩
      for control in [0:16] do
        for address in [0:words] do
          for data in [0:values] do
            let p : Pins a w := ⟨BitVec.ofNat 1 control, BitVec.ofNat 1 (control / 2),
              BitVec.ofNat 1 (control / 4), BitVec.ofNat a address, BitVec.ofNat w data,
              BitVec.ofNat 1 (control / 8)⟩
            let _ ← checkEdge a w s!"exhaustive a{a} w{w}" edges p s
            edges := edges + 1
  return edges

def delivered (p : Pins a w) (s : Oracle) : List Nat :=
  let o : Values (Output w) := (StreamFlops.circuit a w).observe p.values (registerValues a w s)
  if p.ready == 1 && o outValid == 1 then [(o outData).toNat] else []

def directed : IO Nat := do
  checkDescriptors 2 8
  let initial : Oracle := ⟨#[17, 88, 33, 44], 123, true⟩
  let pins : Array (Pins 2 8) := #[
    ⟨1, 1, 1, 1, 255, 1⟩, -- Reset cancels an arbitrary response and offered write.
    ⟨0, 0, 1, 1, 200, 0⟩, -- Invalid write cannot alter memory or Q.
    ⟨0, 1, 0, 1, 207, 0⟩, -- Read data bits are ignored.
    ⟨0, 0, 1, 2, 99, 0⟩,  -- Invalid garbage while a response is held.
    ⟨0, 1, 0, 2, 234, 0⟩, -- A blocked read cannot overwrite Q.
    ⟨0, 1, 1, 1, 7, 0⟩,   -- A blocked write cannot alter the array.
    ⟨0, 1, 0, 2, 101, 1⟩, -- Retire 88 and accept read 33 on one edge.
    ⟨0, 1, 1, 2, 157, 1⟩, -- Retire 33, commit write, hold Q.
    ⟨0, 1, 0, 2, 99, 0⟩,
    ⟨1, 1, 0, 0, 77, 1⟩,  -- Cancel 157 without clearing memory or Q.
    ⟨0, 0, 1, 0, 255, 1⟩,
    ⟨0, 1, 0, 2, 46, 1⟩,
    ⟨0, 0, 1, 0, 199, 1⟩]
  let expectedResponses : Array (List Nat) :=
    #[[], [], [], [], [], [], [88], [33], [], [], [], [], [157]]
  let mut s := initial
  for cycle in [0:pins.size] do
    let p := pins[cycle]?.getD ⟨0, 0, 0, 0, 0, 0⟩
    unless delivered p s == expectedResponses[cycle]! do
      throw (IO.userError s!"directed edge {cycle}: wrong response timing")
    s ← checkEdge 2 8 "directed" cycle p s
  unless s == ⟨#[17, 88, 157, 44], 157, false⟩ do
    throw (IO.userError "directed final memory differs; reset must preserve committed writes and Q")
  return pins.size

def longTrace : IO Nat := do
  checkDescriptors 3 8
  let mut s : Oracle := ⟨#[5, 47, 169, 63, 213, 8, 71, 254], 137, false⟩
  let mut reads : List Nat := []
  let mut responses : List Nat := []
  for cycle in [0:240] do
    let p : Pins 3 8 := ⟨BitVec.ofBool (cycle % 43 == 0), BitVec.ofBool (cycle % 9 != 0),
      BitVec.ofBool (cycle % 5 < 2), BitVec.ofNat 3 (cycle * 13 + 7),
      BitVec.ofNat 8 (cycle * 41), BitVec.ofBool (cycle % 17 > 6)⟩
    if p.reset == 1 then
      reads := []
      responses := []
    else
      responses := responses ++ delivered p s
      if p.valid == 1 && p.write == 0 && (!s.pending || p.ready == 1) then
        reads := reads ++ [s.words[p.address.toNat]?.getD 0]
    s ← checkEdge 3 8 "long trace" cycle p s
    unless reads == responses ++ (if s.pending then [s.q] else []) do
      throw (IO.userError s!"long trace edge {cycle}: response snapshot ledger failed")
  return 240

example (i : Values (Input a w)) (s : Values (StreamFlops.Register a w)) :
    StreamFlops.view ((StreamFlops.circuit a w).step i s) =
      StreamModel.step (decode i) (StreamFlops.view s) := StreamFlops.step_view i s

example (i : Values (Input a w)) (s : Values (StreamFlops.Register a w)) (hr : i reset = 1)
    (r : CommandFlops.Register a w b) :
    (StreamFlops.circuit a w).step i s (.left r) = s (.left r) := StreamFlops.reset_memory i s hr r

end MemoryStreamFlopsTests

def main : IO Unit := do
  let mut exhaustive := 0
  exhaustive := exhaustive + (← MemoryStreamFlopsTests.exhaustive 1 2)
  exhaustive := exhaustive + (← MemoryStreamFlopsTests.exhaustive 0 2)
  exhaustive := exhaustive + (← MemoryStreamFlopsTests.exhaustive 0 0)
  let directed ← MemoryStreamFlopsTests.directed
  let trace ← MemoryStreamFlopsTests.longTrace
  IO.println s!"Memory stream flops: {exhaustive} exhaustive raw state/input edges, {directed} directed edges, {trace} trace edges; every register, every pre/post output, timing and response ledger agree."
