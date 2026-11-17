import Lean
import Pinwheel.Hardware.Switch.PacketEncoding

open Pinwheel.Hardware Pinwheel.Hardware.Switch
open Pinwheel.Hardware.Switch.Physical
open Pinwheel.Hardware.Switch.PacketEncoding
open Lean Elab Command

set_option backward.isDefEq.respectTransparency false

elab "#audit_packet_encoding" : command => do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "Pinwheel.Hardware.Switch.PacketEncoding." ||
        name == ``Stream.mapInput || name == ``Stream.queue_map_step ||
        name == ``Stream.queue_map_ready || name == ``Stream.queue_map_offer ||
        name == ``Stream.queue_map_observe then
      count := count + 1
      let axioms ← collectAxioms name
      let bad := axioms.filter fun a => a != ``propext && a != ``Classical.choice && a != ``Quot.sound
      unless bad.isEmpty do throwError "Unapproved axioms in {name}: {bad}"
  if count == 0 then throwError "Empty packet encoding proof audit"
  logInfo m!"Packet encoding audit: {count} declarations, standard axioms only."

#audit_packet_encoding

namespace PacketEncodingTests

def dest1 : DestinationEncoding 1 := ⟨1, by decide, by decide⟩
def dest3 : DestinationEncoding 3 := ⟨2, by decide, by decide⟩
def dest5 : DestinationEncoding 5 := ⟨3, by decide, by decide⟩

example : pack dest3 (⟨2, 42⟩ : Packet 3 (BitVec 8)) = 554#10 := by decide +kernel
example : unpack dest5 (1234#11) = some (⟨4, 210⟩ : Packet 5 (BitVec 8)) := by decide +kernel
example : unpack dest1 (256#9) = (none : Option (Packet 1 (BitVec 8))) := by decide +kernel
example : unpack dest3 (768#10) = (none : Option (Packet 3 (BitVec 8))) := by decide +kernel
example : unpack dest5 (1280#11) = (none : Option (Packet 5 (BitVec 8))) := by decide +kernel

example (e : DestinationEncoding outputs) (p : Packet outputs (BitVec w)) :
    unpack e (pack e p) = some p := unpack_pack e p

example (f : α → β) (depth : Nat) (i : Stream.Input α) (q : List α) :
    (Stream.queue depth).step (Stream.mapInput f i) (q.map f) =
      ((Stream.queue depth).step i q).map f := Stream.queue_map_step f depth i q

private def checkCodec (m : Nat) (e : DestinationEncoding (m + 1)) : IO Nat := do
  let mut checked := 0
  -- Enumerate the entire raw wire space, including every invalid destination
  -- code, with four payload bits. The oracle uses integer quotient/remainder.
  for raw in [:2^(e.width + 4)] do
    let x := BitVec.ofNat (e.width + 4) raw
    let decoded := unpack e x
    let dest := raw / 16
    let data := raw % 16
    unless decoded.isSome == (dest < m + 1) do
      throw (IO.userError s!"Destination acceptance mismatch: outputs={m+1}, raw={raw}")
    if let some p := decoded then
      unless p.destination.val == dest && p.payload.toNat == data && pack e p == x do
        throw (IO.userError s!"Packet roundtrip mismatch: outputs={m+1}, raw={raw}")
    checked := checked + 1
  pure checked

private def sample (m seed : Nat) : Packet (m + 1) (BitVec 8) :=
  ⟨⟨seed % (m + 1), Nat.mod_lt _ (by omega)⟩, BitVec.ofNat 8 (seed * 37 + 19)⟩

private def checkQueue (m : Nat) (e : DestinationEncoding (m + 1)) : IO Nat := do
  let mut checked := 0
  for depth in [1, 2, 3] do
    for length in [:depth + 1] do
      for seed in [:16] do
        let q := (List.range length).map (fun offset => sample m (seed + offset))
        for reset in [false, true] do
          for ready in [false, true] do
            for offered in [none, some (sample m (seed + 7)), some (sample m (seed + 13))] do
              let i : Stream.Input (Packet (m + 1) (BitVec 8)) := ⟨reset, offered, ready⟩
              let bits : Values (Stream.In (e.width + 8)) := Stream.inputValues (Stream.mapInput (pack e) i)
              let circuit := Stream.Fifo.circuit (e.width + 8) depth
              let before : Values (Stream.CellReg (e.width + 8) depth) := cells e q
              let after : Values (Stream.CellReg (e.width + 8) depth) := circuit.step bits before
              let expected : Values (Stream.CellReg (e.width + 8) depth) := cells e ((Stream.queue depth).step i q)
              for k in List.finRange depth do
                unless after (.valid k) == expected (.valid k) && after (.data k) == expected (.data k) do
                  throw (IO.userError s!"Packet FIFO state mismatch: outputs={m+1}, depth={depth}, length={length}, seed={seed}")
              let logical := (Stream.queue depth).component.observe i q
              let output : Values (Stream.Out (e.width + 8)) := circuit.observe bits before
              let expectedOutput : Values (Stream.Out (e.width + 8)) := Stream.outputValues
                (⟨logical.ready, logical.offered.map (pack e)⟩ : Stream.Output (BitVec (e.width + 8)))
              for ⟨_, p⟩ in (Stream.outputPorts (e.width + 8)).interface.ports do
                unless output p == expectedOutput p do
                  throw (IO.userError s!"Packet FIFO output mismatch: outputs={m+1}, depth={depth}, length={length}, seed={seed}")
              checked := checked + 1
  pure checked

end PacketEncodingTests

def main : IO Unit := do
  let codecs ← PacketEncodingTests.checkCodec 0 PacketEncodingTests.dest1
  let codecs := codecs + (← PacketEncodingTests.checkCodec 2 PacketEncodingTests.dest3)
  let codecs := codecs + (← PacketEncodingTests.checkCodec 4 PacketEncodingTests.dest5)
  let queues ← PacketEncodingTests.checkQueue 0 PacketEncodingTests.dest1
  let queues := queues + (← PacketEncodingTests.checkQueue 2 PacketEncodingTests.dest3)
  let queues := queues + (← PacketEncodingTests.checkQueue 4 PacketEncodingTests.dest5)
  IO.println s!"Switch packet encoding: {codecs} exhaustive raw codecs and {queues} FIFO state/output transitions passed."
