import Lean
import Pinwheel.Hardware.Memory.ByteAccess

open Lean Elab Command
open Pinwheel.Hardware.Memory.ByteAccess

namespace MemoryByteAccessTests

/-- Independent arithmetic oracle: division/remainders extract a contiguous
integer segment. It does not call the library's decoder, lanes, pack, masks,
alignment, extension, or core operations. Inputs here are already wire-sized. -/
def referenceFault (raw offset : Nat) : Option Fault :=
  if raw = 3 then some .reservedSize
  else if offset % (2^raw) ≠ 0 then some .misaligned else none

def referenceLoad (raw offset word : Nat) (signed : Bool) : Option Fault × Nat :=
  match referenceFault raw offset with
  | some error => (some error, 0)
  | none =>
    let bits := 8 * 2^raw
    let span := 2^bits
    let segment := word / (256^offset) % span
    let value := if signed && segment ≥ span/2 then segment + 2^32 - span else segment
    (none, value)

def referenceStore (raw offset word data : Nat) : Option Fault × Nat :=
  match referenceFault raw offset with
  | some error => (some error, word)
  | none =>
    let low := 256^offset
    let span := 256^(2^raw)
    (none, word % low + (data % span)*low + (word / (low*span))*(low*span))

def loadView : Except Fault Word → Option Fault × Nat
  | .error error => (some error, 0)
  | .ok value => (none, value.toNat)

def storeView (value : StoreResult) : Option Fault × Nat := (value.fault, value.word.toNat)

def requireEqual (actual expected : Option Fault × Nat) (label : String) : IO Unit :=
  unless actual = expected do
    throw (IO.userError s!"{label}: expected {repr expected}, got {repr actual}")

def check (raw offset word data : Nat) : IO Unit := do
  let r := BitVec.ofNat 2 raw
  let o := BitVec.ofNat 2 offset
  let w := BitVec.ofNat 32 word
  let d := BitVec.ofNat 32 data
  for signed in [false, true] do
    requireEqual (loadView (load r signed o w)) (referenceLoad raw offset word signed)
      s!"load size{raw}/offset{offset}/signed{signed}/{word}"
  let result := store r o w d
  let expected := referenceStore raw offset word data
  requireEqual (storeView result) expected s!"store size{raw}/offset{offset}/{word}/{data}"
  -- A second access uses the independently computed complete new word,
  -- checking that written and retained bytes survive beyond the write result.
  for lane in [:4] do
    requireEqual (loadView (load 0 false (BitVec.ofNat 2 lane) result.word))
      (referenceLoad 0 lane expected.2 false) s!"readback lane{lane}"

def boundaries : List Nat :=
  [0, 1, 0x7f, 0x80, 0xff, 0x100, 0x7fff, 0x8000, 0xffff, 0x10000,
   0x7fffffff, 0x80000000, 0xffffffff, 0x80ff7f01, 0x01234567, 0xfedcba98,
   0x000080ff, 0x8000ffff, 0xff008000, 0xa55a00ff]

def mutationControls : IO Nat := do
  let probes : List (String × (Option Fault × Nat) × (Option Fault × Nat)) :=
    [("reversed-byte-lanes", loadView (load 0 false 3 0x12345678), referenceLoad 0 0 0x12345678 false),
     ("missing-byte-sign-extension", loadView (load 0 false 0 0x80), referenceLoad 0 0 0x80 true),
     ("missing-half-sign-extension", loadView (load 1 false 2 0x80000000), referenceLoad 1 2 0x80000000 true),
     ("high-data-byte-instead-of-low", storeView (store 0 2 0x12345678 (0xaabbccdd >>> 8)),
       referenceStore 0 2 0x12345678 0xaabbccdd),
     ("write-on-alignment-fault", (some .misaligned, 0), referenceStore 1 1 0x12345678 0xaabbccdd),
     ("reserved-size-as-word", storeView (store 2 0 0x12345678 0xaabbccdd),
       referenceStore 3 0 0x12345678 0xaabbccdd),
     ("round-down-misaligned-half", storeView (store 1 0 0x12345678 0xaabbccdd),
       referenceStore 1 1 0x12345678 0xaabbccdd),
     ("clear-untouched-lanes", (none, 0xdd0000), referenceStore 0 2 0x12345678 0xaabbccdd)]
  for (label, actual, expected) in probes do
    if actual = expected then throw (IO.userError s!"Mutation escaped arithmetic oracle: {label}")
  return probes.length

-- Concrete kernel reductions make the byte order and high-bit interpretation
-- reviewable independently of runtime execution.
example : load 0 true 2 0x00800000 = .ok 0xffffff80 := rfl
example : load 1 true 2 0x80001234 = .ok 0xffff8000 := rfl
example : store 0 2 0x12345678 0xaabbccdd = ⟨0x12dd5678, none⟩ := rfl
example : store 1 3 0x12345678 0xaabbccdd = ⟨0x12345678, some .misaligned⟩ := rfl
example : store 3 0 0x12345678 0xaabbccdd = ⟨0x12345678, some .reservedSize⟩ := rfl

end MemoryByteAccessTests

elab "#audit_byte_access" : command => do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "Pinwheel.Hardware.Memory.ByteAccess." ||
        name.toString.startsWith "MemoryByteAccessTests." ||
        name.toString.startsWith "_private.test.MemoryByteAccess." then
      count := count + 1
      let axioms ← collectAxioms name
      let bad := axioms.filter fun a => a != ``propext && a != ``Classical.choice && a != ``Quot.sound
      unless bad.isEmpty do throwError "Unapproved byte-access axioms in {name}: {bad}"
  if count < 25 then throwError "Incomplete byte-access audit"
  logInfo m!"Byte-access audit: {count} declarations, standard axioms only."

#audit_byte_access

def main : IO Unit := do
  let mut count := 0
  for raw in [:4] do
    for offset in [:4] do
      for word in MemoryByteAccessTests.boundaries do
        for data in MemoryByteAccessTests.boundaries do
          MemoryByteAccessTests.check raw offset word data
          count := count + 1
  -- Sweep every byte value in every lane, with unrelated high/low bytes.
  for lane in [:4] do
    for value in [:256] do
      let word := (0x5a00a5ff / (256^(lane+1)))*(256^(lane+1)) +
        value*(256^lane) + 0x5a00a5ff % (256^lane)
      MemoryByteAccessTests.check 0 lane word (255-value)
      count := count + 1
  let mut seed : Nat := 0x62797465
  for k in [:4096] do
    seed := (1664525*seed + 1013904223) % 2^32
    let word := seed
    seed := (1664525*seed + 1013904223) % 2^32
    MemoryByteAccessTests.check (k % 4) ((k/4) % 4) word seed
    count := count + 1
  let mutations ← MemoryByteAccessTests.mutationControls
  IO.println s!"Byte access: {count} arithmetic-reference cases, signed/unsigned loads, stores and all-lane readback; {mutations} semantic mutations rejected."
