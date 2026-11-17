import Lean
import Pinwheel.Hardware.Memory.TransferRange

open Lean Elab Command
open Pinwheel.Hardware.Memory
open Pinwheel.Hardware.Memory.TransferRange

namespace MemoryTransferRangeTests

def capture (a : Nat) (memory : Contents a w) : Array Nat :=
  (Array.range (2^a)).map (fun k => (memory (BitVec.ofNat a k)).toNat)

def contents (a w : Nat) (words : Array Nat) : Contents a w :=
  fun address => BitVec.ofNat w (words[address.toNat]?.getD 0)

def checkedRange (a base length : Nat) : IO (Range a) :=
  match Range.decode (BitVec.ofNat a base) (BitVec.ofNat (a+1) length) with
  | some range => pure range
  | none => throw (IO.userError s!"Expected checked range a{a}, base {base}, length {length}")

/-- All raw length codes, including overlong lengths and crossing the memory
end. No wrapping or truncated count is accepted. -/
def codecs (a : Nat) : IO Nat := do
  let depth := 2^a
  let mut checks := 0
  for base in [0:depth] do
    for length in [0:2^(a+1)] do
      let result := Range.decode (BitVec.ofNat a base) (BitVec.ofNat (a+1) length)
      unless result.isSome == decide (length ≤ depth-base) do
        throw (IO.userError s!"Codec a{a} base {base} length {length}: incorrect admission")
      if let some range := result then
        unless range.base.toNat == base && range.length == length && range.encodedLength.toNat == length do
          throw (IO.userError "Range codec changed a legal base or length")
        let mut addresses : Array Nat := #[]
        for offset in [0:length] do
          let address := (range.index offset).toNat
          unless address == base+offset && address < depth && !addresses.contains address do
            throw (IO.userError "Range index wrapped or duplicated an address")
          addresses := addresses.push address
      checks := checks + 1
  return checks

/-- Compare recursive prefix construction and incremental word writes with an
independent array-slice oracle at every prefix length and every address. -/
def transfers (a w : Nat) (seeds : Array Nat) : IO Nat := do
  let depth := 2^a
  let modulus := 2^w
  let mut checks := 0
  for sourceSeed in seeds do
    let sourceWords := (Array.range depth).map (fun k => sourceSeed / modulus^k % modulus)
    let source := contents a w sourceWords
    for destinationSeed in seeds do
      let initialWords := (Array.range depth).map (fun k => destinationSeed / modulus^k % modulus)
      let initial := contents a w initialWords
      for delta in [0:modulus] do
        let f := fun v : BitVec w => v + BitVec.ofNat w delta
        for sourceBase in [0:depth] do
          for destinationBase in [0:depth] do
            for length in [0:min (depth-sourceBase) (depth-destinationBase)+1] do
              let sr ← checkedRange a sourceBase length
              let dr ← checkedRange a destinationBase length
              let mut incremental := initialWords
              for completed in [0:length+1] do
                let expected := (Array.range depth).map fun address =>
                  if destinationBase ≤ address && address < destinationBase+completed then
                    (sourceWords[sourceBase + (address-destinationBase)]! + delta) % modulus
                  else initialWords[address]!
                let actual := capture a (copyPrefix sr dr source initial f completed)
                unless actual == expected && incremental == expected do
                  throw (IO.userError s!"Prefix a{a} w{w} src{sourceBase} dst{destinationBase} len{length} k{completed}: expected {expected}, got recursive {actual}, incremental {incremental}")
                if completed < length then
                  let address := dr.index completed
                  let payload := f (source (sr.index completed))
                  incremental := capture a ((contents a w incremental).write ⟨true, address, payload⟩)
                checks := checks + 1
  return checks

-- Full depth needs the extra length bit; zero length and the last word are legal.
example : (Range.full 3).encodedLength.toNat = 8 := rfl
example : Range.decode (7 : BitVec 3) (2 : BitVec 4) = none := by decide +kernel
example : (⟨7, 1, by decide⟩ : Range 3).index 0 = 7 := rfl
example (r : Range a) (source : Contents a wi) (initial : Contents a wo) (f : BitVec wi → BitVec wo) :
    copyPrefix r r source initial f 0 = initial := rfl

example (sourceRange destinationRange : Range a) (source : Contents a wi)
    (initial current : Contents a wo) (f : BitVec wi → BitVec wo)
    (sameLength : sourceRange.length = destinationRange.length)
    (k : Nat) (hk : k < sourceRange.length)
    (h : Patched destinationRange initial (copyValue sourceRange source f) k current) :
    Patched destinationRange initial (copyValue sourceRange source f) (k+1)
      (current.write ⟨true, destinationRange.index k, f (source (sourceRange.index k))⟩) :=
  copy_patch_step sourceRange destinationRange source initial current f sameLength k hk h

end MemoryTransferRangeTests

elab "#audit_transfer_range" : command => do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "Pinwheel.Hardware.Memory.TransferRange." ||
        name.toString.startsWith "_private.Pinwheel.Hardware.Memory.TransferRange." then
      count := count + 1
      let axioms ← collectAxioms name
      let bad := axioms.filter fun a => a != ``propext && a != ``Classical.choice && a != ``Quot.sound
      unless bad.isEmpty do throwError "Unapproved axioms in {name}: {bad}"
  if count == 0 then throwError "Empty transfer range audit"
  logInfo m!"Transfer range audit: {count} declarations, standard axioms only."

#audit_transfer_range

def main : IO Unit := do
  let mut codecs := 0
  for a in [0:5] do
    codecs := codecs + (← MemoryTransferRangeTests.codecs a)
  let mut prefixes := 0
  prefixes := prefixes + (← MemoryTransferRangeTests.transfers 0 0 #[0])
  prefixes := prefixes + (← MemoryTransferRangeTests.transfers 0 2 (Array.range 4))
  prefixes := prefixes + (← MemoryTransferRangeTests.transfers 1 2 (Array.range 16))
  prefixes := prefixes + (← MemoryTransferRangeTests.transfers 2 3 #[0, 1, 85, 593, 1337, 4095])
  IO.println s!"Transfer ranges: {codecs} exhaustive raw range codes, {prefixes} destination prefix checks; every address matches the independent slice oracle."
