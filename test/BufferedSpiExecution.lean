import Pinwheel.Hardware.Buffered.SpiExecution

/-! Kernel checked decoder controls and universal execution theorem signatures.
The executable checks complement, rather than replace, the universal theorem.
-/
namespace Pinwheel.Test.BufferedSpiExecution
open Pinwheel.Hardware Pinwheel.Program Pinwheel.Engine.Reactive
open Hardware.Buffered

private def changedRow (k : BitVec 6) (value : BitVec 92) : Memory.Contents 6 92 :=
  fun address => if address == k then value else SpiSource.rows BufferedSPI.Config.default address

private def changedTable : Memory.Contents 4 56 := fun k => if k == 0 then 1 else 0

private def badWord : Memory.Contents 6 92 :=
  changedRow 0 ((SpiSource.rows BufferedSPI.Config.default 0) ^^^ BitVec.ofNat 92 (2^56))
private def badControl : Memory.Contents 6 92 :=
  changedRow 1 ((SpiSource.rows BufferedSPI.Config.default 1) ^^^ BitVec.ofNat 92 (2^64))
private def badIndex : Memory.Contents 6 92 :=
  changedRow 0 ((SpiSource.rows BufferedSPI.Config.default 0) ^^^ BitVec.ofNat 92 (2^88))
private def unsupportedWord : Memory.Contents 6 92 :=
  changedRow 0 ((0#4) ++ (SpiSource.control BufferedSPI.Config.default 0 ++ (5#64)))

example : SpiExecution.decode badWord SpiSource.dictionary = none := by decide +kernel
example : SpiExecution.decode badControl SpiSource.dictionary = none := by decide +kernel
example : SpiExecution.decode badIndex SpiSource.dictionary = none := by decide +kernel
example : SpiExecution.decode unsupportedWord SpiSource.dictionary = none := by decide +kernel
example : SpiExecution.decode (SpiSource.rows BufferedSPI.Config.default) changedTable = none := by
  decide +kernel

/-- Both supported geometry boundaries are kernel theorem instances. -/
private def smallest : BufferedSPI.Config := ⟨0, 2, by decide⟩
private def largest : BufferedSPI.Config := ⟨3, 255, by decide⟩
example : SpiExecution.decode (SpiSource.rows smallest) SpiSource.dictionary =
    some (BufferedSPI.program smallest) := SpiExecution.decode_source smallest
example : SpiExecution.decode (SpiSource.rows largest) SpiSource.dictionary =
    some (BufferedSPI.program largest) := SpiExecution.decode_source largest

/-- This checks the quantifiers really allow arbitrary capacities, complete
source states, raw histories and prefix lengths (including terminal prefixes). -/
example (c : BufferedSPI.Config) (capacity : Transfer.Capacity) (s : Program.Buffered.State)
    (incoming : Nat → Inputs) (n : Nat) :
    SpiExecution.run (SpiSource.rows c) SpiSource.dictionary capacity s incoming n =
      some (Program.Buffered.run (BufferedSPI.program c) capacity s incoming n) :=
  SpiExecution.run_source c capacity s incoming n

private def check : IO Unit := do
  let rejected := [SpiExecution.decode badWord SpiSource.dictionary,
    SpiExecution.decode badControl SpiSource.dictionary,
    SpiExecution.decode badIndex SpiSource.dictionary,
    SpiExecution.decode unsupportedWord SpiSource.dictionary,
    SpiExecution.decode (SpiSource.rows BufferedSPI.Config.default) changedTable].all Option.isNone
  if !rejected then throw (IO.userError "SPI decoder accepted a malformed image")
  let positive := [smallest, largest, BufferedSPI.Config.default].all fun c =>
    (SpiExecution.decode (SpiSource.rows c) SpiSource.dictionary).isSome
  if !positive then throw (IO.userError "SPI decoder rejected a supported geometry")
  IO.println "SPI decoded execution: universal source theorem, 5 rejected image mutations, 3 positive geometries; passed"
end Pinwheel.Test.BufferedSpiExecution

def main : IO Unit := Pinwheel.Test.BufferedSpiExecution.check
