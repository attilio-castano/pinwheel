import Pinwheel

open Pinwheel Pinwheel.Engine Pinwheel.Hardware

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

def main : IO Unit := do
  let mut accepted := 0
  let slots : Samples := Vector.replicate 8 true
  for value in [:65536] do
    let word := BitVec.ofNat 16 value
    ensure (Encoding.wordFromNat value == some word) s!"checked conversion {value}"
    -- Integer classification is independent of the bitvector decoder.
    let legal := value == 32768 || (value < 32768 && (value % 16 == 0 || value % 16 >= 8))
    ensure ((Encoding.decode word).isSome == legal) s!"classification {value}"
    match Encoding.decode word with
    | some instruction =>
      accepted := accepted + 1
      ensure (Encoding.encode instruction == word) s!"noncanonical alias {value}"
    | none =>
      let p : Raw.Program := ⟨Vector.replicate 32 word, 5⟩
      for input in [false, true] do
        let s := Raw.enter p 0 slots input
        ensure (s == ⟨.stopped .fault, 5, slots⟩ && result s == none) s!"fault {value}"
  ensure (accepted == 18433) "wrong accepted-word count"
  for levels in [:8] do
    for duration in [:256] do
      for capture in [:9] do
        let a : Action := ⟨BitVec.ofNat 3 levels, Fin.ofNat 256 duration,
          if capture == 8 then none else some (Fin.ofNat 8 capture)⟩
        ensure (Encoding.decode (Encoding.encode (.action a)) == some (.action a)) "round trip"
        ensure (a.duration == duration + 1) "duration convention"
  for value in [65536, 65537, 131072, 2^64] do
    ensure ((Encoding.wordFromNat value).isNone) "integer wrapped instead of rejection"
  IO.println "Passed all 65,536 raw words: 18,433 accepted, 47,103 rejected; all typed actions round-trip."
