import Pinwheel.Hardware.Storage.DenseEmit

open Pinwheel.Hardware

inductive CodecInput : Nat → Type where | word : CodecInput 64 | dense : CodecInput 55
inductive CodecOutput : Nat → Type where | packed : CodecOutput 55 | expanded : CodecOutput 64

def codec : Circuit CodecInput Emit.NoRegister CodecOutput where
  next := fun r => nomatch r
  output := fun p => match p with
    | .packed => Storage.Dense.compressExpr (.input .word)
    | .expanded => Storage.Dense.expandExpr (.input .dense)

def main : IO Unit := do
  match Emit.moduleText "pinwheel_dense_codec" codec #[⟨64, .word⟩, ⟨55, .dense⟩] #[]
    #[⟨55, .packed⟩, ⟨64, .expanded⟩] (fun p => match p with | .word => "word" | .dense => "dense")
    (fun r => nomatch r) (fun p => match p with | .packed => "compressed" | .expanded => "expanded") with
  | .ok text => IO.FS.writeFile "build/storage/codec.mlir" text
  | .error e => throw (IO.userError e)
  let mut count := 0
  for line in (← IO.FS.lines "build/storage/codec-vectors.txt") do
    let v := (line.splitOn " ").toArray.map (fun n => n.toNat!.toUInt64)
    let i : Values CodecInput := fun p => match p with
      | .word => BitVec.ofNat 64 v[0]!.toNat | .dense => BitVec.ofNat 55 v[1]!.toNat
    let r : Values Emit.NoRegister := fun r => nomatch r
    unless (codec.observe i r .packed).toNat == v[2]!.toNat &&
        (codec.observe i r .expanded).toNat == v[3]!.toNat do
      throw (IO.userError s!"dense codec vector {count}")
    count := count+1
  IO.println s!"Dense structural codec matched {count} independent vectors."
