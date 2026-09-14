import Pinwheel.Binary.Collections
import Pinwheel.Binary.Explicit
import Pinwheel.Binary.Layout

/-! PWL version 0. A complete externally framed byte sequence, with no trailing data.
This is a load-image format; it does not prescribe physical memory word widths. -/
namespace Pinwheel.Binary
open Engine.Reactive

inductive Image where
  | explicit (program : Program)
  | counted (program : Counted.Program)
  deriving Repr

def Image.store : Image → Fetch.Store
  | .explicit p => Fetch.Store.ofProgram p
  | .counted p => p.store

def magic : List Byte := [0x50, 0x57, 0x4c, 0]

def expect (expected : Byte) : Reader Unit := do
  let actual ← getFin 256
  if actual == expected then return () else fun _ => none

def encode : Image → List Byte
  | .explicit p => magic ++ putFin (by decide) (0 : Fin 2) ++ putPins p.idle ++
      putFin (by decide) p.last ++ putVector putInstruction p.memory
  | .counted p => magic ++ putFin (by decide) (1 : Fin 2) ++ putPins p.idle ++
      putVector (putBits (by decide)) p.data ++ putCode p.code

def getImage : Reader Image := do
  expect 0x50; expect 0x57; expect 0x4c; expect 0
  let kind ← getFin 2
  let idle ← getPins
  if kind.val == 0 then
    let last ← getFin 128
    let memory ← getVector getInstruction 128
    return .explicit ⟨memory, idle, last⟩
  else
    let data ← getVector (getBits 8) 2
    let code ← getCode 64
    if hs : code.span ≤ 128 then
      if hn : code.nodes ≤ 64 then
        if hd : code.nesting ≤ 2 then return .counted ⟨code, data, idle, hs, hn, hd⟩
        else fun _ => none
      else fun _ => none
    else fun _ => none

/-- Canonical whole-image validation rejects aliases, trailing bytes, and malformed headers.
The parser validates program bounds before an image becomes available for loading. -/
def decode (bytes : List Byte) : Option Image := do
  let (image, rest) ← getImage bytes
  if rest.isEmpty && encode image == bytes then some image else none

end Pinwheel.Binary
