import Pinwheel.Hardware.Execution.RecordProofs
import Pinwheel.Binary.Execution

set_option maxRecDepth 4096

namespace Pinwheel.Hardware.Execution
open Engine.Reactive

abbrev Words := Vector (BitVec 64) 256

def imageWords (p : Image) : Words := p.memory.map encode

def directStore (words : Words) (idle : Pins) (last : Fin 256) : Fetch.Store 255 15 :=
  ⟨fun pc => decode words[pc.val], idle, last⟩

structure Indexed where
  dictionary : Vector (BitVec 64) 64
  addresses : Vector (BitVec 6) 256
  deriving DecidableEq, Repr

def Indexed.expand (image : Indexed) : Words :=
  Vector.ofFn fun pc => image.dictionary[image.addresses[pc.val].toNat]

def Indexed.store (image : Indexed) (idle : Pins) (last : Fin 256) : Fetch.Store 255 15 :=
  ⟨fun pc => decode image.dictionary[image.addresses[pc.val].toNat], idle, last⟩

/-- Bounded load-time deduplication plus an executable certificate check of all 256 lookups.
Programs with more than 64 distinct records are rejected, not truncated or silently expanded. -/
def lowerIndexed (words : Words) : Option {image : Indexed // image.expand = words} := do
  let unique := words.toList.eraseDups
  if unique.length > 64 then none else do
    let image : Indexed := {
      dictionary := Vector.ofFn fun k => unique[k.val]?.getD 4
      addresses := words.map (fun word => BitVec.ofNat 6 (unique.idxOf word)) }
    if h : image.expand = words then some ⟨image, h⟩ else none

theorem direct_agrees (p : Image) : Fetch.Agrees (directStore (imageWords p) p.idle p.last) p := by
  constructor <;> simp [directStore, imageWords, Program.fetch, decode_encode]
  done

theorem indexed_agrees (p : Image) (image : Indexed) (h : image.expand = imageWords p) :
    Fetch.Agrees (image.store p.idle p.last) p := by
  constructor
  · intro pc
    have hw := congrArg (fun words : Words => words[pc.val]) h
    simpa [Indexed.expand, Indexed.store, imageWords, Program.fetch, decode_encode] using congrArg decode hw
    done
  · rfl
  · rfl
  done

/-- Widen numeric operands without changing their value. V0 itself retains its old bounds. -/
def widenCapture (c : Capture) : Capture 15 := ⟨c.input, ⟨c.destination.val, by omega⟩⟩
def widenFinish : Finish → Finish 255 15
  | .sequential => .sequential
  | .jump pc => .jump ⟨pc.val, by omega⟩
  | .branch slot yes no => .branch ⟨slot.val, by omega⟩ ⟨yes.val, by omega⟩ ⟨no.val, by omega⟩
def widenAction (a : Action) : Action 15 := ⟨a.pins, a.durationMinusOne, a.capture.map widenCapture⟩
def widenInstruction : Instruction → Operation
  | .action a => .action (widenAction a)
  | .wait w => .wait w
  | .checked a => .checked ⟨widenAction a.action, a.guard, a.terminalCapture.map widenCapture, widenFinish a.finish⟩
  | .qualify q => .qualify q
  | .halt => .halt

def widenProgram (p : Program) : Image :=
  ⟨Vector.ofFn (fun pc => if h : pc.val < 128 then widenInstruction (p.fetch ⟨pc.val, h⟩) else .halt),
    p.idle, ⟨p.last.val, by omega⟩⟩

/-- Resolve counted operands once during loading; failed source fetch becomes an invalid opcode. -/
def lowerV0 (image : Pinwheel.Binary.Image) : Words :=
  Vector.ofFn fun pc => if h : pc.val < 128 then
    ((image.store.fetch ⟨pc.val, h⟩).map (encode ∘ widenInstruction)).getD 5 else encode .halt

end Pinwheel.Hardware.Execution
