import Pinwheel.Program.Buffered
import Pinwheel.Hardware.Buffered.Reactive

/-! Static fields of a buffered instruction word. Encoding and decoding are
independent of controller state, execution traces, or observed pin values. -/
namespace Pinwheel.Hardware.Buffered.GenericEncoding
open Pinwheel.Hardware Pinwheel.Program

structure Fields where
  kind : BitVec 3
  levels : BitVec 3
  enabled : BitVec 3
  duration : BitVec 8
  preserveLevels : BitVec 3
  output : BitVec 2
  append : BitVec 2
  shiftEnable : BitVec 1
  invert : BitVec 1
  preserveEnabled : BitVec 3
  capture : BitVec 6
  terminal : BitVec 6
  checkMask : BitVec 2
  checkValue : BitVec 2
  waitInput : BitVec 1
  waitLevel : BitVec 1
  budget : BitVec 8
  timeout : BitVec 1
  reserved : BitVec 8
  deriving DecidableEq, Repr

def Fields.word (f : Fields) : BitVec 64 :=
  f.reserved ++ f.timeout ++ f.budget ++ f.waitLevel ++ f.waitInput ++
  f.checkValue ++ f.checkMask ++ f.terminal ++ f.capture ++ f.preserveEnabled ++
  f.invert ++ f.shiftEnable ++ f.append ++ f.output ++ f.preserveLevels ++
  f.duration ++ f.enabled ++ f.levels ++ f.kind

def decode (word : BitVec 64) : Fields :=
  ⟨word.extractLsb' 0 3, word.extractLsb' 3 3, word.extractLsb' 6 3,
   word.extractLsb' 9 8, word.extractLsb' 17 3, word.extractLsb' 20 2,
   word.extractLsb' 22 2, word.extractLsb' 24 1, word.extractLsb' 25 1,
   word.extractLsb' 26 3, word.extractLsb' 29 6, word.extractLsb' 35 6,
   word.extractLsb' 41 2, word.extractLsb' 43 2, word.extractLsb' 45 1,
   word.extractLsb' 46 1, word.extractLsb' 47 8, word.extractLsb' 55 1,
   word.extractLsb' 56 8⟩

theorem decode_word (f : Fields) : decode f.word = f := by
  cases f
  simp only [decode, Fields.word]
  congr 1 <;> bv_decide
  done

theorem word_decode (word : BitVec 64) : (decode word).word = word := by
  simp only [decode, Fields.word]
  bv_decide
  done

def empty : Fields := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

def capture (c : Option (Engine.Reactive.Capture 15)) : BitVec 6 :=
  match c with
  | none => 0
  | some c => BitVec.ofNat 4 c.destination.val ++ BitVec.ofNat 1 c.input.val ++ (1 : BitVec 1)

def append (input : Option (Fin 2)) : BitVec 2 :=
  match input with | none => 0 | some input => BitVec.ofNat 2 (input.val + 1)

def action (a : Engine.Reactive.Action 15) : Fields :=
  { empty with
    levels := a.pins.levels
    enabled := a.pins.enabled
    duration := BitVec.ofNat 8 a.durationMinusOne.val
    capture := capture a.capture }

/-- Only operands that affect the corresponding source operation are encoded.
Branch destinations live in the separate 56-bit descriptor. -/
def instruction (i : Program.Buffered.Instruction) : Fields :=
  match i.operation with
  | .drive a => {action a with append := append i.append}
  | .shift pin enable invert a =>
    {action a with
      kind := 1
      output := BitVec.ofNat 2 pin.val
      shiftEnable := BitVec.ofBool enable
      invert := BitVec.ofBool invert
      append := append i.append}
  | .keep levels enabled a =>
    {action a with
      kind := 2
      preserveLevels := levels
      preserveEnabled := enabled
      append := append i.append}
  | .wait w =>
    {empty with
      kind := 5
      levels := w.pins.levels
      enabled := w.pins.enabled
      waitInput := BitVec.ofNat 1 w.condition.input.val
      waitLevel := BitVec.ofBool w.condition.level
      budget := BitVec.ofNat 8 w.budgetMinusOne.val
      preserveLevels := i.preserveLevels
      preserveEnabled := i.preserveEnabled
      append := append i.append}
  | .checked a guard terminal _ =>
    {action a with
      kind := 6
      terminal := capture terminal
      checkMask := guard.mask
      checkValue := guard.value
      preserveLevels := i.preserveLevels
      preserveEnabled := i.preserveEnabled
      append := append i.append}
  | .qualify q =>
    {empty with
      kind := 7
      levels := q.pins.levels
      enabled := q.pins.enabled
      duration := BitVec.ofNat 8 q.durationMinusOne.val
      budget := BitVec.ofNat 8 q.budgetMinusOne.val
      checkMask := q.condition.mask
      checkValue := q.condition.value
      preserveLevels := i.preserveLevels
      preserveEnabled := i.preserveEnabled
      append := append i.append}
  | .halt => {empty with kind := 3}
  | .fault reason => {empty with kind := 4, timeout := BitVec.ofBool (reason == .timeout)}

def encode (i : Program.Buffered.Instruction) : BitVec 64 := (instruction i).word

theorem decode_encode (i : Program.Buffered.Instruction) : decode (encode i) = instruction i :=
  decode_word _

end Pinwheel.Hardware.Buffered.GenericEncoding
