import Pinwheel.Hardware.Streaming.Core
import Pinwheel.Program.StreamingCompile
import Pinwheel.Program.StreamingExecution

/-! Generic pin correspondence for every streaming cell, independent of protocols. -/
namespace Pinwheel.Hardware.Streaming.PinCorrespondence
open Pinwheel.Hardware Pinwheel.Program.Streaming

private def packedDrive (base : BitVec 3) (pin : Fin 3)
    (transmit mode invert : Bool) (bit : BitVec 1) (enabled : Bool) : BitVec 3 :=
  let shifted := if BitVec.ofBool invert = 1#1 then ~~~bit else bit
  let value := if enabled then (if BitVec.ofBool mode = 1#1 then ~~~shifted else 1#1)
    else (if BitVec.ofBool mode = 1#1 then 0#1 else shifted)
  let pick := fun k =>
    if (BitVec.ofBool transmit &&& BitVec.ofBool (decide
      (BitVec.ofNat 2 pin.val = BitVec.ofNat 2 k))) = 1#1 then value
    else base.extractLsb' k 1
  (pick 2 ++ pick 1) ++ pick 0

private def maskedDrive (base : BitVec 3) (pin : Fin 3)
    (transmit mode invert : Bool) (bit : BitVec 1) (enabled : Bool) : BitVec 3 :=
  let value := bit.getLsbD 0 != invert
  let mask : BitVec 3 := 1 <<< pin.val
  if transmit then
    if enabled then
      if mode then (base &&& ~~~mask) ||| (if value then 0 else mask)
      else base ||| mask
    else
      if mode then base &&& ~~~mask
      else (base &&& ~~~mask) ||| (if value then mask else 0)
  else base

private theorem packed_masked : ∀ (base : BitVec 3) (pin : Fin 3)
    (transmit mode invert : Bool) (bit : BitVec 1) (enabled : Bool),
    packedDrive base pin transmit mode invert bit enabled =
      maskedDrive base pin transmit mode invert bit enabled := by
  decide +kernel

theorem driven_fields (i : Values Core.Input) (r : Values (Core.Register a))
    (high enabled : Bool) (bit : Core.E a 1) (pin : Fin 3)
    (transmit mode invert : Bool)
    (tx : Core.transmit.eval i r = BitVec.ofBool transmit)
    (output : (Core.field 31 2 (by decide)).eval i r = BitVec.ofNat 2 pin.val)
    (enableMode : (Core.field 43 1 (by decide)).eval i r = BitVec.ofBool mode)
    (inverted : (Core.field 42 1 (by decide)).eval i r = BitVec.ofBool invert) :
    (Core.driven high enabled bit).eval i r =
      maskedDrive ((Core.basePins high enabled).eval i r) pin transmit mode invert (bit.eval i r) enabled := by
  have certificate := packed_masked ((Core.basePins high enabled).eval i r)
    pin transmit mode invert (bit.eval i r) enabled
  cases enabled <;> simpa only [Core.driven, Core.pack, Core.both, Expr.eval, tx, output, enableMode,
    inverted, packedDrive, Fin.val_zero, Fin.val_succ, Nat.reduceAdd, Bool.false_eq_true,
    ↓reduceIte, BitVec.ofNat_eq_ofNat] using certificate

private theorem either_value (x y : BitVec 3) : ~~~(~~~x &&& ~~~y) = x ||| y := by
  rw [BitVec.not_and, BitVec.not_not, BitVec.not_not]

private theorem not_and_ones (x : BitVec 3) : ~~~(~~~x &&& 7#3) = x := by
  rw [show 7#3 = BitVec.allOnes 3 from rfl, BitVec.and_allOnes, BitVec.not_not]

theorem base_fields (i : Values Core.Input) (r : Values (Core.Register a))
    (c : Cell) (opcode : BitVec 3) (high enabled last : Bool)
    (fields : WordFields (r .currentWord) c opcode)
    (lastValue : Core.lastCell.eval i r = BitVec.ofBool last) :
    (Core.basePins high enabled).eval i r =
      if enabled then (c.basePins high last).enabled else (c.basePins high last).levels := by
  rcases fields with ⟨op, lo, hi, ll, le, hl, he, tx, rx, tr, re, lll, lhl, ti, tm, lle, lhe, rs⟩
  cases high <;> cases enabled <;> cases last <;>
    simp_all [Core.basePins, Core.field, Core.either, Expr.eval, Cell.basePins, either_value]
  all_goals exact not_and_ones _

private theorem masked_dataPins (c : Cell) (high last enabled : Bool) (bit : BitVec 1) :
    maskedDrive (if enabled then (c.basePins high last).enabled else (c.basePins high last).levels)
      c.txOutput c.transmit c.txEnableMode c.txInvert bit enabled =
      if enabled then (c.dataPins high last (bit.getLsbD 0)).enabled
      else (c.dataPins high last (bit.getLsbD 0)).levels := by
  cases enabled <;> cases tx : c.transmit <;> cases mode : c.txEnableMode <;>
    simp [maskedDrive, Cell.dataPins, *]

theorem driven_stream (i : Values Core.Input) (r : Values (Core.Register a))
    (c : Cell) (high enabled : Bool) (bit : Core.E a 1)
    (word : r .currentWord = encode (.stream c)) :
    (Core.driven high enabled bit).eval i r =
      if enabled then (c.dataPins high (r .remaining == 1) ((bit.eval i r).getLsbD 0)).enabled
      else (c.dataPins high (r .remaining == 1) ((bit.eval i r).getLsbD 0)).levels := by
  have fields : WordFields (r .currentWord) c 1 := by
    simpa only [word, encode] using cellWord_fields c 1
  have stream : Core.stream.eval i r = BitVec.ofBool true := by
    simp [Core.stream, Core.field, Expr.eval, fields.operation]
  have transmit : Core.transmit.eval i r = BitVec.ofBool c.transmit := by
    simp only [Core.transmit, Core.both, Expr.eval, stream, Core.field, fields.transmit,
      BitVec.ofBool_and_ofBool, Bool.true_and]
  have last : Core.lastCell.eval i r = BitVec.ofBool (r .remaining == 1) := by
    simp only [Core.lastCell, Core.both, Expr.eval, stream,
      BitVec.ofBool_and_ofBool, Bool.true_and, Bool.beq_eq_decide_eq, BitVec.ofNat_eq_ofNat]
    rfl
  have actual := driven_fields i r high enabled bit c.txOutput c.transmit c.txEnableMode c.txInvert
    transmit (by simpa only [Core.field, Expr.eval] using fields.txOutput)
    (by simpa only [Core.field, Expr.eval] using fields.txEnableMode)
    (by simpa only [Core.field, Expr.eval] using fields.txInvert)
  rw [base_fields i r c 1 high enabled (r .remaining == 1) fields last] at actual
  exact actual.trans (masked_dataPins c high (r .remaining == 1) enabled (bit.eval i r))

theorem driven_pulse (i : Values Core.Input) (r : Values (Core.Register a))
    (c : Cell) (high enabled : Bool) (bit : Core.E a 1)
    (word : r .currentWord = encode (.pulse c)) :
    (Core.driven high enabled bit).eval i r =
      if enabled then (if high then c.highPins else c.lowPins).enabled
      else (if high then c.highPins else c.lowPins).levels := by
  have fields : WordFields (r .currentWord) c 0 := by
    simpa only [word, encode] using cellWord_fields c 0
  have stream : Core.stream.eval i r = BitVec.ofBool false := by
    simp [Core.stream, Core.field, Expr.eval, fields.operation]
  have transmit : Core.transmit.eval i r = BitVec.ofBool false := by
    simp [Core.transmit, Core.both, Expr.eval, stream]
  have last : Core.lastCell.eval i r = BitVec.ofBool false := by
    simp [Core.lastCell, Core.both, Expr.eval, stream]
  have actual := driven_fields i r high enabled bit c.txOutput false c.txEnableMode c.txInvert
    transmit (by simpa only [Core.field, Expr.eval] using fields.txOutput)
    (by simpa only [Core.field, Expr.eval] using fields.txEnableMode)
    (by simpa only [Core.field, Expr.eval] using fields.txInvert)
  rw [base_fields i r c 0 high enabled false fields last] at actual
  simpa only [maskedDrive, Bool.false_eq_true, ↓reduceIte, Cell.basePins] using actual

theorem driven_instruction (i : Values Core.Input) (r : Values (Core.Register a))
    (instruction : Instruction) (high enabled : Bool) (bit : Core.E a 1)
    (word : r .currentWord = encode instruction) :
    let pins := if instruction.isStream then
      instruction.cell.dataPins high (r .remaining == 1) ((bit.eval i r).getLsbD 0)
      else if high then instruction.cell.highPins else instruction.cell.lowPins
    (Core.driven high enabled bit).eval i r = if enabled then pins.enabled else pins.levels := by
  cases instruction with
  | pulse c => simpa only [Instruction.isStream, Instruction.cell, Bool.false_eq_true, ↓reduceIte] using
      driven_pulse i r c high enabled bit word
  | stream c => simpa only [Instruction.isStream, Instruction.cell, ↓reduceIte] using
      driven_stream i r c high enabled bit word
  | halt =>
    cases high <;> cases enabled <;>
      simp [Core.driven, Core.pack, Core.both, Core.transmit, Core.stream, Core.field,
        Core.basePins, Core.either, Core.lastCell, Expr.eval, word, encode,
        Instruction.isStream, Instruction.cell]
  | fault =>
    cases high <;> cases enabled <;>
      simp [Core.driven, Core.pack, Core.both, Core.transmit, Core.stream, Core.field,
        Core.basePins, Core.either, Core.lastCell, Expr.eval, word, encode,
        Instruction.isStream, Instruction.cell]

end Pinwheel.Hardware.Streaming.PinCorrespondence
