import Pinwheel.Hardware.StreamingReady.Core
import Pinwheel.Program.StreamingReadyCompile
import Pinwheel.Program.StreamingReadyExecution

/-! Generic pin correspondence for every streaming cell, independent of protocols. -/
namespace Pinwheel.Hardware.StreamingReady.PinCorrespondence
open Pinwheel.Hardware Pinwheel.Program.StreamingReady

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
    (c : Cell) (opcode : BitVec 3) (guard : Guard) (guarded : Bool) (high enabled last : Bool)
    (fields : WordFields (r .currentWord) c opcode guard guarded)
    (lastValue : Core.lastCell.eval i r = BitVec.ofBool last) :
    (Core.basePins high enabled).eval i r =
      if enabled then (c.basePins high last).enabled else (c.basePins high last).levels := by
  rcases fields with ⟨op, lo, hi, ll, le, hl, he, tx, rx, tr, re, lll, lhl, ti, tm, lle, lhe, gm, ge, gb, hg, rs⟩
  cases high <;> cases enabled <;> cases last <;>
    simp_all [Core.basePins, Core.field, Core.either, Expr.eval, Pinwheel.Program.Streaming.Cell.basePins, either_value]
  all_goals exact not_and_ones _

private theorem masked_dataPins (c : Cell) (high last enabled : Bool) (bit : BitVec 1) :
    maskedDrive (if enabled then (c.basePins high last).enabled else (c.basePins high last).levels)
      c.txOutput c.transmit c.txEnableMode c.txInvert bit enabled =
      if enabled then (c.dataPins high last (bit.getLsbD 0)).enabled
      else (c.dataPins high last (bit.getLsbD 0)).levels := by
  cases enabled <;> cases tx : c.transmit <;> cases mode : c.txEnableMode <;>
    simp [maskedDrive, Pinwheel.Program.Streaming.Cell.dataPins, *]

theorem driven_instruction (i : Values Core.Input) (r : Values (Core.Register a))
    (instruction : Instruction) (high enabled : Bool) (bit : Core.E a 1)
    (word : r .currentWord = encode instruction) :
    let pins := if instruction.isStream then
      instruction.cell.dataPins high (r .remaining == 1) ((bit.eval i r).getLsbD 0)
      else if high then instruction.cell.highPins else instruction.cell.lowPins
    (Core.driven high enabled bit).eval i r = if enabled then pins.enabled else pins.levels := by
  have fields : WordFields (r .currentWord) instruction.cell (operation instruction)
      instruction.guard instruction.hasHighGuard := by
    simpa only [word] using encode_fields instruction
  have stream : Core.stream.eval i r = BitVec.ofBool instruction.isStream := by
    cases instruction <;> simp [Core.stream,Core.field,Expr.eval,fields.operation,
      operation,Instruction.isStream]
  have transmit : Core.transmit.eval i r = BitVec.ofBool
      (instruction.isStream && instruction.cell.transmit) := by
    simp only [Core.transmit,Core.both,Expr.eval,stream,Core.field,fields.transmit,
      BitVec.ofBool_and_ofBool]
  have last : Core.lastCell.eval i r = BitVec.ofBool
      (instruction.isStream && r .remaining == 1) := by
    simp only [Core.lastCell,Core.both,Expr.eval,stream,
      BitVec.ofBool_and_ofBool,Bool.beq_eq_decide_eq,BitVec.ofNat_eq_ofNat]
    rfl
  have actual := driven_fields i r high enabled bit instruction.cell.txOutput
    (instruction.isStream && instruction.cell.transmit) instruction.cell.txEnableMode
    instruction.cell.txInvert transmit
    (by simpa only [Core.field,Expr.eval] using fields.txOutput)
    (by simpa only [Core.field,Expr.eval] using fields.txEnableMode)
    (by simpa only [Core.field,Expr.eval] using fields.txInvert)
  rw [base_fields i r instruction.cell (operation instruction) instruction.guard
    instruction.hasHighGuard high enabled (instruction.isStream && r .remaining == 1) fields last] at actual
  cases hstream : instruction.isStream
  · simpa only [hstream,Bool.false_and,Bool.false_eq_true,↓reduceIte,maskedDrive,
      Pinwheel.Program.Streaming.Cell.basePins] using actual
  · simp only [hstream,Bool.true_and] at actual ⊢
    exact actual.trans (masked_dataPins instruction.cell high (r .remaining == 1) enabled (bit.eval i r))

end Pinwheel.Hardware.StreamingReady.PinCorrespondence
