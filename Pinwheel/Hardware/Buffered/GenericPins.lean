import Pinwheel.Hardware.Buffered.GenericWord

/-! Actual entry pin commands agree with the source operation's normalized
pins. SHIFT may select any output pin, its level or enable, and invert the bit.
Preservation masks combine old pins with the newly encoded command. -/
namespace Pinwheel.Hardware.Buffered.GenericPins
open Pinwheel.Hardware Pinwheel.Program Pinwheel.Engine.Reactive

def pins (instruction : Program.Buffered.Instruction) (old : Pins) (txBit : Bool) : Pins :=
  match instruction.operation with
  | .drive a => a.pins
  | .shift pin enable invert a => Program.Buffered.shiftPins a.pins pin enable invert txBit
  | .keep levels enabled a => Program.Buffered.keepPins a.pins old levels enabled
  | .wait w => Program.Buffered.keepPins w.pins old
      instruction.preserveLevels instruction.preserveEnabled
  | .checked a _ _ _ => Program.Buffered.keepPins a.pins old
      instruction.preserveLevels instruction.preserveEnabled
  | .qualify q => Program.Buffered.keepPins q.pins old
      instruction.preserveLevels instruction.preserveEnabled
  | .halt | .fault _ => ⟨0, 0⟩

private theorem either_value (a b : BitVec 3) : ~~~(~~~a &&& ~~~b) = a ||| b := by
  rw [BitVec.not_and, BitVec.not_not, BitVec.not_not]

private theorem preserve_zero : ∀ base old : BitVec 3,
    base &&& ~~~(0 : BitVec 3) ||| old &&& (0 : BitVec 3) = base := by
  decide +kernel

private def shiftedValue (base : BitVec 3) (bit : BitVec 1) (pin : Fin 3) (invert : Bool) : BitVec 3 :=
  let shifted := if BitVec.ofBool invert = (1 : BitVec 1) then ~~~bit else bit
  ((if BitVec.ofBool (decide (BitVec.ofNat 2 pin.val = BitVec.ofNat 2 2)) = (1 : BitVec 1)
      then shifted else base.extractLsb' 2 1) ++
    (if BitVec.ofBool (decide (BitVec.ofNat 2 pin.val = BitVec.ofNat 2 1)) = (1 : BitVec 1)
      then shifted else base.extractLsb' 1 1)) ++
    (if BitVec.ofBool (decide (BitVec.ofNat 2 pin.val = BitVec.ofNat 2 0)) = (1 : BitVec 1)
      then shifted else base.extractLsb' 0 1)

private theorem shifted_certificate : ∀ (base : BitVec 3) (bit : BitVec 1) (pin : Fin 3) (invert : Bool),
    shiftedValue base bit pin invert = Program.Buffered.setBit base pin (bit.getLsbD 0 != invert) := by
  decide +kernel

theorem shifted_matches (i : Values Reactive.Input) (r : Values Reactive.Register)
    (base : Reactive.E 3) (pin : Fin 3) (invert : Bool)
    (output : (Reactive.entryWord.eval i r).extractLsb' 20 2 = BitVec.ofNat 2 pin.val)
    (inverted : (Reactive.entryWord.eval i r).extractLsb' 25 1 = BitVec.ofBool invert) :
    (Reactive.shifted base).eval i r =
      Program.Buffered.setBit (base.eval i r) pin
        ((Reactive.entryTx.eval i r).getLsbD 0 != invert) := by
  have h := shifted_certificate (base.eval i r) ((Reactive.entryTx.eval i r).extractLsb' 0 1) pin invert
  simpa only [Reactive.shifted, Reactive.pack, Reactive.shiftValue, Expr.eval, output, inverted,
    Fin.val_zero, Fin.val_succ, shiftedValue, BitVec.getLsbD_extractLsb', Nat.zero_add,
    Nat.reduceAdd, show decide (0 < (1 : Nat)) = true from rfl, Bool.true_and] using h

theorem entry_pins (instruction : Program.Buffered.Instruction)
    (i : Values Reactive.Input) (r : Values Reactive.Register)
    (word : Reactive.entryWord.eval i r = GenericEncoding.encode instruction) :
    (⟨Reactive.entryLevels.eval i r, Reactive.entryEnabled.eval i r⟩ : Pins) =
      pins instruction ⟨r .levels, r .enabled⟩ ((Reactive.entryTx.eval i r).getLsbD 0) := by
  rcases instruction with ⟨operation, append, preserveLevels, preserveEnabled⟩
  cases operation
  case shift pin enable invert action =>
    have output : (Reactive.entryWord.eval i r).extractLsb' 20 2 = BitVec.ofNat 2 pin.val := by
      simp only [word, GenericWord.output_field, GenericEncoding.instruction]
    have inverted : (Reactive.entryWord.eval i r).extractLsb' 25 1 = BitVec.ofBool invert := by
      simp only [word, GenericWord.invert_field, GenericEncoding.instruction]
    have shiftedLevels := shifted_matches i r (.slice 3 3 (by decide) Reactive.entryWord)
      pin invert output inverted
    have shiftedEnabled := shifted_matches i r (.slice 6 3 (by decide) Reactive.entryWord)
      pin invert output inverted
    simp only [Reactive.entryLevels, Reactive.entryEnabled, Reactive.isKind, Reactive.kind,
      Expr.eval, shiftedLevels, shiftedEnabled, word, GenericWord.kind_field,
      GenericWord.levels_field, GenericWord.enabled_field, GenericWord.shiftEnable_field,
      GenericEncoding.instruction, GenericEncoding.action, GenericEncoding.empty,
      pins, Program.Buffered.shiftPins]
    cases enable <;> rfl
  all_goals simp only [Reactive.entryLevels, Reactive.entryEnabled, Reactive.isKind,
    Reactive.kind, Reactive.preserve, Reactive.either, Expr.eval, word,
    GenericWord.kind_field, GenericWord.levels_field, GenericWord.enabled_field,
    GenericWord.preserveLevels_field, GenericWord.preserveEnabled_field,
    GenericEncoding.instruction, GenericEncoding.action, GenericEncoding.empty,
    pins, Program.Buffered.keepPins]
  all_goals simp only [either_value, preserve_zero]
  all_goals simp
  done

end Pinwheel.Hardware.Buffered.GenericPins
