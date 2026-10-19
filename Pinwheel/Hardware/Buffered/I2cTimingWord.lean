import Pinwheel.Hardware.Buffered.I2cTimingSource

/-! Symbolic retiming of packed instruction fields. Loop controls and shared
branch descriptors are retained byte for byte. -/
namespace Pinwheel.Hardware.Buffered.I2cTiming
open Pinwheel.Hardware Pinwheel.Program GenericEncoding

def fields (duration budget : Fin 256) (f : Fields) : Fields :=
  {f with
    duration := if f.kind = 0 ∨ f.kind = 1 ∨ f.kind = 2 ∨ f.kind = 6 ∨ f.kind = 7
      then BitVec.ofNat 8 duration.val else f.duration
    budget := if f.kind = 5 ∨ f.kind = 7 then BitVec.ofNat 8 budget.val else f.budget}

theorem fields_instruction (duration budget : Fin 256) (i : Program.Buffered.Instruction) :
    fields duration budget (GenericEncoding.instruction i) =
      GenericEncoding.instruction (retime duration budget i) := by
  cases operation : i.operation
  all_goals simp [fields, retime, GenericEncoding.instruction, GenericEncoding.action,
    GenericEncoding.empty, operation]

def patchWord (duration budget : Fin 256) (word : BitVec 64) : BitVec 64 :=
  (fields duration budget (GenericEncoding.decode word)).word

theorem patch_encode (duration budget : Fin 256) (i : Program.Buffered.Instruction) :
    patchWord duration budget (GenericEncoding.encode i) =
      GenericEncoding.encode (retime duration budget i) := by
  unfold patchWord
  rw [GenericEncoding.decode_encode, fields_instruction]
  rfl

def patchRecord (duration budget : Fin 256) (record : BitVec 144) : BitVec 144 :=
  record.extractLsb' 88 56 ++ record.extractLsb' 64 24 ++
    patchWord duration budget (record.extractLsb' 0 64)

def fullWords (duration budget : Fin 256) (index : BitVec 6) : BitVec 144 :=
  if index.toNat < 50 then patchRecord duration budget (I2cSource.fullWords index) else 0

theorem patch_record (duration budget : Fin 256)
    (map : Program.Buffered.PC → GenericLayout.Coordinates) (control : BitVec 24)
    (i : Program.Buffered.Instruction) :
    patchRecord duration budget (GenericLayout.record map control i) =
      GenericLayout.record map control (retime duration budget i) := by
  simp (disch := decide) only [patchRecord, GenericLayout.record,
    BitVec.extractLsb'_append_eq_of_add_le, BitVec.extractLsb'_append_eq_of_le,
    BitVec.extractLsb'_eq_self, Nat.reduceSub, patch_encode, retime_finish]

theorem full_fields (duration budget : Fin 256) (index : BitVec 6) (live : index.toNat < 50) :
    (fullWords duration budget index).extractLsb' 0 64 = patchWord duration budget (I2cSource.word index) ∧
    (fullWords duration budget index).extractLsb' 64 24 = I2cSource.control index ∧
    (fullWords duration budget index).extractLsb' 88 56 = I2cSource.dictionary (I2cSource.branchIndex index) ∧
    (fullWords duration budget index).extractLsb' 64 22 = (I2cSource.control index).extractLsb' 0 22 := by
  simp (disch := decide) only [fullWords, live, ↓reduceIte, patchRecord, I2cSource.fullWords,
    BitVec.extractLsb'_append_eq_of_add_le, BitVec.extractLsb'_append_eq_of_le,
    BitVec.extractLsb'_eq_self, Nat.reduceSub]
  change True ∧ True ∧
    (I2cSource.dictionary (I2cSource.branchIndex index)).extractLsb' 0 56 =
      I2cSource.dictionary (I2cSource.branchIndex index) ∧ True
  simp only [BitVec.extractLsb'_eq_self, and_self]

theorem patch_kind (duration budget : Fin 256) (word : BitVec 64) :
    (patchWord duration budget word).extractLsb' 0 3 = word.extractLsb' 0 3 := by
  exact congrArg Fields.kind (GenericEncoding.decode_word (fields duration budget (GenericEncoding.decode word)))

end Pinwheel.Hardware.Buffered.I2cTiming
