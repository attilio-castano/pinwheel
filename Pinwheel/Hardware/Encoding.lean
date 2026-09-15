import Pinwheel.Engine.Proofs

/-! Canonical 16-bit instruction words for the first hardware implementation. -/
namespace Pinwheel.Hardware.Encoding

open Pinwheel.Engine

/-- Bits 15: opcode; 14:12: levels; 11:4: duration minus one; 3: capture; 2:0: slot. -/
def pack (levels : BitVec 3) (duration : BitVec 8) (capture : BitVec 4) : BitVec 16 :=
  0#1 ++ levels ++ duration ++ capture

def encode : Instruction → BitVec 16
  | .halt => 0x8000
  | .action a => pack a.levels (BitVec.ofFin a.durationMinusOne)
      (match a.capture with | none => 0 | some slot => 1#1 ++ (BitVec.ofFin slot : BitVec 3))

/-- Halt has zero payload; a disabled capture has zero slot bits. No noncanonical aliases. -/
def decode (word : BitVec 16) : Option Instruction :=
  if word[15] then
    if word = 0x8000 then some .halt else none
  else if word[3] then
    some (.action ⟨word.extractLsb' 12 3, (word.extractLsb' 4 8).toFin,
      some (word.extractLsb' 0 3).toFin⟩)
  else if word.extractLsb' 0 3 = 0 then
    some (.action ⟨word.extractLsb' 12 3, (word.extractLsb' 4 8).toFin, none⟩)
  else none

/-- Checked external conversion: reject instead of wrapping an out-of-range host value. -/
def wordFromNat (value : Nat) : Option (BitVec 16) :=
  if h : value < 65536 then some (BitVec.ofNatLT value h) else none

@[simp] theorem pack_fields (levels : BitVec 3) (duration : BitVec 8) (cap : BitVec 4) :
    (pack levels duration cap)[15] = false ∧
    (pack levels duration cap).extractLsb' 12 3 = levels ∧
    (pack levels duration cap).extractLsb' 4 8 = duration ∧
    (pack levels duration cap).extractLsb' 0 4 = cap ∧
    (pack levels duration cap)[3] = cap[3] ∧
    (pack levels duration cap).extractLsb' 0 3 = cap.extractLsb' 0 3 := by
  unfold pack
  bv_normalize

@[simp] theorem cap_fields (slot : BitVec 3) :
    (1#1 ++ slot)[3] = true ∧ (1#1 ++ slot).extractLsb' 0 3 = slot := by
  bv_normalize

theorem decode_encode (instruction : Instruction) : decode (encode instruction) = some instruction := by
  cases instruction with
  | halt => rfl
  | action a =>
    cases a with
    | mk levels duration cap =>
      cases cap <;> simp [encode, decode]

theorem reconstruct (word : BitVec 16) (h : word[15] = false) :
    pack (word.extractLsb' 12 3) (word.extractLsb' 4 8) (word.extractLsb' 0 4) = word := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [pack, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb', BitVec.getLsbD_zero]
  grind

theorem low_capture (word : BitVec 16) :
    (word[3] = true → 1#1 ++ word.extractLsb' 0 3 = word.extractLsb' 0 4) ∧
    (word[3] = false → word.extractLsb' 0 3 = 0 → word.extractLsb' 0 4 = 0) := by
  constructor
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb', BitVec.getLsbD_one]
    grind
  · intro h hz
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have bits := congrArg (fun v : BitVec 3 => v.getLsbD i) hz
    grind

theorem encode_decode (word : BitVec 16) (instruction : Instruction)
    (h : decode word = some instruction) : encode instruction = word := by
  simp only [decode] at h
  split at h <;> split at h <;> try simp only [Option.some.injEq, reduceCtorEq] at h
  all_goals try split at h
  all_goals simp_all only [Option.some.injEq, reduceCtorEq, Bool.not_eq_true]
  all_goals subst instruction
  all_goals simp only [encode, BitVec.ofFin_toFin]
  all_goals grind only [reconstruct, low_capture]

theorem checked_reject (value : Nat) (h : 65536 ≤ value) : wordFromNat value = none := by
  simp [wordFromNat, show ¬value < 65536 by omega]

theorem checked_exact (value : Nat) (word : BitVec 16) (h : wordFromNat value = some word) :
    word.toNat = value := by
  unfold wordFromNat at h
  split at h <;> simp_all
  subst word
  rfl

end Pinwheel.Hardware.Encoding
