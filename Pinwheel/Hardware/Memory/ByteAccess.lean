import Std.Tactic.BVDecide

/-! Pure accesses within one 32-bit little-endian word. This layer has no bus,
address-space, ownership, or memory-handshake semantics. Faulting stores retain
the supplied word; a later memory adapter must also suppress its write request.
-/
namespace Pinwheel.Hardware.Memory.ByteAccess

abbrev Word := BitVec 32
abbrev Offset := BitVec 2

inductive Size where
  | byte | half | word
  deriving DecidableEq, Repr

inductive Fault where
  | reservedSize | misaligned
  deriving DecidableEq, Repr

def Size.bytes : Size → Nat
  | .byte => 1
  | .half => 2
  | .word => 4

def decodeSize (raw : BitVec 2) : Except Fault Size :=
  if raw = 0 then .ok .byte else if raw = 1 then .ok .half
  else if raw = 2 then .ok .word else .error .reservedSize

def Aligned (size : Size) (offset : Offset) : Prop :=
  offset.toNat % size.bytes = 0

instance : Decidable (Aligned size offset) := inferInstanceAs (Decidable (_ % _ = 0))

def access (raw : BitVec 2) (offset : Offset) : Except Fault Size :=
  match decodeSize raw with
  | .error error => .error error
  | .ok size => if Aligned size offset then .ok size else .error .misaligned

/-- Lane zero is the least significant byte. -/
def byte (word : Word) (lane : Offset) : BitVec 8 :=
  word.extractLsb' (8 * lane.toNat) 8

def pack (lanes : Offset → BitVec 8) : Word :=
  lanes 3 ++ lanes 2 ++ lanes 1 ++ lanes 0

theorem raw_cases (raw : BitVec 2) : raw = 0 ∨ raw = 1 ∨ raw = 2 ∨ raw = 3 := by
  bv_omega

@[simp] theorem byte_pack (lanes : Offset → BitVec 8) (lane : Offset) :
    byte (pack lanes) lane = lanes lane := by
  rcases raw_cases lane with rfl | rfl | rfl | rfl <;> simp [byte, pack] <;> bv_decide

@[simp] theorem pack_byte (word : Word) : pack (byte word) = word := by
  simp [byte, pack]
  bv_decide

def Touched (size : Size) (offset lane : Offset) : Prop :=
  offset.toNat ≤ lane.toNat ∧ lane.toNat < offset.toNat + size.bytes

instance : Decidable (Touched size offset lane) := inferInstanceAs (Decidable (_ ∧ _))

/-- Replace consecutive lanes with low input-data bytes. Public access checking
prevents an unaligned or cross-word store from reaching this operation. -/
def storeCore (size : Size) (offset : Offset) (word data : Word) : Word :=
  pack fun lane => if Touched size offset lane then byte data (lane - offset) else byte word lane

def extend (signed : Bool) (value : BitVec w) : Word :=
  if signed then value.signExtend 32 else value.setWidth 32

def loadCore (size : Size) (signed : Bool) (offset : Offset) (word : Word) : Word :=
  match size with
  | .byte => extend signed (byte word offset)
  | .half => extend signed (byte word (offset + 1) ++ byte word offset)
  | .word => word

def load (raw : BitVec 2) (signed : Bool) (offset : Offset) (word : Word) : Except Fault Word :=
  match access raw offset with
  | .error error => .error error
  | .ok size => .ok (loadCore size signed offset word)

structure StoreResult where
  word : Word
  fault : Option Fault
  deriving DecidableEq, Repr

def store (raw : BitVec 2) (offset : Offset) (word data : Word) : StoreResult :=
  match access raw offset with
  | .error error => ⟨word, some error⟩
  | .ok size => ⟨storeCore size offset word data, none⟩

theorem storeCore_retained (size : Size) (offset lane : Offset) (word data : Word)
    (h : ¬Touched size offset lane) :
    byte (storeCore size offset word data) lane = byte word lane := by
  simp [storeCore, h]

theorem storeCore_written (size : Size) (offset lane : Offset) (word data : Word)
    (h : Touched size offset lane) :
    byte (storeCore size offset word data) lane = byte data (lane - offset) := by
  simp [storeCore, h]

theorem store_fault_atomic (raw : BitVec 2) (offset : Offset) (word data : Word)
    (error : Fault) (h : access raw offset = .error error) :
    store raw offset word data = ⟨word, some error⟩ := by
  simp [store, h]

theorem load_fault (raw : BitVec 2) (offset : Offset) (word : Word)
    (signed : Bool) (error : Fault) (h : access raw offset = .error error) :
    load raw signed offset word = .error error := by
  simp [load, h]

theorem alignment_cases (size : Size) (offset : Offset) :
    Aligned size offset ↔ size = .byte ∨
      (size = .half ∧ (offset = 0 ∨ offset = 2)) ∨ (size = .word ∧ offset = 0) := by
  rcases raw_cases offset with rfl | rfl | rfl | rfl <;> cases size <;> decide +kernel

theorem access_ok_iff (raw : BitVec 2) (offset : Offset) (size : Size) :
    access raw offset = .ok size ↔ decodeSize raw = .ok size ∧ Aligned size offset := by
  rcases raw_cases raw with rfl | rfl | rfl | rfl
  all_goals rcases raw_cases offset with rfl | rfl | rfl | rfl
  all_goals cases size <;> simp [access, decodeSize, Aligned, Size.bytes]

/-- Exhaustive classification of all sixteen raw size/offset pairs. Reserved
size wins over alignment; legal byte accesses use every lane. -/
theorem access_classification (raw : BitVec 2) (offset : Offset) :
    access raw offset =
      if raw = 0 then .ok .byte
      else if raw = 1 then
        if offset = 0 ∨ offset = 2 then .ok .half else .error .misaligned
      else if raw = 2 then
        if offset = 0 then .ok .word else .error .misaligned
      else .error .reservedSize := by
  rcases raw_cases raw with rfl | rfl | rfl | rfl
  all_goals rcases raw_cases offset with rfl | rfl | rfl | rfl
  all_goals rfl

theorem reserved_iff (raw : BitVec 2) (offset : Offset) :
    access raw offset = .error .reservedSize ↔ raw = 3 := by
  rcases raw_cases raw with rfl | rfl | rfl | rfl
  all_goals rcases raw_cases offset with rfl | rfl | rfl | rfl
  all_goals simp [access, decodeSize, Aligned, Size.bytes]

theorem misaligned_iff (raw : BitVec 2) (offset : Offset) :
    access raw offset = .error .misaligned ↔
      (raw = 1 ∧ (offset = 1 ∨ offset = 3)) ∨ (raw = 2 ∧ offset ≠ 0) := by
  rcases raw_cases raw with rfl | rfl | rfl | rfl
  all_goals rcases raw_cases offset with rfl | rfl | rfl | rfl
  all_goals simp [access, decodeSize, Aligned, Size.bytes]

theorem store_retained (raw : BitVec 2) (offset lane : Offset) (word data : Word) (size : Size)
    (h : access raw offset = .ok size) (untouched : ¬Touched size offset lane) :
    byte (store raw offset word data).word lane = byte word lane := by
  simpa only [store, h] using storeCore_retained size offset lane word data untouched

theorem store_written (raw : BitVec 2) (offset lane : Offset) (word data : Word) (size : Size)
    (h : access raw offset = .ok size) (touched : Touched size offset lane) :
    byte (store raw offset word data).word lane = byte data (lane - offset) := by
  simpa only [store, h] using storeCore_written size offset lane word data touched

theorem fault_preserves_word (raw : BitVec 2) (offset : Offset) (word data : Word) (error : Fault)
    (h : (store raw offset word data).fault = some error) :
    (store raw offset word data).word = word := by
  cases ha : access raw offset <;> simp_all [store]

theorem storeCore_readback (size : Size) (signed : Bool) (offset : Offset) (word data : Word)
    (h : Aligned size offset) :
    loadCore size signed offset (storeCore size offset word data) = loadCore size signed 0 data := by
  rcases raw_cases offset with rfl | rfl | rfl | rfl
  all_goals cases size <;> simp_all [Aligned, Size.bytes, loadCore, storeCore, Touched]
  have hlt (lane : Offset) : lane.toNat < 4 := lane.isLt
  simp [hlt]

theorem aligned_fits (size : Size) (offset : Offset) (h : Aligned size offset) :
    offset.toNat + size.bytes ≤ 4 := by
  rcases raw_cases offset with rfl | rfl | rfl | rfl
  all_goals cases size <;> simp_all [Aligned, Size.bytes]

theorem load_after_store (raw : BitVec 2) (signed : Bool) (offset : Offset) (word data : Word)
    (size : Size) (h : access raw offset = .ok size) :
    load raw signed offset (store raw offset word data).word = .ok (loadCore size signed 0 data) := by
  simpa only [load, store, h, Except.ok.injEq] using
    storeCore_readback size signed offset word data ((access_ok_iff raw offset size).mp h).2

theorem store_success (raw : BitVec 2) (offset : Offset) (word data : Word)
    (size : Size) (h : access raw offset = .ok size) :
    (store raw offset word data).fault = none := by
  simp [store, h]

theorem extend_byte (signed : Bool) (value : BitVec 8) :
    extend signed value = (if signed && value.msb then (-1 : BitVec 24) else 0) ++ value := by
  cases signed <;> simp [extend] <;> bv_decide

theorem extend_half (signed : Bool) (value : BitVec 16) :
    extend signed value = (if signed && value.msb then (-1 : BitVec 16) else 0) ++ value := by
  cases signed <;> simp [extend] <;> bv_decide

theorem load_byte (signed : Bool) (offset : Offset) (word : Word) :
    load 0 signed offset word = .ok
      ((if signed && (byte word offset).msb then (-1 : BitVec 24) else 0) ++ byte word offset) := by
  simp [load, access, decodeSize, Aligned, Size.bytes, Nat.mod_one, loadCore, extend_byte]

theorem load_half (signed : Bool) (offset : Offset) (word : Word)
    (h : Aligned .half offset) :
    load 1 signed offset word = .ok
      ((if signed && (byte word (offset + 1)).msb then (-1 : BitVec 16) else 0) ++
        (byte word (offset + 1) ++ byte word offset)) := by
  simp [load, access, decodeSize, h, loadCore, extend_half]
  bv_decide

theorem load_word (signed : Bool) (word : Word) : load 2 signed 0 word = .ok word := by
  rfl

theorem store_word (word data : Word) : store 2 0 word data = ⟨data, none⟩ := by
  have h := storeCore_readback .word false 0 word data (by decide +kernel)
  change StoreResult.mk (storeCore .word 0 word data) none = StoreResult.mk data none
  simpa only [loadCore] using congrArg (fun v => StoreResult.mk v none) h

end Pinwheel.Hardware.Memory.ByteAccess
