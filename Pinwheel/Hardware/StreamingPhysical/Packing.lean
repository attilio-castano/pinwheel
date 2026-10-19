import Pinwheel.Hardware.Circuit
import Pinwheel.Hardware.StreamingMapped.Word

/-! A checked bit layout is a bijection, not a reachability restriction. It
therefore reconstructs every arbitrary physical FF valuation as typed state. -/
namespace Pinwheel.Hardware.StreamingPhysical

open Pinwheel.Hardware Pinwheel.Hardware.StreamingMapped

structure BitField (register : Nat → Type) where
  width : Nat
  field : register width
  bit : Fin width

def BitField.read (values : Values register) (bit : BitField register) : Bool :=
  (values bit.field).getLsbD bit.bit.val

instance [∀ width, DecidableEq (register width)] : DecidableEq (BitField register) := by
  intro left right
  cases left with
  | mk width field bit =>
    cases right with
    | mk otherWidth otherField otherBit =>
      if sameWidth : width = otherWidth then
        subst otherWidth
        if sameField : field = otherField then
          subst otherField
          if sameBit : bit = otherBit then
            exact isTrue (by cases sameBit; rfl)
          else exact isFalse (by intro same; cases same; exact sameBit rfl)
        else exact isFalse (by intro same; cases same; exact sameField rfl)
      else exact isFalse (by intro same; cases same; exact sameWidth rfl)

structure Packing (register : Nat → Type) (bits : Nat) where
  index : BitField register → Fin bits
  field : Fin bits → BitField register
  index_field : ∀ position, index (field position) = position
  field_index : ∀ bit, field (index bit) = bit

def Packing.encode (packing : Packing register bits) (values : Values register)
    (index : Fin bits) : Bool :=
  BitField.read values (packing.field index)

def Packing.decode (packing : Packing register bits) (values : Fin bits → Bool) : Values register :=
  fun field => Word.pack (fun bit => values (packing.index ⟨_,field,bit⟩))

theorem Packing.decode_bit (packing : Packing register bits) (values : Fin bits → Bool)
    (field : register width) (bit : Fin width) :
    (packing.decode values field).getLsbD bit.val = values (packing.index ⟨width,field,bit⟩) :=
  Word.pack_bit _ _ bit.isLt

theorem Packing.decode_encode (packing : Packing register bits) (values : Values register) :
    (@Packing.decode register bits packing (packing.encode values)) = @values := by
  funext width field
  apply Word.from_bits
  intro index within
  rw [packing.decode_bit _ field ⟨index,within⟩]
  exact congrArg (BitField.read values) (packing.field_index ⟨width,field,⟨index,within⟩⟩)

theorem Packing.encode_decode (packing : Packing register bits) (values : Fin bits → Bool) :
    packing.encode (packing.decode values) = values := by
  funext index
  change (packing.decode values (packing.field index).field).getLsbD
    (packing.field index).bit.val = values index
  rw [packing.decode_bit values (packing.field index).field (packing.field index).bit]
  exact congrArg values (packing.index_field index)

end Pinwheel.Hardware.StreamingPhysical
