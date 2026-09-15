import Pinwheel.Binary.Image

namespace Pinwheel.Binary
open Engine.Reactive

attribute [local simp] List.append_assoc Bind.bind Pure.pure Functor.map
  StateT.bind StateT.pure StateT.map fin_law bits_law pins_law

theorem expect_law (b : Byte) (rest : List Byte) :
    expect b (b :: rest) = some ((), rest) := by
  simp [expect, getFin, b.isLt]
  done

theorem image_law (image : Image) (rest : List Byte) :
    getImage (encode image ++ rest) = some (image, rest) := by
  cases image <;> rename_i p <;> cases p
  all_goals simp_all [encode, getImage, magic, expect_law,
    vector_law putInstruction getInstruction instruction_law,
    vector_law (putBits (show 2 ^ 8 ≤ 256 by decide)) (getBits 8) (bits_law 8 _), code_law]
  done

theorem decode_encode (image : Image) : decode (encode image) = some image := by
  simp [decode, show getImage (encode image) = some (image, []) by simpa using image_law image []]
  done

/-- Every accepted image has a unique byte representation; ignored or aliased bits cannot survive. -/
theorem encode_decode (bytes : List Byte) (image : Image) (h : decode bytes = some image) :
    encode image = bytes := by
  simp only [decode, Bind.bind, Option.bind_eq_some_iff] at h
  rcases h with ⟨⟨found, rest⟩, _, h⟩
  split at h <;> simp_all
  done

end Pinwheel.Binary
