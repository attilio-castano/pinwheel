import Pinwheel.Hardware.Execution.Images

/-! The host upload format, independent of a backend's admissibility rule. -/
namespace Pinwheel.Hardware.Loader.ProgramImage

/-- The 322 words the host pushes for an image: the dictionary, the addresses,
the idle pins and the last address. -/
def upload (p : Execution.Image) : Option (List (BitVec 64)) :=
  (Execution.lowerIndexed (Execution.imageWords p)).map fun image =>
    image.val.dictionary.toList ++ image.val.addresses.toList.map (·.zeroExtend 64) ++
      [(p.idle.enabled ++ p.idle.levels : BitVec 6).zeroExtend 64, BitVec.ofNat 64 p.last.val]

/-- The dictionary the lowering builds: the distinct words in order, padded with halt. -/
theorem lowered_dictionary (words : Execution.Words) (image : {image : Execution.Indexed // image.expand = words})
    (h : Execution.lowerIndexed words = some image) :
    image.val.dictionary = Vector.ofFn fun k => (words.toList.eraseDups)[k.val]?.getD 4 := by
  unfold Execution.lowerIndexed at h
  dsimp only at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · rw [← Option.some.inj h]
    · exact absurd h (by simp)

end Pinwheel.Hardware.Loader.ProgramImage
