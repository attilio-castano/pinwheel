import Pinwheel.Hardware.Loader.ProgramImage
import Pinwheel.Hardware.Storage.Small
import Pinwheel.Hardware.Loader.Program

/-! The words a host pushes for a program, and what they load.

`Loader.ProgramImage.upload p` is the 322-word stream for an image `p`: the dictionary,
the address map, the idle pins, the last address. This file shows that the
stream is what the loader wants and that the bank it leaves *is* the program:
`upload_holds` (`Machine.Holds p (imageOf ws)`), `upload_good` (every word passes
the loader's validation at its position) and, for images with at most 32
distinct records, `upload_fits` (every word passes the small store's capacity
check). With the upload theorem these give `program_loads`: deliver the stream
to a stopped machine and the engine is reset on `p`, ready to start. -/
namespace Pinwheel.Hardware.Storage.ProgramUpload
open Loader Loader.ProgramImage

variable {p : Execution.Image} {ws : List (BitVec 64)}

/-- The address map the lowering builds: each word's position among the distinct words. -/
theorem lowered_addresses (words : Execution.Words) (image : {image : Execution.Indexed // image.expand = words})
    (h : Execution.lowerIndexed words = some image) :
    image.val.addresses =
      words.map (fun word => BitVec.ofNat 6 ((words.toList.eraseDups).idxOf word)) := by
  unfold Execution.lowerIndexed at h
  dsimp only at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · rw [← Option.some.inj h]
    · exact absurd h (by simp)

/-- The stream, taken apart. -/
structure Stream (p : Execution.Image) (ws : List (BitVec 64)) : Prop where
  image : ∃ image : {image : Execution.Indexed // image.expand = Execution.imageWords p},
    Execution.lowerIndexed (Execution.imageWords p) = some image ∧
    ws = image.val.dictionary.toList ++ image.val.addresses.toList.map (·.zeroExtend 64) ++
      [(p.idle.enabled ++ p.idle.levels : BitVec 6).zeroExtend 64, BitVec.ofNat 64 p.last.val]

theorem stream (h : upload p = some ws) : Stream p ws := by
  unfold upload at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨image, himage, rfl⟩ := h
  exact ⟨image, himage, rfl⟩

section Parts
variable (image : Execution.Indexed) (idle last : BitVec 64)

private abbrev words : List (BitVec 64) :=
  image.dictionary.toList ++ image.addresses.toList.map (·.zeroExtend 64) ++ [idle, last]

theorem words_length : (words image idle last).length = 322 := by
  simp [words]

theorem words_word (k : Nat) (hk : k < 64) : (words image idle last).getD k 0 = image.dictionary[k] := by
  rw [List.getD_eq_getElem?_getD, words, List.append_assoc,
    List.getElem?_append_left (by simpa using hk)]
  simp [hk]

theorem words_index (a : Nat) (ha : a < 256) :
    (words image idle last).getD (64 + a) 0 = (image.addresses[a]).zeroExtend 64 := by
  rw [List.getD_eq_getElem?_getD, words, List.append_assoc,
    List.getElem?_append_right (by simp), List.getElem?_append_left (by simpa using ha)]
  simp [ha]

theorem words_idle : (words image idle last).getD 320 0 = idle := by
  rw [List.getD_eq_getElem?_getD, words, List.getElem?_append_right (by simp)]
  simp

theorem words_last : (words image idle last).getD 321 0 = last := by
  rw [List.getD_eq_getElem?_getD, words, List.getElem?_append_right (by simp)]
  simp

end Parts

private theorem extract_extend {n : Nat} (x : BitVec n) (h : n ≤ 64) :
    (x.zeroExtend 64).extractLsb' 0 n = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.zeroExtend, BitVec.getLsbD_setWidth, Nat.zero_add]
  have h64 : i < 64 := by omega
  simp [hi, h64]

/-- The length the loader expects. -/
theorem upload_length (h : upload p = some ws) : ws.length = 322 := by
  obtain ⟨image, _, rfl⟩ := (stream h).image
  exact words_length _ _ _

/-- **The bank the stream leaves reads as the program.** -/
theorem upload_holds (h : upload p = some ws) : Machine.Holds p (Machine.imageOf ws) := by
  obtain ⟨image, _, rfl⟩ := (stream h).image
  let idleW : BitVec 64 := (p.idle.enabled ++ p.idle.levels : BitVec 6).zeroExtend 64
  let lastW : BitVec 64 := BitVec.ofNat 64 p.last.val
  show Machine.Holds p (Machine.imageOf (words image.val idleW lastW))
  have hword (k : BitVec 6) :
      Machine.imageOf (words image.val idleW lastW) (.word k) = image.val.dictionary[k.toNat] := by
    have hk := k.isLt
    simp only [Machine.imageOf, Store.offset, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega), words_word _ _ _ _ hk, BitVec.extractLsb'_eq_self]
  have hindex (a : BitVec 8) :
      Machine.imageOf (words image.val idleW lastW) (.index a) = image.val.addresses[a.toNat] := by
    have ha := a.isLt
    simp only [Machine.imageOf, Store.offset, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega), words_index _ _ _ _ ha, extract_extend _ (by decide)]
  refine ⟨fun a => ?_, ?_, ?_⟩
  · have ha := a.isLt
    show Machine.imageOf (words image.val idleW lastW)
      (.word (Machine.imageOf (words image.val idleW lastW) (.index a))) = _
    rw [hindex, hword]
    have hexpand := congrArg (fun v => v[a.toNat]'ha) image.property
    simp only [Execution.Indexed.expand, Vector.getElem_ofFn, Execution.imageWords, Vector.getElem_map] at hexpand
    rw [hexpand]
    rfl
  · have hidle : Machine.imageOf (words image.val idleW lastW) .idle =
        (p.idle.enabled ++ p.idle.levels : BitVec 6) := by
      simp only [Machine.imageOf, Store.offset]
      rw [show (320 : BitVec 9).toNat = 320 from rfl, words_idle, extract_extend _ (by decide)]
    rw [hidle]
    have hl : (p.idle.enabled ++ p.idle.levels : BitVec 6).extractLsb' 0 3 = p.idle.levels := by
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
      simp [hi]
    have he : (p.idle.enabled ++ p.idle.levels : BitVec 6).extractLsb' 3 3 = p.idle.enabled := by
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
      simp [hi]
    rw [hl, he]
  · simp only [Machine.imageOf, Store.offset]
    rw [show (321 : BitVec 9).toNat = 321 from rfl, words_last]
    apply BitVec.eq_of_toNat_eq
    have hlast := p.last.isLt
    show ((BitVec.ofNat 64 p.last.val).extractLsb' 0 8).toNat = (BitVec.ofFin p.last : BitVec 8).toNat
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofFin, Nat.shiftRight_zero]
    omega

private theorem cursor_toNat (k : Nat) (hk : k < 322) : (BitVec.ofNat 9 k).toNat = k := by
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by omega)

private theorem extend_toNat {n : Nat} (x : BitVec n) (h : n ≤ 64) : (x.zeroExtend 64).toNat = x.toNat := by
  simp only [BitVec.zeroExtend, BitVec.toNat_setWidth]
  have hx := x.isLt
  have hpow : 2 ^ n ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) h
  exact Nat.mod_eq_of_lt (by omega)

/-- A dictionary entry is one of the program's records or the halt padding. -/
theorem dictionary_entry (image : {image : Execution.Indexed // image.expand = Execution.imageWords p})
    (himage : Execution.lowerIndexed (Execution.imageWords p) = some image) (k : Nat) (hk : k < 64) :
    image.val.dictionary[k] = ((Execution.imageWords p).toList.eraseDups)[k]?.getD 4 := by
  rw [lowered_dictionary _ image himage]
  simp

/-- **Every word of the stream passes the loader's validation at its position.** -/
theorem upload_good (h : upload p = some ws) (k : Nat) (hk : k < 322) :
    goodWord (BitVec.ofNat 9 k) (ws.getD k 0) = true := by
  obtain ⟨image, himage, rfl⟩ := (stream h).image
  unfold goodWord
  rw [cursor_toNat k hk]
  by_cases h64 : k < 64
  · rw [if_pos h64, words_word _ _ _ _ h64, dictionary_entry image himage k h64]
    cases hget : ((Execution.imageWords p).toList.eraseDups)[k]? with
    | none => decide
    | some word =>
      have hmem : word ∈ (Execution.imageWords p).toList :=
        List.mem_eraseDups.mp (List.mem_of_getElem? hget)
      simp only [Execution.imageWords, Vector.toList_map, List.mem_map] at hmem
      obtain ⟨op, _, rfl⟩ := hmem
      simp [Execution.valid_decode, Execution.decode_encode]
  · rw [if_neg h64]
    by_cases h320 : k < 320
    · obtain ⟨a, rfl⟩ : ∃ a, k = 64 + a := ⟨k - 64, by omega⟩
      have ha : a < 256 := by omega
      rw [if_pos (by omega), words_index _ _ _ _ ha, extend_toNat _ (by decide)]
      simpa using (image.val.addresses[a]).isLt
    · by_cases h320' : k = 320
      · subst h320'
        rw [if_pos (by decide), words_idle, extend_toNat _ (by decide)]
        simpa using (p.idle.enabled ++ p.idle.levels : BitVec 6).isLt
      · have h321 : k = 321 := by omega
        subst h321
        rw [if_neg (by decide), words_last]
        have hlast := p.last.isLt
        simp only [BitVec.toNat_ofNat, decide_eq_true_eq]
        omega

/-- The image has at most 32 distinct records: it fits the small dense store. -/
def Fits (p : Execution.Image) : Prop := ((Execution.imageWords p).toList.eraseDups).length ≤ 32

/-- **Every word of a fitting image's stream passes the small store's capacity check.** -/
theorem upload_fits (h : upload p = some ws) (hfits : Fits p) (k : Nat) (hk : k < 322) :
    Small.capacity (BitVec.ofNat 9 k) (ws.getD k 0) = true := by
  obtain ⟨image, himage, rfl⟩ := (stream h).image
  unfold Small.capacity
  rw [cursor_toNat k hk]
  by_cases h32 : k < 32
  · rw [if_pos h32]
  · rw [if_neg h32]
    by_cases h64 : k < 64
    · rw [if_pos h64, words_word _ _ _ _ h64, dictionary_entry image himage k h64]
      have hnone : ((Execution.imageWords p).toList.eraseDups)[k]? = none :=
        List.getElem?_eq_none (by unfold Fits at hfits; omega)
      rw [hnone]
      rfl
    · rw [if_neg h64]
      by_cases h320 : k < 320
      · obtain ⟨a, rfl⟩ : ∃ a, k = 64 + a := ⟨k - 64, by omega⟩
        have ha : a < 256 := by omega
        rw [if_pos (by omega), words_index _ _ _ _ ha, extend_toNat _ (by decide),
          lowered_addresses _ image himage, Vector.getElem_map]
        have hmem : (Execution.imageWords p)[a] ∈ (Execution.imageWords p).toList.eraseDups :=
          List.mem_eraseDups.mpr (by simp)
        have hidx := List.idxOf_lt_length_iff.mpr hmem
        unfold Fits at hfits
        simp only [BitVec.toNat_ofNat, decide_eq_true_eq]
        have : List.idxOf (Execution.imageWords p)[a] (Execution.imageWords p).toList.eraseDups < 32 := by omega
        omega
      · rw [if_neg h320]

/-- **Deliver a program's stream to a stopped machine and the engine is reset on
that program**, ready to start, with the bank that was active untouched. -/
theorem program_loads (A : BitVec 9 → BitVec 64 → Bool) (h : upload p = some ws)
    (hA : ∀ k, k < 322 → A (BitVec.ofNat 9 k) (ws.getD k 0) = true) (d₀ d₁ : BitVec 64)
    (history : List Machine.Inputs) (s : Machine.State)
    (hidle : Reactive.runningValue s.core = false)
    (hd : Machine.Delivers history (Machine.uploadCommands ws d₀ d₁)) :
    Machine.Running p (Engine.Reactive.reset p) (Machine.runWith A s history) :=
  (Machine.upload_loads A ws (upload_length h) (upload_good h) hA d₀ d₁ history s hidle hd).running p
    (upload_holds h)

end Pinwheel.Hardware.Storage.ProgramUpload
