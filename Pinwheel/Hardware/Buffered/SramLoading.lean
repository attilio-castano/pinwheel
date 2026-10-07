import Pinwheel.Hardware.Buffered.SramState
import Pinwheel.Hardware.Buffered.SramCoverage

/-! An accepted-upload ledger for the actual closed-loop SRAM controller.
Unknown startup cells, metadata, dictionary entries and the START mirror remain
unspecified. Only actual accepted writes establish ledger values. COMMIT's tail
clearing is recorded independently of instruction storage. -/
namespace Pinwheel.Hardware.Buffered.SramLoading
open Pinwheel.Hardware
open SramState

structure Ledger where
  words : Memory.Sram.Model 6 64 2
  metadata : BitVec 6 → Option (BitVec 28)
  dictionary : BitVec 4 → Option (BitVec 56)
  start : Option (BitVec 64)

def Ledger.initial : Ledger := ⟨Memory.Sram.Model.initial, fun _ => none,
  fun _ => none, none⟩

def rowAccepted (s : State) (i : Values Reactive.Input) : Bool :=
  decide (Sram.rowWriting.eval (s.inputs i) s.registers = 1)
def tableAccepted (s : State) (i : Values Reactive.Input) : Bool :=
  decide (Sram.tableWriting.eval (s.inputs i) s.registers = 1)
def tailCleared (s : State) (i : Values Reactive.Input) (k : BitVec 6) : Bool :=
  decide (Sram.committing.eval (s.inputs i) s.registers = 1) &&
    decide ((i .count).toNat ≤ k.toNat)
def uploadedMetadata (i : Values Reactive.Input) : BitVec 28 :=
  (i .branch).extractLsb' 0 4 ++ i .control

def Ledger.step (t : Ledger) (s : State) (i : Values Reactive.Input) : Ledger where
  words := t.words.step (Sram.arrayRequest (s.inputs i) s.registers)
  metadata := fun k => if tailCleared s i k then some 0
    else if rowAccepted s i && i .address == k then some (uploadedMetadata i)
    else t.metadata k
  dictionary := fun k => if tableAccepted s i && (i .address).extractLsb' 0 4 == k
    then some (i .branch) else t.dictionary k
  start := if rowAccepted s i && i .address == 0 then some (i .word) else t.start

structure Agrees (s : State) (t : Ledger) : Prop where
  words : Memory.Sram.Related s.arrays t.words
  metadata : ∀ k v, t.metadata k = some v → s.registers (.metadata k) = v
  dictionary : ∀ k v, t.dictionary k = some v → s.registers (.branch k) = v
  start : ∀ v, t.start = some v → s.registers .startWord = v

theorem agrees_initial (s : State) : Agrees s Ledger.initial := by
  exact ⟨Memory.Sram.related_initial s.arrays, by simp [Ledger.initial],
    by simp [Ledger.initial], by simp [Ledger.initial]⟩

private theorem band_one : ∀ x y : BitVec 1, x &&& y = 1 ↔ x = 1 ∧ y = 1 := by
  decide +kernel

private theorem ofBool_one : ∀ b : Bool, BitVec.ofBool b = 1 ↔ b = true := by
  decide +kernel

private theorem not_ofBool_one : ∀ b : Bool, ~~~BitVec.ofBool b = 1 ↔ b = false := by
  decide +kernel

private theorem widened_index (k : BitVec 6) :
    (BitVec.ofNat 7 k.toNat).toNat = k.toNat := by
  simp only [BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (Nat.lt_trans k.isLt (by decide +kernel : 2^6 < 2^7))]

theorem metadata_step (s : State) (i : Values Reactive.Input) (k : BitVec 6) :
    (s.step i).registers (.metadata k) =
      if tailCleared s i k then 0
      else if rowAccepted s i && i .address == k then uploadedMetadata i
      else s.registers (.metadata k) := by
  simp only [State.step, Circuit.step, Sram.circuit, Sram.next, Expr.eval,
    State.inputs, widened_index, band_one, tailCleared, rowAccepted,
    uploadedMetadata, Bool.and_eq_true, ofBool_one, not_ofBool_one,
    decide_eq_true_eq, decide_eq_false_iff_not, Nat.not_lt, beq_iff_eq]
  by_cases ha : i .address = k <;> simp [ha]
  done

theorem dictionary_step (s : State) (i : Values Reactive.Input) (k : BitVec 4) :
    (s.step i).registers (.branch k) =
      if tableAccepted s i && (i .address).extractLsb' 0 4 == k then i .branch
      else s.registers (.branch k) := by
  simp only [State.step, Circuit.step, Sram.circuit, Sram.next, Expr.eval,
    State.inputs, band_one, tableAccepted, Bool.and_eq_true, ofBool_one,
    decide_eq_true_eq, beq_iff_eq]
  by_cases ha : (i .address).extractLsb' 0 4 = k <;> simp [ha]
  done

theorem start_step (s : State) (i : Values Reactive.Input) :
    (s.step i).registers .startWord =
      if rowAccepted s i && i .address == 0 then i .word
      else s.registers .startWord := by
  simp only [State.step, Circuit.step, Sram.circuit, Sram.next, Expr.eval,
    State.inputs, band_one, rowAccepted, Bool.and_eq_true, ofBool_one,
    decide_eq_true_eq, beq_iff_eq]
  by_cases ha : i .address = (0 : BitVec 6) <;> simp only [ha, decide_true,
    decide_false, Bool.false_eq_true, and_true, and_false, if_false]
  done

theorem metadata_agrees_step (s : State) (t : Ledger) (i : Values Reactive.Input)
    (h : Agrees s t) (k : BitVec 6) (v : BitVec 28)
    (hv : (t.step s i).metadata k = some v) :
    (s.step i).registers (.metadata k) = v := by
  simp only [Ledger.step] at hv
  rw [metadata_step]
  split <;> simp_all
  split <;> simp_all
  exact h.metadata k v hv
  done

theorem dictionary_agrees_step (s : State) (t : Ledger) (i : Values Reactive.Input)
    (h : Agrees s t) (k : BitVec 4) (v : BitVec 56)
    (hv : (t.step s i).dictionary k = some v) :
    (s.step i).registers (.branch k) = v := by
  grind [Ledger.step, dictionary_step, h.dictionary]
  done

theorem start_agrees_step (s : State) (t : Ledger) (i : Values Reactive.Input)
    (h : Agrees s t) (v : BitVec 64) (hv : (t.step s i).start = some v) :
    (s.step i).registers .startWord = v := by
  grind [Ledger.step, start_step, h.start]
  done

theorem agrees_step (s : State) (t : Ledger) (i : Values Reactive.Input)
    (h : Agrees s t) : Agrees (s.step i) (t.step s i) :=
  ⟨Memory.Sram.related_step (Sram.arrayRequest (s.inputs i) s.registers)
      s.arrays t.words h.words,
    metadata_agrees_step s t i h, dictionary_agrees_step s t i h,
    start_agrees_step s t i h⟩

def advance (pair : State × Ledger) (i : Values Reactive.Input) : State × Ledger :=
  (pair.1.step i, pair.2.step pair.1 i)

def run (s : State) (t : Ledger) (inputs : List (Values Reactive.Input)) : State × Ledger :=
  inputs.foldl advance (s,t)

/-- Actual accepted requests, rather than a supplied write schedule, determine
every ledger update. This relation covers reset, rejected commands and runtime. -/
theorem agrees_run (inputs : List (Values Reactive.Input)) (s : State) (t : Ledger)
    (h : Agrees s t) : Agrees (run s t inputs).1 (run s t inputs).2 := by
  induction inputs generalizing s t with
  | nil => exact h
  | cons i rest ih => exact ih (s.step i) (t.step s i) (agrees_step s t i h)
  done

/-- Initializing the unknown ledger alone establishes memory agreement; this
does not initialize the hardware coverage masks. Use `initialized_loading` for
the initialized controller contract. -/
theorem independently_initialized_history (s : State)
    (inputs : List (Values Reactive.Input)) :
    Agrees (run s Ledger.initial inputs).1 (run s Ledger.initial inputs).2 :=
  agrees_run inputs s Ledger.initial (agrees_initial s)

theorem metadata_defined_step (s : State) (t : Ledger) (i : Values Reactive.Input)
    (k : BitVec 6) (h : ∃ v, t.metadata k = some v) :
    ∃ v, (t.step s i).metadata k = some v := by
  grind [Ledger.step]
  done

theorem dictionary_defined_step (s : State) (t : Ledger) (i : Values Reactive.Input)
    (k : BitVec 4) (h : ∃ v, t.dictionary k = some v) :
    ∃ v, (t.step s i).dictionary k = some v := by
  grind [Ledger.step]
  done

theorem word_contents_step (s : State) (t : Ledger) (i : Values Reactive.Input)
    (k : BitVec 6) :
    (t.step s i).words.contents k =
      if rowAccepted s i && i .address == k then some (i .word)
      else t.words.contents k := by
  dsimp only [Ledger.step, Memory.Sram.Model.step, Sram.arrayRequest,
    Sram.request, Expr.eval, rowAccepted, State.inputs]
  by_cases hw : Sram.rowWriting.eval (s.inputs i) s.registers = 1 <;>
    simp only [hw, decide_true, decide_false, if_true, if_false,
      Bool.true_and, Bool.false_and, Bool.false_eq_true]
  done

structure Coherent (t : Ledger) : Prop where
  metadata : ∀ k, t.words.Defined k → ∃ v, t.metadata k = some v
  start : ∀ v, t.words.contents 0 = some v → t.start = some v

theorem coherent_initial : Coherent Ledger.initial := by
  constructor <;> simp [Ledger.initial, Memory.Sram.Model.Defined, Memory.Sram.Model.initial]
  done

theorem coherent_metadata_step (s : State) (t : Ledger) (i : Values Reactive.Input)
    (h : Coherent t) (k : BitVec 6) (hw : (t.step s i).words.Defined k) :
    ∃ v, (t.step s i).metadata k = some v := by
  obtain ⟨v,hv⟩ := hw
  rw [word_contents_step] at hv
  simp only [Ledger.step]
  split <;> simp_all
  split <;> simp_all
  exact h.metadata k ⟨v,hv⟩
  done

theorem coherent_start_step (s : State) (t : Ledger) (i : Values Reactive.Input)
    (h : Coherent t) (v : BitVec 64) (hv : (t.step s i).words.contents 0 = some v) :
    (t.step s i).start = some v := by
  rw [word_contents_step] at hv
  simp only [Ledger.step]
  split <;> simp_all
  apply h.start v
  grind
  done

theorem coherent_step (s : State) (t : Ledger) (i : Values Reactive.Input)
    (h : Coherent t) : Coherent (t.step s i) :=
  ⟨coherent_metadata_step s t i h, coherent_start_step s t i h⟩

theorem coherent_run (inputs : List (Values Reactive.Input)) (s : State) (t : Ledger)
    (h : Coherent t) : Coherent (run s t inputs).2 := by
  induction inputs generalizing s t with
  | nil => exact h
  | cons i rest ih => exact ih (s.step i) (t.step s i) (coherent_step s t i h)
  done

def Ledger.instructions (t : Ledger) : Memory.Contents 6 64 :=
  fun k => (t.words.contents k).getD 0
def Ledger.rows (t : Ledger) : Memory.Contents 6 92 :=
  fun k => (t.metadata k).getD 0 ++ t.instructions k
def Ledger.dictionaryWords (t : Ledger) : Memory.Contents 4 56 :=
  fun k => (t.dictionary k).getD 0

theorem row_defined_write (s : State) (t : Ledger) (i : Values Reactive.Input)
    (k : BitVec 6) (hw : rowAccepted s i = true) (ha : i .address = k) :
    (t.step s i).words.Defined k := by
  exact ⟨i .word, by simp [word_contents_step, hw, ha]⟩

theorem dictionary_defined_write (s : State) (t : Ledger) (i : Values Reactive.Input)
    (k : BitVec 4) (hw : tableAccepted s i = true)
    (ha : (i .address).extractLsb' 0 4 = k) :
    ∃ v, (t.step s i).dictionary k = some v := by
  exact ⟨i .branch, by simp [Ledger.step, hw, ha]⟩

theorem known_word (s : State) (t : Ledger) (h : Agrees s t)
    (k : BitVec 6) (hk : t.words.Defined k) (port : Fin 2) :
    (s.arrays port).contents k = t.instructions k := by
  obtain ⟨v,hv⟩ := hk
  simpa [Ledger.instructions, hv] using (h.words port).1 k v hv
  done

theorem known_metadata (s : State) (t : Ledger) (h : Agrees s t) (hc : Coherent t)
    (k : BitVec 6) (hk : t.words.Defined k) :
    s.registers (.metadata k) = (t.rows k).extractLsb' 64 28 := by
  obtain ⟨v,hv⟩ := hc.metadata k hk
  change s.registers (.metadata k) =
    (((t.metadata k).getD 0 : BitVec 28) ++ t.instructions k).extractLsb' 64 28
  rw [BitVec.extractLsb'_append_eq_left, hv]
  exact h.metadata k v hv
  done

theorem row_word (t : Ledger) (k : BitVec 6) :
    (t.rows k).extractLsb' 0 64 = t.instructions k := by
  change (((t.metadata k).getD 0 : BitVec 28) ++ t.instructions k).extractLsb' 0 64 = _
  simp only [BitVec.extractLsb'_append_eq_of_add_le (by decide : 0+64 ≤ 64),
    BitVec.extractLsb'_eq_self]
  done

theorem known_dictionary (s : State) (t : Ledger) (h : Agrees s t)
    (k : BitVec 4) (hk : ∃ v, t.dictionary k = some v) :
    s.registers (.branch k) = t.dictionaryWords k := by
  obtain ⟨v,hv⟩ := hk
  simpa only [Ledger.dictionaryWords, hv, Option.getD_some] using h.dictionary k v hv
  done

theorem known_start (s : State) (t : Ledger) (h : Agrees s t) (hc : Coherent t)
    (hk : t.words.Defined 0) : s.registers .startWord = t.instructions 0 := by
  obtain ⟨v,hv⟩ := hk
  simpa only [Ledger.instructions, hv, Option.getD_some] using h.start v (hc.start v hv)
  done

structure Covered (s : State) (t : Ledger) : Prop where
  rows : ∀ k, (s.registers (.core .written)).getLsbD k.toNat = true → t.words.Defined k
  dictionary : ∀ k, (s.registers .branchWritten).getLsbD k.toNat = true →
    ∃ v, t.dictionary k = some v

theorem covered_cold (s : State) (i : Values Reactive.Input) (hi : i .initialize = 1)
    (t : Ledger) : Covered (s.step i) t := by
  have h := SramCoverage.cold_masks (s.inputs i) s.registers hi
  constructor <;> simp only [State.step, h.1, h.2]
  all_goals simp
  done

theorem covered_rows_step (s : State) (t : Ledger) (i : Values Reactive.Input)
    (h : Covered s t) (k : BitVec 6)
    (hk : ((s.step i).registers (.core .written)).getLsbD k.toNat = true) :
    (t.step s i).words.Defined k := by
  rcases SramCoverage.row_mask_provenance (s.inputs i) s.registers k hk with hw | hold
  · exact row_defined_write s t i k (by simpa only [rowAccepted, decide_eq_true_eq] using hw.1) hw.2
  · exact t.words.defined_step _ k (h.rows k hold)
  done

theorem covered_dictionary_step (s : State) (t : Ledger) (i : Values Reactive.Input)
    (h : Covered s t) (k : BitVec 4)
    (hk : ((s.step i).registers .branchWritten).getLsbD k.toNat = true) :
    ∃ v, (t.step s i).dictionary k = some v := by
  rcases SramCoverage.dictionary_mask_provenance (s.inputs i) s.registers k hk with hw | hold
  · exact dictionary_defined_write s t i k
      (by simpa only [tableAccepted, decide_eq_true_eq] using hw.1) hw.2
  · exact dictionary_defined_step s t i k (h.dictionary k hold)
  done

theorem covered_step (s : State) (t : Ledger) (i : Values Reactive.Input)
    (h : Covered s t) : Covered (s.step i) (t.step s i) :=
  ⟨covered_rows_step s t i h, covered_dictionary_step s t i h⟩

theorem covered_run (inputs : List (Values Reactive.Input)) (s : State) (t : Ledger)
    (h : Covered s t) : Covered (run s t inputs).1 (run s t inputs).2 := by
  induction inputs generalizing s t with
  | nil => exact h
  | cons i rest ih => exact ih (s.step i) (t.step s i) (covered_step s t i h)
  done

/-- Cold initialization discards arbitrary coverage bits; accepted history then
establishes every covered word and dictionary slot. It never assumes cleared
SRAM contents or equal memory copies, metadata, dictionary values or Q.
-/
theorem initialized_loading (s : State) (i : Values Reactive.Input)
    (hi : i .initialize = 1) (inputs : List (Values Reactive.Input)) :
    let after := run (s.step i) Ledger.initial inputs
    Agrees after.1 after.2 ∧ Coherent after.2 ∧ Covered after.1 after.2 :=
  ⟨agrees_run inputs (s.step i) Ledger.initial (agrees_initial _),
    coherent_run inputs (s.step i) Ledger.initial coherent_initial,
    covered_run inputs (s.step i) Ledger.initial (covered_cold s i hi _)⟩

end Pinwheel.Hardware.Buffered.SramLoading
