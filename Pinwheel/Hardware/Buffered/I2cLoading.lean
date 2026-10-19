import Pinwheel.Hardware.Buffered.I2cSource
import Pinwheel.Hardware.Buffered.SramCorrespondence

/-! Accepted-upload provenance for the fixed reactive I²C source image.
Only operands of actual accepted commands are constrained. Initial SRAM cells,
replicas, registered responses, metadata and branch words are arbitrary. -/
namespace Pinwheel.Hardware.Buffered.I2cLoading
open Pinwheel.Hardware
open I2cSource

/-- Accepted rows constrain the effective dictionary index, not ignored high
bits of the shared upload operand. Accepted COMMIT fixes source geometry. -/
structure SourceInput (s : SramState.State) (i : Values Reactive.Input) : Prop where
  row : SramLoading.rowAccepted s i = true → i .word = word (i .address) ∧
    i .control = control (i .address) ∧
    (i .branch).extractLsb' 0 4 = branchIndex (i .address)
  table : SramLoading.tableAccepted s i = true →
    i .branch = dictionary ((i .address).extractLsb' 0 4)
  commit : Sram.committing.eval (s.inputs i) s.registers = 1 →
    i .count = 50 ∧ i .virtualSpan = 270 ∧
    i .idleLevels = 0 ∧ i .idleEnabled = 0

structure Known (t : SramLoading.Ledger) : Prop where
  words : ∀ k v, t.words.contents k = some v → v = word k
  metadata : ∀ k v, t.metadata k = some v → v = (branchIndex k ++ control k)
  dictionary : ∀ k v, t.dictionary k = some v → v = I2cSource.dictionary k

def SourceHistory : SramState.State → List (Values Reactive.Input) → Prop
  | _, [] => True
  | s, i :: rest => SourceInput s i ∧ SourceHistory (s.step i) rest

theorem known_initial : Known SramLoading.Ledger.initial := by
  constructor <;> simp [SramLoading.Ledger.initial, Memory.Sram.Model.initial]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem row_tail : ∀ k : BitVec 6, 50 ≤ k.toNat → rows k = 0 := by
  decide +kernel

theorem metadata_tail : ∀ k : BitVec 6, 50 ≤ k.toNat →
    branchIndex k ++ control k = 0 := by
  decide +kernel

theorem known_words_step (s : SramState.State) (t : SramLoading.Ledger)
    (i : Values Reactive.Input) (h : Known t) (hi : SourceInput s i)
    (k : BitVec 6) (v : BitVec 64) (hv : (t.step s i).words.contents k = some v) :
    v = word k := by
  rw [SramLoading.word_contents_step] at hv
  split at hv
  · rename_i hw
    have hs := hi.row (Bool.and_eq_true_iff.mp hw).1
    simpa only [Option.some.injEq, beq_iff_eq] using
      (Option.some.inj hv).symm.trans
        (hs.1.trans (congrArg word (of_decide_eq_true (Bool.and_eq_true_iff.mp hw).2)))
  · exact h.words k v hv
  done

theorem known_metadata_step (s : SramState.State) (t : SramLoading.Ledger)
    (i : Values Reactive.Input) (h : Known t) (hi : SourceInput s i)
    (k : BitVec 6) (v : BitVec 28) (hv : (t.step s i).metadata k = some v) :
    v = (branchIndex k ++ control k) := by
  simp only [SramLoading.Ledger.step] at hv
  split at hv
  · rename_i ht
    have hp := Bool.and_eq_true_iff.mp ht
    have hge : 50 ≤ k.toNat := by
      have hh := of_decide_eq_true hp.2
      change (i .count).toNat ≤ k.toNat at hh
      rw [(hi.commit (of_decide_eq_true hp.1)).1] at hh
      exact hh
    exact (Option.some.inj hv).symm.trans (metadata_tail k hge).symm
  · split at hv
    · rename_i hw
      rw [← Option.some.inj hv, SramLoading.uploadedMetadata,
        (hi.row (Bool.and_eq_true_iff.mp hw).1).2.2,
        (hi.row (Bool.and_eq_true_iff.mp hw).1).2.1,
        of_decide_eq_true (Bool.and_eq_true_iff.mp hw).2]
    · exact h.metadata k v hv
  done

theorem known_dictionary_step (s : SramState.State) (t : SramLoading.Ledger)
    (i : Values Reactive.Input) (h : Known t) (hi : SourceInput s i)
    (k : BitVec 4) (v : BitVec 56) (hv : (t.step s i).dictionary k = some v) :
    v = dictionary k := by
  simp only [SramLoading.Ledger.step] at hv
  split at hv
  · rename_i hw
    exact (Option.some.inj hv).symm.trans
      ((hi.table (Bool.and_eq_true_iff.mp hw).1).trans
        (congrArg dictionary (of_decide_eq_true (Bool.and_eq_true_iff.mp hw).2)))
  · exact h.dictionary k v hv
  done

theorem known_step (s : SramState.State) (t : SramLoading.Ledger)
    (i : Values Reactive.Input) (h : Known t) (hi : SourceInput s i) :
    Known (t.step s i) :=
  ⟨known_words_step s t i h hi, known_metadata_step s t i h hi,
    known_dictionary_step s t i h hi⟩

theorem known_run (s : SramState.State) (t : SramLoading.Ledger)
    (inputs : List (Values Reactive.Input)) (h : Known t) (hi : SourceHistory s inputs) :
    Known (SramLoading.run s t inputs).2 := by
  induction inputs generalizing s t with
  | nil => exact h
  | cons i rest ih => exact ih (s.step i) (t.step s i) (known_step s t i h hi.1) hi.2

private theorem dictionary_bit : ∀ k : BitVec 4,
    (65535 : BitVec 16).getLsbD k.toNat = true := by
  decide +kernel

/-- VALID coverage supplies defined values for every dictionary slot, notably
the nonzero ACK-branch descriptor in slot one. -/
theorem known_dictionary (s : SramState.State) (t : SramLoading.Ledger)
    (h : Known t) (he : SramCorrespondence.Established s t)
    (hv : s.registers (.core .valid) = 1) :
    t.dictionaryWords = dictionary := by
  funext k
  obtain ⟨v, hk⟩ := he.covered.dictionary k
    (by simpa only [(he.admitted hv).2] using dictionary_bit k)
  simpa only [SramLoading.Ledger.dictionaryWords, hk, Option.getD_some] using h.dictionary k v hk

theorem known_live_row (s : SramState.State) (t : SramLoading.Ledger)
    (h : Known t) (he : SramCorrespondence.Established s t)
    (hv : s.registers (.core .valid) = 1) (k : BitVec 6)
    (hk : SramExecution.live (s.registers (.core .count)) k = true) :
    t.rows k = rows k := by
  obtain ⟨w, hw⟩ := he.covered.rows k
    ((he.admitted hv).1 k (of_decide_eq_true hk))
  obtain ⟨m, hm⟩ := he.coherent.metadata k ⟨w, hw⟩
  simp only [SramLoading.Ledger.rows, SramLoading.Ledger.instructions, hw, hm,
    Option.getD_some, h.words k w hw, h.metadata k m hm, rows]
  exact BitVec.append_assoc

theorem projected_source_row (s : SramState.State) (t : SramLoading.Ledger)
    (h : Known t) (he : SramCorrespondence.Established s t)
    (hv : s.registers (.core .valid) = 1) (hc : s.registers (.core .count) = 50)
    (k : BitVec 6) : SramExecution.projectedRow 50 t.rows k = rows k := by
  change (if decide (k.toNat < 50) = true then t.rows k else 0) = rows k
  by_cases hk : k.toNat < 50
  · have hl : SramExecution.live (s.registers (.core .count)) k = true := by
      rw [hc]
      exact decide_eq_true hk
    simpa only [if_pos (decide_eq_true hk)] using known_live_row s t h he hv k hl
  · simp only [hk, decide_false, Bool.false_eq_true, if_false]
    exact (row_tail k (Nat.le_of_not_gt hk)).symm
  done

theorem resident_source_words (s : SramState.State) (t : SramLoading.Ledger)
    (h : Known t) (he : SramCorrespondence.Established s t)
    (hv : s.registers (.core .valid) = 1) (hc : s.registers (.core .count) = 50) :
    SramExecution.residentWords 50 t.rows t.dictionaryWords = fullWords := by
  funext k
  simp only [SramExecution.residentWords, known_dictionary s t h he hv,
    projected_source_row s t h he hv hc k, rows, fullWords,
    BitVec.extractLsb'_append_eq_left, BitVec.extractLsb'_append_eq_right]
  done

def CountWhenValid (s : SramState.State) : Prop :=
  s.registers (.core .valid) = 1 → s.registers (.core .count) = 50

theorem source_count_step (s : SramState.State) (i : Values Reactive.Input)
    (h : CountWhenValid s) (hi : SourceInput s i) : CountWhenValid (s.step i) := by
  intro hv
  change Sram.circuit.step (s.inputs i) s.registers (.core .valid) = 1 at hv
  change Sram.circuit.step (s.inputs i) s.registers (.core .count) = 50
  rw [SramCoverage.valid_step] at hv
  rw [SramCoverage.count_step]
  split <;> simp_all
  split <;> simp_all [CountWhenValid, SramState.State.inputs]
  · exact (hi.commit ‹_›).1
  · split at hv <;> simp_all
  done

theorem source_count_cold (s : SramState.State) (i : Values Reactive.Input)
    (hi : i .initialize = 1) : CountWhenValid (s.step i) := by
  intro hv
  change Sram.circuit.step (s.inputs i) s.registers (.core .valid) = 1 at hv
  rw [SramCoverage.valid_step] at hv
  simp [SramCoverage.cold_resetting (s.inputs i) s.registers hi] at hv

theorem source_count_run (s : SramState.State) (t : SramLoading.Ledger)
    (inputs : List (Values Reactive.Input)) (h : CountWhenValid s)
    (hi : SourceHistory s inputs) : CountWhenValid (SramLoading.run s t inputs).1 := by
  induction inputs generalizing s t with
  | nil => exact h
  | cons i rest ih => exact ih (s.step i) (t.step s i) (source_count_step s i h hi.1) hi.2

theorem initialized_source_count (s : SramState.State)
    (i : Values Reactive.Input) (hi : i .initialize = 1)
    (loading : List (Values Reactive.Input)) (hs : SourceHistory (s.step i) loading)
    (hv : (SramLoading.run (s.step i) SramLoading.Ledger.initial loading).1.registers (.core .valid) = 1) :
    (SramLoading.run (s.step i) SramLoading.Ledger.initial loading).1.registers (.core .count) = 50 :=
  source_count_run (s.step i) SramLoading.Ledger.initial loading (source_count_cold s i hi) hs hv

theorem reference_source (s : SramState.State) (t : SramLoading.Ledger)
    (h : Known t) (he : SramCorrespondence.Established s t)
    (hv : s.registers (.core .valid) = 1) (hc : s.registers (.core .count) = 50) :
    @SramExecution.reference s t.rows t.dictionaryWords =
      @SramExecution.withWords (SramExecution.core s.registers) fullWords := by
  unfold SramExecution.reference
  rw [hc, resident_source_words s t h he hv hc]

/-- Actual accepted canonical operands after initialization determine the
resident image; neither an image equality nor equal initial replicas/Q is a
premise. Loading order, repeated writes and rejected commands remain free. -/
theorem initialized_source_reference (s : SramState.State)
    (i : Values Reactive.Input) (hi : i .initialize = 1)
    (loading : List (Values Reactive.Input)) (hs : SourceHistory (s.step i) loading)
    (hv : (SramLoading.run (s.step i) SramLoading.Ledger.initial loading).1.registers (.core .valid) = 1) :
    let after := SramLoading.run (s.step i) SramLoading.Ledger.initial loading
    @SramExecution.reference after.1 after.2.rows after.2.dictionaryWords =
      @SramExecution.withWords (SramExecution.core after.1.registers) fullWords :=
  reference_source _ _ (known_run (s.step i) SramLoading.Ledger.initial loading known_initial hs)
    (SramCorrespondence.initialized_established s i hi loading) hv
    (initialized_source_count s i hi loading hs hv)

end Pinwheel.Hardware.Buffered.I2cLoading
