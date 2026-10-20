import Pinwheel.Hardware.Buffered.I2cTimingCertificate
import Pinwheel.Hardware.Buffered.I2cLoading
import Pinwheel.Hardware.Buffered.I2cGeometry
import Pinwheel.Hardware.Buffered.GenericInstalledSram
import Pinwheel.Hardware.Buffered.SpiGeometry

/-! Actual accepted-upload provenance for every symbolic I²C timing pair.
Only accepted operands are constrained; initial SRAM contents remain arbitrary. -/
namespace Pinwheel.Hardware.Buffered.I2cTiming
open Pinwheel.Hardware Pinwheel.Program
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

def word (duration budget : Fin 256) (index : BitVec 6) : BitVec 64 :=
  if index.toNat < 50 then patchWord duration budget (I2cSource.word index) else 0

def rows (duration budget : Fin 256) (index : BitVec 6) : BitVec 92 :=
  I2cSource.branchIndex index ++ (I2cSource.control index ++ word duration budget index)

private theorem tail_fields (index : BitVec 6) (outside : 50 ≤ index.toNat) :
    I2cSource.branchIndex index = 0 ∧ I2cSource.control index = 0 := by
  have metadata := I2cLoading.metadata_tail index outside
  have indexZero : I2cSource.branchIndex index = (0 : BitVec 28).extractLsb' 24 4 := by
    simpa only [BitVec.extractLsb'_append_eq_left] using
      congrArg (fun x : BitVec 28 => x.extractLsb' 24 4) metadata
  have controlZero : I2cSource.control index = (0 : BitVec 28).extractLsb' 0 24 := by
    simpa only [BitVec.extractLsb'_append_eq_right] using
      congrArg (fun x : BitVec 28 => x.extractLsb' 0 24) metadata
  exact ⟨indexZero.trans (by decide), controlZero.trans (by decide)⟩

theorem row_tail (duration budget : Fin 256) (index : BitVec 6) (outside : 50 ≤ index.toNat) :
    rows duration budget index = 0 := by
  have fields := tail_fields index outside
  simp [rows, word, show ¬ index.toNat < 50 by omega, fields.1, fields.2]

theorem full_words (duration budget : Fin 256) (index : BitVec 6) :
    fullWords duration budget index = I2cSource.dictionary (I2cSource.branchIndex index) ++
      (I2cSource.control index ++ word duration budget index) := by
  by_cases live : index.toNat < 50
  case pos =>
    simp (disch := decide) only [fullWords, word, live, ↓reduceIte, patchRecord, I2cSource.fullWords,
      BitVec.extractLsb'_append_eq_of_add_le, BitVec.extractLsb'_append_eq_of_le,
      BitVec.extractLsb'_eq_self, Nat.reduceSub]
    change ((I2cSource.dictionary (I2cSource.branchIndex index)).extractLsb' 0 56 ++
      I2cSource.control index) ++ patchWord duration budget (I2cSource.word index) = _
    rw [BitVec.extractLsb'_eq_self, BitVec.append_assoc]
    rfl
  case neg =>
    have fields := tail_fields index (by omega)
    simp only [fullWords, word, live, ↓reduceIte, fields.1, fields.2]
    rfl

namespace Loading

structure SourceInput (duration budget : Fin 256) (s : SramState.State)
    (i : Values Reactive.Input) : Prop where
  row : SramLoading.rowAccepted s i = true → i .word = word duration budget (i .address) ∧
    i .control = I2cSource.control (i .address) ∧
    (i .branch).extractLsb' 0 4 = I2cSource.branchIndex (i .address)
  table : SramLoading.tableAccepted s i = true →
    i .branch = I2cSource.dictionary ((i .address).extractLsb' 0 4)
  commit : Sram.committing.eval (s.inputs i) s.registers = 1 →
    i .count = 50 ∧ i .virtualSpan = 270 ∧ i .idleLevels = 0 ∧ i .idleEnabled = 0

structure Known (duration budget : Fin 256) (t : SramLoading.Ledger) : Prop where
  words : ∀ k v, t.words.contents k = some v → v = word duration budget k
  metadata : ∀ k v, t.metadata k = some v → v = I2cSource.branchIndex k ++ I2cSource.control k
  dictionary : ∀ k v, t.dictionary k = some v → v = I2cSource.dictionary k

def SourceHistory (duration budget : Fin 256) : SramState.State → List (Values Reactive.Input) → Prop
  | _, [] => True
  | s, i :: rest => SourceInput duration budget s i ∧ SourceHistory duration budget (s.step i) rest

theorem known_initial (duration budget : Fin 256) : Known duration budget SramLoading.Ledger.initial := by
  constructor <;> simp [SramLoading.Ledger.initial, Memory.Sram.Model.initial]

theorem known_words_step (duration budget : Fin 256) (s : SramState.State) (t : SramLoading.Ledger)
    (i : Values Reactive.Input) (h : Known duration budget t) (hi : SourceInput duration budget s i)
    (k : BitVec 6) (v : BitVec 64) (hv : (t.step s i).words.contents k = some v) :
    v = word duration budget k := by
  rw [SramLoading.word_contents_step] at hv
  split at hv
  · rename_i accepted
    have source := hi.row (Bool.and_eq_true_iff.mp accepted).1
    simpa only [Option.some.injEq, beq_iff_eq] using
      (Option.some.inj hv).symm.trans
        (source.1.trans (congrArg (word duration budget)
          (of_decide_eq_true (Bool.and_eq_true_iff.mp accepted).2)))
  · exact h.words k v hv

theorem known_metadata_step (duration budget : Fin 256) (s : SramState.State) (t : SramLoading.Ledger)
    (i : Values Reactive.Input) (h : Known duration budget t) (hi : SourceInput duration budget s i)
    (k : BitVec 6) (v : BitVec 28) (hv : (t.step s i).metadata k = some v) :
    v = I2cSource.branchIndex k ++ I2cSource.control k := by
  simp only [SramLoading.Ledger.step] at hv
  split at hv
  · rename_i committed
    have accepted := Bool.and_eq_true_iff.mp committed
    have outside : 50 ≤ k.toNat := by
      have bound := of_decide_eq_true accepted.2
      change (i .count).toNat ≤ k.toNat at bound
      rw [(hi.commit (of_decide_eq_true accepted.1)).1] at bound
      exact bound
    exact (Option.some.inj hv).symm.trans (I2cLoading.metadata_tail k outside).symm
  · split at hv
    · rename_i uploaded
      rw [← Option.some.inj hv, SramLoading.uploadedMetadata,
        (hi.row (Bool.and_eq_true_iff.mp uploaded).1).2.2,
        (hi.row (Bool.and_eq_true_iff.mp uploaded).1).2.1,
        of_decide_eq_true (Bool.and_eq_true_iff.mp uploaded).2]
    · exact h.metadata k v hv

theorem known_dictionary_step (duration budget : Fin 256) (s : SramState.State) (t : SramLoading.Ledger)
    (i : Values Reactive.Input) (h : Known duration budget t) (hi : SourceInput duration budget s i)
    (k : BitVec 4) (v : BitVec 56) (hv : (t.step s i).dictionary k = some v) :
    v = I2cSource.dictionary k := by
  simp only [SramLoading.Ledger.step] at hv
  split at hv
  · rename_i uploaded
    exact (Option.some.inj hv).symm.trans
      ((hi.table (Bool.and_eq_true_iff.mp uploaded).1).trans
        (congrArg I2cSource.dictionary (of_decide_eq_true (Bool.and_eq_true_iff.mp uploaded).2)))
  · exact h.dictionary k v hv

theorem known_step (duration budget : Fin 256) (s : SramState.State) (t : SramLoading.Ledger)
    (i : Values Reactive.Input) (h : Known duration budget t) (hi : SourceInput duration budget s i) :
    Known duration budget (t.step s i) :=
  ⟨known_words_step duration budget s t i h hi, known_metadata_step duration budget s t i h hi,
    known_dictionary_step duration budget s t i h hi⟩

theorem known_run (duration budget : Fin 256) (s : SramState.State) (t : SramLoading.Ledger)
    (loading : List (Values Reactive.Input)) (h : Known duration budget t)
    (source : SourceHistory duration budget s loading) :
    Known duration budget (SramLoading.run s t loading).2 := by
  induction loading generalizing s t
  case nil => exact h
  case cons i rest ih =>
    exact ih (s.step i) (t.step s i) (known_step duration budget s t i h source.1) source.2

private theorem dictionary_bit : ∀ k : BitVec 4, (65535 : BitVec 16).getLsbD k.toNat = true := by
  decide +kernel

theorem known_dictionary (duration budget : Fin 256) (s : SramState.State) (t : SramLoading.Ledger)
    (h : Known duration budget t) (established : SramCorrespondence.Established s t)
    (valid : s.registers (.core .valid) = 1) : t.dictionaryWords = I2cSource.dictionary := by
  funext k
  obtain ⟨value, known⟩ := established.covered.dictionary k
    (by simpa only [(established.admitted valid).2] using dictionary_bit k)
  simpa only [SramLoading.Ledger.dictionaryWords, known, Option.getD_some] using h.dictionary k value known

theorem known_live_row (duration budget : Fin 256) (s : SramState.State) (t : SramLoading.Ledger)
    (h : Known duration budget t) (established : SramCorrespondence.Established s t)
    (valid : s.registers (.core .valid) = 1) (k : BitVec 6)
    (live : SramExecution.live (s.registers (.core .count)) k = true) :
    t.rows k = rows duration budget k := by
  obtain ⟨value, known⟩ := established.covered.rows k
    ((established.admitted valid).1 k (of_decide_eq_true live))
  obtain ⟨metadata, stored⟩ := established.coherent.metadata k ⟨value, known⟩
  simp only [SramLoading.Ledger.rows, SramLoading.Ledger.instructions, known, stored,
    Option.getD_some, h.words k value known, h.metadata k metadata stored, rows]
  exact BitVec.append_assoc

theorem projected_source_row (duration budget : Fin 256) (s : SramState.State) (t : SramLoading.Ledger)
    (h : Known duration budget t) (established : SramCorrespondence.Established s t)
    (valid : s.registers (.core .valid) = 1) (count : s.registers (.core .count) = 50) (k : BitVec 6) :
    SramExecution.projectedRow 50 t.rows k = rows duration budget k := by
  change (if decide (k.toNat < 50) = true then t.rows k else 0) = rows duration budget k
  by_cases live : k.toNat < 50
  case pos =>
    have inRange : SramExecution.live (s.registers (.core .count)) k = true := by
      rw [count]
      exact decide_eq_true live
    simpa only [if_pos (decide_eq_true live)] using
      known_live_row duration budget s t h established valid k inRange
  case neg =>
    simp only [live, decide_false, Bool.false_eq_true, if_false]
    exact (row_tail duration budget k (by omega)).symm

theorem resident_source_words (duration budget : Fin 256) (s : SramState.State) (t : SramLoading.Ledger)
    (h : Known duration budget t) (established : SramCorrespondence.Established s t)
    (valid : s.registers (.core .valid) = 1) (count : s.registers (.core .count) = 50) :
    SramExecution.residentWords 50 t.rows t.dictionaryWords = fullWords duration budget := by
  funext k
  simp only [SramExecution.residentWords, known_dictionary duration budget s t h established valid,
    projected_source_row duration budget s t h established valid count k, rows, full_words,
    BitVec.extractLsb'_append_eq_left, BitVec.extractLsb'_append_eq_right]

private theorem valid_post (i : Values Sram.Input) (s : Values Sram.Register)
    (valid : Sram.circuit.step i s (.core .valid) = 1) :
    SramCoverage.resetting.eval i s ≠ 1 ∧ i (.base .initialize) ≠ 1 ∧
      (Sram.committing.eval i s = 1 ∨ s (.core .valid) = 1) := by
  rw [SramCoverage.valid_step] at valid
  split at valid
  · contradiction
  · rename_i notReset
    have reset : SramCoverage.resetting.eval i s ≠ 1 := fun h => notReset (Or.inl h)
    refine ⟨reset, fun cold => reset (SramCoverage.cold_resetting i s cold), ?_⟩
    split at valid
    · exact Or.inl ‹Sram.committing.eval i s = 1›
    · exact Or.inr valid

def WhenValid (s : SramState.State) : Prop :=
  s.registers (.core .valid) = 1 → I2cGeometry.Geometry (SramExecution.core s.registers)

theorem geometry_step (duration budget : Fin 256) (s : SramState.State)
    (i : Values Reactive.Input) (h : WhenValid s) (source : SourceInput duration budget s i) :
    WhenValid (s.step i) := by
  intro valid
  have facts := valid_post (s.inputs i) s.registers valid
  by_cases committing : Sram.committing.eval (s.inputs i) s.registers = 1
  case pos =>
    have geometry := source.commit committing
    constructor
    all_goals simp only [SramExecution.core, SramState.State.step, SramCoverage.count_step,
      SpiGeometry.virtualSpan_step, SpiGeometry.idleLevels_step, SpiGeometry.idleEnabled_step,
      if_neg facts.1, if_pos committing, SramState.State.inputs]
    all_goals simp only [geometry.1, geometry.2.1, geometry.2.2.1, geometry.2.2.2, ite_self]
  case neg =>
    have old := h (facts.2.2.resolve_left committing)
    have cold : i .initialize ≠ 1 := facts.2.1
    constructor
    all_goals simp only [SramExecution.core, SramState.State.step, SramCoverage.count_step,
      SpiGeometry.virtualSpan_step, SpiGeometry.idleLevels_step, SpiGeometry.idleEnabled_step,
      if_neg facts.1, if_neg committing, SramState.State.inputs, if_neg cold]
    · exact old.count
    · exact old.virtualSpan
    · exact old.idleLevels
    · exact old.idleEnabled

theorem geometry_cold (s : SramState.State) (cold : Values Reactive.Input)
    (coldInit : cold .initialize = 1) : WhenValid (s.step cold) := by
  intro valid
  exact False.elim ((valid_post (s.inputs cold) s.registers valid).2.1 coldInit)

theorem geometry_run (duration budget : Fin 256) (s : SramState.State) (t : SramLoading.Ledger)
    (loading : List (Values Reactive.Input)) (h : WhenValid s)
    (history : SourceHistory duration budget s loading) :
    WhenValid (SramLoading.run s t loading).1 := by
  induction loading generalizing s t
  case nil => exact h
  case cons i rest ih =>
    exact ih (s.step i) (t.step s i) (geometry_step duration budget s i h history.1) history.2

theorem initialized_installed (duration budget : Fin 256) (s : SramState.State)
    (cold : Values Reactive.Input) (coldInit : cold .initialize = 1)
    (loading : List (Values Reactive.Input))
    (history : SourceHistory duration budget (s.step cold) loading)
    (valid : (SramLoading.run (s.step cold) SramLoading.Ledger.initial loading).1.registers (.core .valid) = 1) :
    Refinement.InstalledSram (source duration budget) (layout duration budget)
      (SramLoading.run (s.step cold) SramLoading.Ledger.initial loading).1 := by
  let after := SramLoading.run (s.step cold) SramLoading.Ledger.initial loading
  have geometry := geometry_run duration budget (s.step cold) SramLoading.Ledger.initial loading
    (geometry_cold s cold coldInit) history valid
  have known := known_run duration budget (s.step cold) SramLoading.Ledger.initial loading
    (known_initial duration budget) history
  have established := SramCorrespondence.initialized_established s cold coldInit loading
  have initialized := SramCorrespondence.initialized_resident s cold coldInit loading valid
  have count : after.1.registers (.core .count) = 50 := geometry.count
  have image : @SramExecution.reference after.1 after.2.rows after.2.dictionaryWords =
      @SramExecution.withWords after.1.core (fullWords duration budget) := by
    unfold SramExecution.reference
    rw [count, resident_source_words duration budget after.1 after.2 known established valid count]
    rfl
  refine ⟨after.2.rows, after.2.dictionaryWords, initialized.2.1, initialized.2.2, ?_, valid⟩
  rw [image]
  exact ⟨geometry.count, geometry.virtualSpan, geometry.idleLevels, geometry.idleEnabled, fun _ => rfl⟩

end Loading

end Pinwheel.Hardware.Buffered.I2cTiming
