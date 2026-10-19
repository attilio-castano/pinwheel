import Pinwheel.Hardware.Buffered.GenericInstalledSram
import Pinwheel.Hardware.Buffered.GenericResetLoading
import Pinwheel.Hardware.Buffered.SpiGeometry

/-! A static shared-dictionary upload representation for any certified source.
The packing equation mentions no actual SRAM state, clock, history or execution.
Accepted operands then establish that representation in an initially unknown
digital SRAM; inactive payloads remain projected away by the real controller. -/
namespace Pinwheel.Hardware.Buffered.GenericUpload
open Pinwheel.Hardware Pinwheel.Program
set_option maxRecDepth 4096

structure Image (p : Program.Buffered.Program) (layout : GenericCertificate.Layout p) where
  word : BitVec 6 → BitVec 64
  control : BitVec 6 → BitVec 24
  branchIndex : BitVec 6 → BitVec 4
  dictionary : BitVec 4 → BitVec 56
  packed : SramExecution.residentWords (BitVec.ofNat 7 layout.count.val)
    (fun k => branchIndex k ++ (control k ++ word k)) dictionary = layout.words

variable {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}

def Image.rows (image : Image p layout) (k : BitVec 6) : BitVec 92 :=
  image.branchIndex k ++ (image.control k ++ image.word k)

theorem count_toNat (layout : GenericCertificate.Layout p) :
    (BitVec.ofNat 7 layout.count.val).toNat = layout.count.val := by
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt]
  have bound := layout.count.isLt
  omega

structure SourceInput (image : Image p layout) (s : SramState.State) (i : Values Reactive.Input) : Prop where
  row : SramLoading.rowAccepted s i = true → i .word = image.word (i .address) ∧
    i .control = image.control (i .address) ∧
    (i .branch).extractLsb' 0 4 = image.branchIndex (i .address)
  table : SramLoading.tableAccepted s i = true →
    i .branch = image.dictionary ((i .address).extractLsb' 0 4)
  commit : Sram.committing.eval (s.inputs i) s.registers = 1 →
    i .count = BitVec.ofNat 7 layout.count.val ∧ i .virtualSpan = BitVec.ofNat 11 p.code.span ∧
    i .idleLevels = p.idle.levels ∧ i .idleEnabled = p.idle.enabled

structure Known (image : Image p layout) (t : SramLoading.Ledger) : Prop where
  words : ∀ k v, t.words.contents k = some v → v = image.word k
  metadata : ∀ k, k.toNat < layout.count.val → ∀ v, t.metadata k = some v →
    v = image.branchIndex k ++ image.control k
  dictionary : ∀ k v, t.dictionary k = some v → v = image.dictionary k

def SourceHistory (image : Image p layout) : SramState.State → List (Values Reactive.Input) → Prop
  | _, [] => True
  | s, i :: rest => SourceInput image s i ∧ SourceHistory image (s.step i) rest

theorem known_initial (image : Image p layout) : Known image SramLoading.Ledger.initial := by
  constructor <;> simp [SramLoading.Ledger.initial,Memory.Sram.Model.initial]

theorem known_metadata_step (image : Image p layout) (s : SramState.State) (t : SramLoading.Ledger)
    (i : Values Reactive.Input) (h : Known image t) (hi : SourceInput image s i)
    (k : BitVec 6) (live : k.toNat < layout.count.val) (v : BitVec 28)
    (hv : (t.step s i).metadata k = some v) : v = image.branchIndex k ++ image.control k := by
  simp only [SramLoading.Ledger.step] at hv
  split at hv
  · rename_i cleared
    have accepted := Bool.and_eq_true_iff.mp cleared
    have outside := of_decide_eq_true accepted.2
    change (i .count).toNat ≤ k.toNat at outside
    rw [(hi.commit (of_decide_eq_true accepted.1)).1,count_toNat] at outside
    omega
  · split at hv
    · rename_i uploaded
      rw [← Option.some.inj hv,SramLoading.uploadedMetadata,
        (hi.row (Bool.and_eq_true_iff.mp uploaded).1).2.2,
        (hi.row (Bool.and_eq_true_iff.mp uploaded).1).2.1,
        of_decide_eq_true (Bool.and_eq_true_iff.mp uploaded).2]
    · exact h.metadata k live v hv

theorem known_words_step (image : Image p layout) (s : SramState.State) (t : SramLoading.Ledger)
    (i : Values Reactive.Input) (h : Known image t) (hi : SourceInput image s i)
    (k : BitVec 6) (v : BitVec 64) (hv : (t.step s i).words.contents k = some v) :
    v = image.word k := by
  rw [SramLoading.word_contents_step] at hv
  split at hv
  · rename_i accepted
    have source := hi.row (Bool.and_eq_true_iff.mp accepted).1
    simpa only [Option.some.injEq,beq_iff_eq] using
      (Option.some.inj hv).symm.trans (source.1.trans
        (congrArg image.word (of_decide_eq_true (Bool.and_eq_true_iff.mp accepted).2)))
  · exact h.words k v hv

theorem known_dictionary_step (image : Image p layout) (s : SramState.State) (t : SramLoading.Ledger)
    (i : Values Reactive.Input) (h : Known image t) (hi : SourceInput image s i)
    (k : BitVec 4) (v : BitVec 56) (hv : (t.step s i).dictionary k = some v) :
    v = image.dictionary k := by
  simp only [SramLoading.Ledger.step] at hv
  split at hv
  · rename_i accepted
    exact (Option.some.inj hv).symm.trans ((hi.table (Bool.and_eq_true_iff.mp accepted).1).trans
      (congrArg image.dictionary (of_decide_eq_true (Bool.and_eq_true_iff.mp accepted).2)))
  · exact h.dictionary k v hv

theorem known_step (image : Image p layout) (s : SramState.State) (t : SramLoading.Ledger)
    (i : Values Reactive.Input) (h : Known image t) (hi : SourceInput image s i) :
    Known image (t.step s i) :=
  ⟨known_words_step image s t i h hi,known_metadata_step image s t i h hi,
    known_dictionary_step image s t i h hi⟩

theorem known_run (image : Image p layout) (s : SramState.State) (t : SramLoading.Ledger)
    (inputs : List (Values Reactive.Input)) (h : Known image t) (history : SourceHistory image s inputs) :
    Known image (SramLoading.run s t inputs).2 := by
  induction inputs generalizing s t with
  | nil => exact h
  | cons i rest ih => exact ih (s.step i) (t.step s i) (known_step image s t i h history.1) history.2

private theorem dictionary_bit : ∀ k : BitVec 4, (65535 : BitVec 16).getLsbD k.toNat = true := by
  decide +kernel

theorem known_dictionary (image : Image p layout) (s : SramState.State) (t : SramLoading.Ledger)
    (h : Known image t) (established : SramCorrespondence.Established s t)
    (valid : s.registers (.core .valid) = 1) : t.dictionaryWords = image.dictionary := by
  funext k
  obtain ⟨v,known⟩ := established.covered.dictionary k
    (by simpa only [(established.admitted valid).2] using dictionary_bit k)
  simpa only [SramLoading.Ledger.dictionaryWords,known,Option.getD_some] using h.dictionary k v known

theorem known_live_row (image : Image p layout) (s : SramState.State) (t : SramLoading.Ledger)
    (h : Known image t) (established : SramCorrespondence.Established s t)
    (valid : s.registers (.core .valid) = 1) (count : s.core .count = BitVec.ofNat 7 layout.count.val)
    (k : BitVec 6) (live : SramExecution.live (s.registers (.core .count)) k = true) :
    t.rows k = image.rows k := by
  have within := of_decide_eq_true live
  change k.toNat < (s.core .count).toNat at within
  rw [count,count_toNat] at within
  obtain ⟨w,known⟩ := established.covered.rows k ((established.admitted valid).1 k (of_decide_eq_true live))
  obtain ⟨metadata,stored⟩ := established.coherent.metadata k ⟨w,known⟩
  simp only [SramLoading.Ledger.rows,SramLoading.Ledger.instructions,known,stored,
    Option.getD_some,h.words k w known,h.metadata k within metadata stored,Image.rows]
  exact BitVec.append_assoc

theorem projected_source_row (image : Image p layout) (s : SramState.State) (t : SramLoading.Ledger)
    (h : Known image t) (established : SramCorrespondence.Established s t)
    (valid : s.registers (.core .valid) = 1) (count : s.core .count = BitVec.ofNat 7 layout.count.val)
    (k : BitVec 6) :
    SramExecution.projectedRow (BitVec.ofNat 7 layout.count.val) t.rows k =
      SramExecution.projectedRow (BitVec.ofNat 7 layout.count.val) image.rows k := by
  change (if decide (k.toNat < (BitVec.ofNat 7 layout.count.val).toNat) = true then t.rows k else 0) =
    (if decide (k.toNat < (BitVec.ofNat 7 layout.count.val).toNat) = true then image.rows k else 0)
  rw [count_toNat]
  by_cases live : k.toNat < layout.count.val
  · have actual : SramExecution.live (s.registers (.core .count)) k = true := by
      change decide (k.toNat < (s.core .count).toNat) = true
      rw [count,count_toNat]
      exact decide_eq_true live
    simpa only [if_pos (decide_eq_true live)] using known_live_row image s t h established valid count k actual
  · simp only [live,decide_false,Bool.false_eq_true,if_false]

theorem resident_source_words (image : Image p layout) (s : SramState.State) (t : SramLoading.Ledger)
    (h : Known image t) (established : SramCorrespondence.Established s t)
    (valid : s.registers (.core .valid) = 1) (count : s.core .count = BitVec.ofNat 7 layout.count.val) :
    SramExecution.residentWords (BitVec.ofNat 7 layout.count.val) t.rows t.dictionaryWords = layout.words := by
  rw [← image.packed]
  funext k
  simp only [SramExecution.residentWords,known_dictionary image s t h established valid,
    projected_source_row image s t h established valid count k]
  rfl

end Pinwheel.Hardware.Buffered.GenericUpload
