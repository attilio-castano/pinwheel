import Pinwheel.Program.BufferedSPI
import Pinwheel.Hardware.Buffered.SramCorrespondence

/-! A bounded source-to-resident bridge for canonical compact mode-0 SPI.
The typed source has four stored leaves. Their linear instruction encoding and
two counted-loop descriptors reconstruct the resident full-register words.
Initialized SRAM execution can then use that exact image. This file does not
prove a universal Buffered.run/compiler simulation or serial/RTL refinement. -/
namespace Pinwheel.Hardware.Buffered.SpiSource
open Pinwheel.Hardware Pinwheel.Program
open Engine.Reactive

abbrev Config := BufferedSPI.Config

def appendBits : Option (Fin 2) → BitVec 2
  | none => 0
  | some input => BitVec.ofNat 2 (input.val + 1)

/-- The supported SPI subset has no scratch capture, guard or branch fields.
Unsupported source operations return none rather than silently inventing an
encoding. The compact SPI source is proved to stay within this subset. -/
def encodeLinear (instruction : Program.Buffered.Instruction) : Option (BitVec 64) := do
  let (kind, action, preserve, output) ← match instruction.operation with
    | .drive action => some (0#3, action, 0#3, 0#2)
    | .shift output false false action =>
      some (1#3, action, 0#3, BitVec.ofNat 2 output.val)
    | .keep preserve 0 action => some (2#3, action, preserve, 0#2)
    | .halt => return 3
    | _ => none
  if action.capture.isSome || instruction.preserveLevels != 0 ||
      instruction.preserveEnabled != 0 then none
  else some ((0#40) ++ appendBits instruction.append ++ output ++ preserve ++
    BitVec.ofNat 8 action.durationMinusOne.val ++ action.pins.enabled ++ action.pins.levels ++ kind)

def leafAt (duration : Fin 256) (k : Fin 4) : Program.Buffered.Instruction :=
  match k.val with
  | 0 => BufferedSPI.low duration
  | 1 => BufferedSPI.high duration
  | 2 => BufferedSPI.release duration
  | _ => BufferedSPI.halt

def leaf (c : Config) (k : Fin 4) : Program.Buffered.Instruction :=
  leafAt c.halfCyclesMinusOne k

/-- An independent field decoder for the linear SPI subset. Reserved/inactive
fields and unsupported encodings are rejected, not normalized away. -/
def decodeLinear (word : BitVec 64) : Option Program.Buffered.Instruction := do
  if word == 3 then return {operation := .halt}
  if (word.extractLsb' 24 40) != 0 then none else do
    let append ← match (word.extractLsb' 22 2).toNat with
      | 0 => some none | 1 => some (some (0 : Fin 2))
      | 2 => some (some (1 : Fin 2)) | _ => none
    let action : Action 15 :=
      ⟨⟨word.extractLsb' 3 3, word.extractLsb' 6 3⟩,
        (word.extractLsb' 9 8).toFin, none⟩
    let preserve := word.extractLsb' 17 3
    let output := word.extractLsb' 20 2
    let operation : Program.Buffered.Operation ← match (word.extractLsb' 0 3).toNat with
      | 0 => if preserve == 0 && output == 0 then some (.drive action) else none
      | 1 => (if h : output.toNat < 3 then
          (if preserve == 0 then some (.shift ⟨output.toNat, h⟩ false false action) else none)
          else none)
      | 2 => if output == 0 then some (.keep preserve 0 action) else none
      | _ => none
    return {operation, append}

theorem linear_round_trip : ∀ d : Fin 256, ∀ k : Fin 4,
    decodeLinear ((encodeLinear (leafAt d k)).getD 0) = some (leafAt d k) := by
  decide +kernel

theorem leaf_encodable (c : Config) (k : Fin 4) : (encodeLinear (leaf c k)).isSome = true := by
  match k with
  | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ => rfl

def word (c : Config) (k : BitVec 6) : BitVec 64 :=
  if h : k.toNat < 4 then (encodeLinear (leaf c ⟨k.toNat, h⟩)).getD 0 else 0

theorem source_leaf_decode (c : Config) (k : Fin 4) :
    decodeLinear (word c (BitVec.ofNat 6 k.val)) = some (leaf c k) := by
  have hk : k.val < 2^6 := Nat.lt_trans k.isLt (by decide)
  simp only [word, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk, dif_pos k.isLt, leaf]
  exact linear_round_trip c.halfCyclesMinusOne k

def control (c : Config) (k : BitVec 6) : BitVec 24 :=
  if k == 0 then BitVec.ofNat 24 (2 + c.bytesMinusOne.val * 2^8 + 7 * 2^17)
  else if k == 1 then BitVec.ofNat 24
    (2 + c.bytesMinusOne.val * 2^8 + 7 * 2^17 + 2^20 + 2^21)
  else 0

/-- The binary descriptors encode the source's two nested loops, both starting
at row zero; the KEEP row closes both loops. The final drive/HALT are outside
the loops. Bounds store count-minus-one, exactly as the hardware decodes them. -/
theorem loop_descriptor (c : Config) :
    (control c 0).extractLsb' 0 2 = 2 ∧
    (control c 0).extractLsb' 2 6 = 0 ∧
    (control c 0).extractLsb' 8 3 = BitVec.ofNat 3 c.bytesMinusOne.val ∧
    (control c 0).extractLsb' 11 6 = 0 ∧
    (control c 0).extractLsb' 17 3 = 7 ∧
    (control c 0).extractLsb' 20 2 = 0 ∧
    (control c 1).extractLsb' 20 2 = 3 ∧
    (control c 1).extractLsb' 22 2 = 0 ∧ control c 2 = 0 ∧ control c 3 = 0 := by
  match c with
  | ⟨⟨0, _⟩, _, _⟩ | ⟨⟨1, _⟩, _, _⟩ | ⟨⟨2, _⟩, _, _⟩ | ⟨⟨3, _⟩, _, _⟩ =>
    dsimp only [control]
    decide +kernel
    done

def rows (c : Config) : Memory.Contents 6 92 :=
  fun k => (0#4) ++ (control c k ++ word c k)

def dictionary : Memory.Contents 4 56 := fun _ => 0

def fullWords (c : Config) : Memory.Contents 6 144 :=
  fun k => (0#56) ++ (control c k ++ word c k)

theorem resident_words (c : Config) :
    SramExecution.residentWords 4 (rows c) dictionary = fullWords c := by
  funext k
  simp only [SramExecution.residentWords, SramExecution.projectedRow,
    dictionary, SramCandidates.project, SramExecution.live,
    rows, fullWords]
  change 0#56 ++ ((if decide (k.toNat < 4) = true then
    0#4 ++ (control c k ++ word c k) else 0#92).extractLsb' 0 88) = _
  by_cases hk : k.toNat < 4
  · simp only [hk, decide_true, if_true]
    exact congrArg (fun v : BitVec 88 => 0#56 ++ v)
      (BitVec.extractLsb'_append_eq_right (a := 0#4) (b := control c k ++ word c k))
  · have h0 : k ≠ 0 := by intro h; subst k; contradiction
    have h1 : k ≠ 1 := by intro h; subst k; contradiction
    simp only [hk, decide_false, Bool.false_eq_true, if_false, control, word, beq_iff_eq]
    rw [if_neg h0, if_neg h1]
    simp
    done
  done

private theorem band_one : ∀ x y : BitVec 1, x &&& y = 1 ↔ x = 1 ∧ y = 1 := by
  decide +kernel

private theorem ofBool_one : ∀ b : Bool, BitVec.ofBool b = 1 ↔ b = true := by
  decide +kernel

theorem row_command (s : SramState.State) (i : Values Reactive.Input)
    (h : SramLoading.rowAccepted s i = true) : i .command = 1 := by
  have hw := of_decide_eq_true h
  simp only [Sram.rowWriting, SramExecution.control_correct, SharedBranches.rowWriting,
    SharedBranches.both, SharedBranches.cmd, Expr.eval, SramState.State.inputs,
    band_one, ofBool_one] at hw
  exact of_decide_eq_true hw.2
  done

theorem table_command (s : SramState.State) (i : Values Reactive.Input)
    (h : SramLoading.tableAccepted s i = true) : i .command = 6 := by
  have hw := of_decide_eq_true h
  simp only [Sram.tableWriting, SramExecution.control_correct, SharedBranches.tableWriting,
    SharedBranches.both, SharedBranches.cmd, Expr.eval, SramState.State.inputs,
    band_one, ofBool_one] at hw
  exact of_decide_eq_true hw.2

/-- Only actual loader operands are constrained. Acceptance remains the
controller's decision; order, repeated writes and rejected commands are free. -/
structure SourceInput (c : Config) (s : SramState.State) (i : Values Reactive.Input) : Prop where
  row : SramLoading.rowAccepted s i = true → i .word = word c (i .address) ∧
    i .control = control c (i .address) ∧ i .branch = 0
  table : SramLoading.tableAccepted s i = true → i .branch = 0
  commit : Sram.committing.eval (s.inputs i) s.registers = 1 →
    i .count = 4 ∧
    i .virtualSpan = BitVec.ofNat 11 (16 * (c.bytesMinusOne.val + 1) + 2) ∧
    i .idleLevels = 4 ∧ i .idleEnabled = 7

structure Known (c : Config) (t : SramLoading.Ledger) : Prop where
  words : ∀ k v, t.words.contents k = some v → v = word c k
  metadata : ∀ k v, t.metadata k = some v → v = (0#4 ++ control c k)
  dictionary : ∀ k v, t.dictionary k = some v → v = 0

theorem known_initial (c : Config) : Known c SramLoading.Ledger.initial := by
  constructor <;> simp [SramLoading.Ledger.initial, Memory.Sram.Model.initial]

theorem control_tail (c : Config) (k : BitVec 6) (hk : 4 ≤ k.toNat) : control c k = 0 := by
  have h0 : k ≠ 0 := by intro h; subst k; contradiction
  have h1 : k ≠ 1 := by intro h; subst k; contradiction
  simp only [control, beq_iff_eq]
  rw [if_neg h0, if_neg h1]

theorem known_words_step (c : Config) (s : SramState.State) (t : SramLoading.Ledger)
    (i : Values Reactive.Input) (h : Known c t) (hi : SourceInput c s i)
    (k : BitVec 6) (v : BitVec 64) (hv : (t.step s i).words.contents k = some v) :
    v = word c k := by
  rw [SramLoading.word_contents_step] at hv
  split at hv
  · rename_i hw
    rcases Bool.and_eq_true_iff.mp hw with ⟨hr, ha⟩
    have hs := hi.row hr
    simpa only [Option.some.injEq, beq_iff_eq] using
      (Option.some.inj hv).symm.trans (hs.1.trans (congrArg (word c) (of_decide_eq_true ha)))
    done
  · exact h.words k v hv
  done

theorem known_metadata_step (c : Config) (s : SramState.State) (t : SramLoading.Ledger)
    (i : Values Reactive.Input) (h : Known c t) (hi : SourceInput c s i)
    (k : BitVec 6) (v : BitVec 28) (hv : (t.step s i).metadata k = some v) :
    v = (0#4 ++ control c k) := by
  simp only [SramLoading.Ledger.step] at hv
  split at hv
  · rename_i ht
    have hp := Bool.and_eq_true_iff.mp ht
    have hcount := (hi.commit (of_decide_eq_true hp.1)).1
    have hge : 4 ≤ k.toNat := by
      have hh := of_decide_eq_true hp.2
      change (i .count).toNat ≤ k.toNat at hh
      rw [hcount] at hh
      exact hh
    rw [(Option.some.inj hv).symm, control_tail c k hge]
    rfl
    done
  · split at hv
    · rename_i hw
      rcases Bool.and_eq_true_iff.mp hw with ⟨hr, ha⟩
      have hs := hi.row hr
      have ha' : i .address = k := of_decide_eq_true ha
      rw [← Option.some.inj hv, SramLoading.uploadedMetadata, hs.2.2, hs.2.1, ha']
      rfl
    · exact h.metadata k v hv
  done

theorem known_dictionary_step (c : Config) (s : SramState.State) (t : SramLoading.Ledger)
    (i : Values Reactive.Input) (h : Known c t) (hi : SourceInput c s i)
    (k : BitVec 4) (v : BitVec 56) (hv : (t.step s i).dictionary k = some v) : v = 0 := by
  simp only [SramLoading.Ledger.step] at hv
  split at hv
  · rename_i hw
    exact (Option.some.inj hv).symm.trans (hi.table (Bool.and_eq_true_iff.mp hw).1)
  · exact h.dictionary k v hv

theorem known_step (c : Config) (s : SramState.State) (t : SramLoading.Ledger)
    (i : Values Reactive.Input) (h : Known c t) (hi : SourceInput c s i) :
    Known c (t.step s i) :=
  ⟨known_words_step c s t i h hi, known_metadata_step c s t i h hi,
    known_dictionary_step c s t i h hi⟩

/-- Source operands are required only for commands actually accepted along
this hardware history. Noncanonical rejected writes need no source premise. -/
def SourceHistory (c : Config) : SramState.State → List (Values Reactive.Input) → Prop
  | _, [] => True
  | s, i :: rest => SourceInput c s i ∧ SourceHistory c (s.step i) rest

theorem known_run (c : Config) (s : SramState.State) (t : SramLoading.Ledger)
    (inputs : List (Values Reactive.Input)) (h : Known c t) (hi : SourceHistory c s inputs) :
    Known c (SramLoading.run s t inputs).2 := by
  induction inputs generalizing s t with
  | nil => exact h
  | cons i rest ih => exact ih (s.step i) (t.step s i) (known_step c s t i h hi.1) hi.2

def CountWhenValid (s : SramState.State) : Prop :=
  s.registers (.core .valid) = 1 → s.registers (.core .count) = 4

theorem source_count_step (c : Config) (s : SramState.State) (i : Values Reactive.Input)
    (h : CountWhenValid s) (hi : SourceInput c s i) : CountWhenValid (s.step i) := by
  intro hv
  change Sram.circuit.step (s.inputs i) s.registers (.core .valid) = 1 at hv
  change Sram.circuit.step (s.inputs i) s.registers (.core .count) = 4
  rw [SramCoverage.valid_step] at hv
  rw [SramCoverage.count_step]
  split <;> simp_all
  split <;> simp_all [CountWhenValid, SramState.State.inputs]
  · rename_i hc
    exact (hi.commit hc).1
  · split at hv <;> simp_all
  done

theorem source_count_cold (s : SramState.State) (i : Values Reactive.Input)
    (hi : i .initialize = 1) : CountWhenValid (s.step i) := by
  intro hv
  change Sram.circuit.step (s.inputs i) s.registers (.core .valid) = 1 at hv
  rw [SramCoverage.valid_step] at hv
  simp [SramCoverage.cold_resetting (s.inputs i) s.registers hi] at hv

theorem source_count_run (c : Config) (s : SramState.State) (t : SramLoading.Ledger)
    (inputs : List (Values Reactive.Input)) (h : CountWhenValid s)
    (hi : SourceHistory c s inputs) : CountWhenValid (SramLoading.run s t inputs).1 := by
  induction inputs generalizing s t with
  | nil => exact h
  | cons i rest ih => exact ih (s.step i) (t.step s i) (source_count_step c s i h hi.1) hi.2

theorem initialized_source_count (c : Config) (s : SramState.State)
    (i : Values Reactive.Input) (hi : i .initialize = 1)
    (loading : List (Values Reactive.Input)) (hs : SourceHistory c (s.step i) loading)
    (hv : (SramLoading.run (s.step i) SramLoading.Ledger.initial loading).1.registers (.core .valid) = 1) :
    (SramLoading.run (s.step i) SramLoading.Ledger.initial loading).1.registers (.core .count) = 4 :=
  source_count_run c (s.step i) SramLoading.Ledger.initial loading (source_count_cold s i hi) hs hv

theorem known_dictionary (c : Config) (t : SramLoading.Ledger) (h : Known c t) :
    t.dictionaryWords = dictionary := by
  funext k
  change (t.dictionary k).getD 0 = 0
  cases hv : t.dictionary k with
  | none => rfl
  | some v => exact h.dictionary k v hv

theorem known_live_row (c : Config) (s : SramState.State) (t : SramLoading.Ledger)
    (h : Known c t) (he : SramCorrespondence.Established s t)
    (hv : s.registers (.core .valid) = 1) (k : BitVec 6)
    (hk : SramExecution.live (s.registers (.core .count)) k = true) :
    t.rows k = rows c k := by
  have hw := he.covered.rows k ((he.admitted hv).1 k (by exact of_decide_eq_true hk))
  rcases hw with ⟨w, hw⟩
  rcases he.coherent.metadata k ⟨w, hw⟩ with ⟨m, hm⟩
  simp only [SramLoading.Ledger.rows, SramLoading.Ledger.instructions, hw, hm,
    Option.getD_some, h.words k w hw, h.metadata k m hm, rows]
  exact BitVec.append_assoc (x₁ := 0#4) (x₂ := control c k) (x₃ := word c k)
  done

theorem row_tail (c : Config) (k : BitVec 6) (hk : 4 ≤ k.toNat) : rows c k = 0 := by
  simp only [rows, control_tail c k hk, word, dif_neg (Nat.not_lt.mpr hk)]
  rfl

theorem projected_source_row (c : Config) (s : SramState.State) (t : SramLoading.Ledger)
    (h : Known c t) (he : SramCorrespondence.Established s t)
    (hv : s.registers (.core .valid) = 1) (hc : s.registers (.core .count) = 4)
    (k : BitVec 6) : SramExecution.projectedRow 4 t.rows k = rows c k := by
  change (if decide (k.toNat < 4) = true then t.rows k else 0) = rows c k
  by_cases hk : k.toNat < 4
  · have hl : SramExecution.live (s.registers (.core .count)) k = true := by
      rw [hc]
      exact decide_eq_true hk
    rw [if_pos (decide_eq_true hk)]
    exact known_live_row c s t h he hv k hl
  · simp only [hk, decide_false, Bool.false_eq_true, if_false]
    exact (row_tail c k (Nat.le_of_not_gt hk)).symm
    done

theorem resident_source_words (c : Config) (s : SramState.State) (t : SramLoading.Ledger)
    (h : Known c t) (he : SramCorrespondence.Established s t)
    (hv : s.registers (.core .valid) = 1) (hc : s.registers (.core .count) = 4) :
    SramExecution.residentWords 4 t.rows t.dictionaryWords = fullWords c := by
  funext k
  simp only [SramExecution.residentWords, known_dictionary c t h,
    projected_source_row c s t h he hv hc k, dictionary, rows, fullWords]
  exact congrArg (fun v : BitVec 88 => 0#56 ++ v)
    (BitVec.extractLsb'_append_eq_right (a := 0#4) (b := control c k ++ word c k))

theorem reference_source (c : Config) (s : SramState.State) (t : SramLoading.Ledger)
    (h : Known c t) (he : SramCorrespondence.Established s t)
    (hv : s.registers (.core .valid) = 1) (hc : s.registers (.core .count) = 4) :
    @SramExecution.reference s t.rows t.dictionaryWords =
      @SramExecution.withWords (SramExecution.core s.registers) (fullWords c) := by
  unfold SramExecution.reference
  rw [hc, resident_source_words c s t h he hv hc]

/-- Initialized accepted source operands establish exactly the canonical SPI
resident words and four-row count. Image equality is derived from actual
accepted writes. Arbitrary startup arrays/Q and rejected noncanonical commands
are allowed. -/
theorem initialized_source_reference (c : Config) (s : SramState.State)
    (i : Values Reactive.Input) (hi : i .initialize = 1)
    (loading : List (Values Reactive.Input))
    (hs : SourceHistory c (s.step i) loading)
    (hv : (SramLoading.run (s.step i) SramLoading.Ledger.initial loading).1.registers (.core .valid) = 1) :
    let after := SramLoading.run (s.step i) SramLoading.Ledger.initial loading
    @SramExecution.reference after.1 after.2.rows after.2.dictionaryWords =
      @SramExecution.withWords (SramExecution.core after.1.registers) (fullWords c) :=
  reference_source c _ _ (known_run c (s.step i) SramLoading.Ledger.initial loading
    (known_initial c) hs) (SramCorrespondence.initialized_established s i hi loading) hv
      (initialized_source_count c s i hi loading hs hv)

/-- Every public output after every permitted runtime prefix agrees with the
independent full-register circuit loaded with the source-constructed SPI words.
Its nonword initial state is the actual valid cut. Source-level execution,
serial transport and emitted RTL remain separate refinement obligations. -/
theorem initialized_spi_observe (c : Config) (s : SramState.State)
    (i : Values Reactive.Input) (hi : i .initialize = 1)
    (loading runtime : List (Values Reactive.Input))
    (hs : SourceHistory c (s.step i) loading)
    (hv : (SramLoading.run (s.step i) SramLoading.Ledger.initial loading).1.registers (.core .valid) = 1)
    (hr : ∀ j ∈ runtime, SramExecution.ExecutingInput j)
    (query : Values Reactive.Input) (hq : SharedBranches.Runtime query) (o : Reactive.Output w) :
    let after := SramLoading.run (s.step i) SramLoading.Ledger.initial loading
    (after.1.run runtime).observe query o =
      Reactive.circuit.observe query
        (SramExecution.reactiveRun
          (SramExecution.withWords (SramExecution.core after.1.registers) (fullWords c)) runtime) o := by
  have ht := SramCorrespondence.initialized_to_execution_observe s i hi loading runtime hv hr query hq o
  exact ht.trans (congrArg (fun state : Values Reactive.Register =>
    Reactive.circuit.observe query (SramExecution.reactiveRun state runtime) o)
    (initialized_source_reference c s i hi loading hs hv))

end Pinwheel.Hardware.Buffered.SpiSource
