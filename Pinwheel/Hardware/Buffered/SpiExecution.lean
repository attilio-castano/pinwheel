import Pinwheel.Hardware.Buffered.SpiSource
import Pinwheel.Hardware.Buffered.ReactiveProofs

/-! Universal execution of the independently decoded compact mode-0 SPI image.
The decoder reads stored words, loop controls and the branch dictionary; it
never receives the source Config. Execution uses the existing Buffered semantic
interpreter. This closes source/image execution at that interpreter, not the
separate packed-register circuit recurrence or serial/RTL boundary. -/
namespace Pinwheel.Hardware.Buffered.SpiExecution
open Pinwheel.Hardware Pinwheel.Program Engine.Reactive Engine.Reactive.Counted

/-- Decode the admitted four-row SPI layout. Missing/nonzero dictionary entries,
noncanonical controls and an outer bound outside one-to-four bytes fail closed.
Leaf opcodes and reserved fields are checked by the independent linear decoder. -/
def decode (rows : Memory.Contents 6 92) (dictionary : Memory.Contents 4 56) :
    Option Program.Buffered.Program := do
  let a ← SpiSource.decodeLinear ((rows 0).extractLsb' 0 64)
  let b ← SpiSource.decodeLinear ((rows 1).extractLsb' 0 64)
  let finish ← SpiSource.decodeLinear ((rows 2).extractLsb' 0 64)
  let halt ← SpiSource.decodeLinear ((rows 3).extractLsb' 0 64)
  let control := (rows 0).extractLsb' 64 24
  let bound := (control.extractLsb' 8 3).toNat
  if h : bound < 4 then
    let first := BitVec.ofNat 24 (2 + bound * 2^8 + 7 * 2^17)
    let second := BitVec.ofNat 24 (2 + bound * 2^8 + 7 * 2^17 + 2^20 + 2^21)
    if control != first || (rows 1).extractLsb' 64 24 != second ||
        (rows 2).extractLsb' 64 24 != 0 || (rows 3).extractLsb' 64 24 != 0 ||
        !(List.finRange 16).all (fun k => dictionary (BitVec.ofFin k) == 0) ||
        !(List.finRange 4).all (fun k => (rows (BitVec.ofNat 6 k.val)).extractLsb' 88 4 == 0)
      then none
    else
      let code : Schedule Program.Buffered.Instruction :=
        .seq (.repeat ⟨bound, by omega⟩ (.repeat 7 (.seq (.emit a) (.emit b))))
          (.seq (.emit finish) (.emit halt))
      return ⟨code, ⟨4, 7⟩,
        by simp only [code, Schedule.span]; omega,
        by simp only [code, Schedule.nodes]; decide,
        by simp only [code, Schedule.nesting]; decide⟩
  else none

private theorem word_slice (c : SpiSource.Config) (k : BitVec 6) :
    (SpiSource.rows c k).extractLsb' 0 64 = SpiSource.word c k := by
  simp only [SpiSource.rows, BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 64 ≤ 88),
    BitVec.extractLsb'_append_eq_right]

private theorem control_slice (c : SpiSource.Config) (k : BitVec 6) :
    (SpiSource.rows c k).extractLsb' 64 24 = SpiSource.control c k := by
  simp only [SpiSource.rows, BitVec.extractLsb'_append_eq_of_add_le (by decide : 64 + 24 ≤ 88)]
  exact BitVec.extractLsb'_append_eq_left
  done

private theorem index_slice (c : SpiSource.Config) (k : BitVec 6) :
    (SpiSource.rows c k).extractLsb' 88 4 = 0 := by
  unfold SpiSource.rows
  exact BitVec.extractLsb'_append_eq_left
  done

/-- The actual emitted row/control/dictionary bytes reconstruct the original
counted source. The decoder is not supplied the source's loop count. -/
theorem decode_source (c : SpiSource.Config) :
    decode (SpiSource.rows c) SpiSource.dictionary = some (BufferedSPI.program c) := by
  have h0 := SpiSource.source_leaf_decode c (0 : Fin 4)
  have h1 := SpiSource.source_leaf_decode c (1 : Fin 4)
  have h2 := SpiSource.source_leaf_decode c (2 : Fin 4)
  have h3 := SpiSource.source_leaf_decode c (3 : Fin 4)
  change SpiSource.decodeLinear (SpiSource.word c 0) = some (SpiSource.leaf c 0) at h0
  change SpiSource.decodeLinear (SpiSource.word c 1) = some (SpiSource.leaf c 1) at h1
  change SpiSource.decodeLinear (SpiSource.word c 2) = some (SpiSource.leaf c 2) at h2
  change SpiSource.decodeLinear (SpiSource.word c 3) = some (SpiSource.leaf c 3) at h3
  simp only [decode, word_slice, h0, h1, h2, h3, control_slice, index_slice]
  have hb := (SpiSource.loop_descriptor c).2.2.1
  have hc : c.bytesMinusOne.val < 8 := Nat.lt_trans c.bytesMinusOne.isLt (by decide)
  simp only [hb, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc]
  simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  simp [c.bytesMinusOne.isLt, SpiSource.control, SpiSource.dictionary, SpiSource.leaf,
    SpiSource.leafAt, BufferedSPI.program, BufferedSPI.code]
  done

/-- Execute the decoded resident image using the independent source interpreter.
The result includes the complete core, ownership, TX/RX prefix and sampler state.
-/
def start (rows : Memory.Contents 6 92) (dictionary : Memory.Contents 4 56)
    (capacity : Transfer.Capacity) (s : Program.Buffered.State) : Option Program.Buffered.State :=
  (decode rows dictionary).map fun p => Program.Buffered.start p capacity s

def run (rows : Memory.Contents 6 92) (dictionary : Memory.Contents 4 56)
    (capacity : Transfer.Capacity) (s : Program.Buffered.State)
    (incoming : Nat → Inputs) (edges : Nat) : Option Program.Buffered.State :=
  (decode rows dictionary).map fun p => Program.Buffered.run p capacity s incoming edges

/-- Universal START correspondence, including stale owners and TX/RX entry
failure. No successful-transfer or observational-equality premise is assumed. -/
theorem start_source (c : SpiSource.Config) (capacity : Transfer.Capacity)
    (s : Program.Buffered.State) :
    start (SpiSource.rows c) SpiSource.dictionary capacity s =
      some (Program.Buffered.start (BufferedSPI.program c) capacity s) := by
  rw [start, decode_source]
  rfl
  done

/-- Every time prefix and every raw-input history has exactly the same complete
state as the typed source. Payloads, ownership and buffers are arbitrary; faults
and retained completion are covered by the equality, not excluded by a premise.
This is image-interpreter equality, not packed circuit execution equality. -/
theorem run_source (c : SpiSource.Config) (capacity : Transfer.Capacity)
    (s : Program.Buffered.State) (incoming : Nat → Inputs) (edges : Nat) :
    run (SpiSource.rows c) SpiSource.dictionary capacity s incoming edges =
      some (Program.Buffered.run (BufferedSPI.program c) capacity s incoming edges) := by
  rw [run, decode_source]
  rfl
  done

/-- The tracked image is justified by actual accepted loading and resident
coverage. Equality with source bytes is derived, not a caller-supplied premise.
-/
theorem resident_decode (c : SpiSource.Config) (s : SramState.State)
    (t : SramLoading.Ledger) (known : SpiSource.Known c t)
    (established : SramCorrespondence.Established s t)
    (valid : s.registers (.core .valid) = 1) (count : s.registers (.core .count) = 4) :
    decode (SramExecution.projectedRow 4 t.rows) t.dictionaryWords =
      some (BufferedSPI.program c) := by
  have rows := funext (SpiSource.projected_source_row c s t known established valid count)
  rw [rows, SpiSource.known_dictionary c t known]
  exact decode_source c
  done

/-- Cold initialization plus actual source-constrained accepted writes is enough
for a valid cut to decode to the source; no arbitrary SRAM startup/Q assumption,
extra count premise, or source execution equality premise is required. -/
theorem initialized_decode (c : SpiSource.Config) (s : SramState.State)
    (i : Values Reactive.Input) (coldInit : i .initialize = 1)
    (loading : List (Values Reactive.Input))
    (source : SpiSource.SourceHistory c (s.step i) loading)
    (valid : (SramLoading.run (s.step i) SramLoading.Ledger.initial loading).1.registers (.core .valid) = 1) :
    let after := SramLoading.run (s.step i) SramLoading.Ledger.initial loading
    decode (SramExecution.projectedRow 4 after.2.rows) after.2.dictionaryWords =
      some (BufferedSPI.program c) :=
  resident_decode c _ _ (SpiSource.known_run c (s.step i) SramLoading.Ledger.initial loading
    (SpiSource.known_initial c) source)
    (SramCorrespondence.initialized_established s i coldInit loading) valid
    (SpiSource.initialized_source_count c s i coldInit loading source valid)

/-- Execution from the independently tracked, actually admitted image agrees
with the source for arbitrary initial source state, payload/owner/buffers and
input histories. The source state is explicit; mapping the actual cut's packed
register state to it remains the separate circuit relation obligation. -/
theorem initialized_run (c : SpiSource.Config) (s : SramState.State)
    (i : Values Reactive.Input) (coldInit : i .initialize = 1)
    (loading : List (Values Reactive.Input))
    (source : SpiSource.SourceHistory c (s.step i) loading)
    (valid : (SramLoading.run (s.step i) SramLoading.Ledger.initial loading).1.registers (.core .valid) = 1)
    (capacity : Transfer.Capacity) (state : Program.Buffered.State)
    (incoming : Nat → Inputs) (edges : Nat) :
    let after := SramLoading.run (s.step i) SramLoading.Ledger.initial loading
    run (SramExecution.projectedRow 4 after.2.rows) after.2.dictionaryWords capacity state incoming edges =
      some (Program.Buffered.run (BufferedSPI.program c) capacity state incoming edges) := by
  dsimp only
  unfold run
  rw [initialized_decode c s i coldInit loading source valid]
  rfl
  done

private theorem packed_low_bit (tx : BitVec 32) : 0#2 ++ tx.extractLsb' 0 1 = if tx.getLsbD 0 then 1#3 else 0#3 := by
  apply (BitVec.eq_of_getLsbD_eq_iff).2
  intro j hj
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  have hj' : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases hj' with rfl | rfl | rfl
  all_goals cases h : tx.getLsbD 0 <;> simp_all
  done

private theorem low_fields : ∀ d : Fin 256,
    let w := (SpiSource.encodeLinear (BufferedSPI.low d)).getD 0
    w.extractLsb' 0 3 = 1 ∧ w.extractLsb' 3 3 = 0 ∧
    w.extractLsb' 6 3 = 7 ∧ w.extractLsb' 17 3 = 0 ∧
    w.extractLsb' 20 2 = 0 ∧ w.extractLsb' 24 1 = 0 ∧ w.extractLsb' 25 1 = 0 := by
  decide +kernel

theorem low_entry_levels (c : SpiSource.Config) (i : Values Reactive.Input)
    (s : Values Reactive.Register) (word : Reactive.entryWord.eval i s = SpiSource.word c 0) :
    Reactive.entryLevels.eval i s =
      Program.Buffered.setBit 0 0 ((Reactive.entryTx.eval i s).getLsbD 0) := by
  have fields := low_fields c.halfCyclesMinusOne
  change Reactive.entryWord.eval i s = (SpiSource.encodeLinear (BufferedSPI.low c.halfCyclesMinusOne)).getD 0 at word
  rcases fields with ⟨kind, levels, enabled, preserve, output, enable, invert⟩
  simp only [Reactive.entryLevels, Reactive.isKind, Reactive.kind, Reactive.shifted,
    Reactive.pack, Reactive.shiftValue, Reactive.preserve, Reactive.either, Expr.eval, word, kind, levels, preserve, output, enable, invert]
  simp [Program.Buffered.setBit]
  simpa using packed_low_bit (Reactive.entryTx.eval i s)
  done

private theorem high_fields : ∀ d : Fin 256,
    let w := (SpiSource.encodeLinear (BufferedSPI.high d)).getD 0
    w.extractLsb' 0 3 = 2 ∧ w.extractLsb' 3 3 = 2 ∧
    w.extractLsb' 6 3 = 7 ∧ w.extractLsb' 17 3 = 1 ∧
    w.extractLsb' 26 3 = 0 ∧ w.extractLsb' 22 2 = 1 := by
  decide +kernel

theorem high_entry_levels (c : SpiSource.Config) (i : Values Reactive.Input)
    (s : Values Reactive.Register) (word : Reactive.entryWord.eval i s = SpiSource.word c 1) :
    Reactive.entryLevels.eval i s =
      (Program.Buffered.keepPins ⟨2, 7⟩ ⟨s .levels, s .enabled⟩ 1 0).levels := by
  have fields := high_fields c.halfCyclesMinusOne
  change Reactive.entryWord.eval i s = (SpiSource.encodeLinear (BufferedSPI.high c.halfCyclesMinusOne)).getD 0 at word
  rcases fields with ⟨kind, levels, enabled, preserve, preserveEnabled, append⟩
  simp only [Reactive.entryLevels, Reactive.isKind, Reactive.kind, Reactive.preserve,
    Reactive.either, Expr.eval, word, kind, levels, preserve]
  rw [BitVec.not_and]
  simp [Program.Buffered.keepPins]
  done

/-- The actual RX selector reads preedge stage2, never the incoming raw input. -/
theorem high_sampled (c : SpiSource.Config) (i : Values Reactive.Input)
    (s : Values Reactive.Register) (word : Reactive.entryWord.eval i s = SpiSource.word c 1) :
    Reactive.sampled.eval i s = (s .stage2).extractLsb' 0 1 := by
  have fields := high_fields c.halfCyclesMinusOne
  change Reactive.entryWord.eval i s = (SpiSource.encodeLinear (BufferedSPI.high c.halfCyclesMinusOne)).getD 0 at word
  rcases fields with ⟨kind, levels, enabled, preserve, preserveEnabled, append⟩
  simp only [Reactive.sampled, Expr.eval, word, append]
  simp
  done

theorem high_append_bit (c : SpiSource.Config) (i : Values Reactive.Input)
    (s : Values Reactive.Register) (word : Reactive.entryWord.eval i s = SpiSource.word c 1)
    (k : Fin 32) :
    (Reactive.appended.eval i s).getLsbD k.val =
      if Reactive.entryRxLength.eval i s = BitVec.ofNat 6 k.val then (s .stage2).getLsbD 0
      else (if Reactive.starting.eval i s = 1 then 0 else s .rxData).getLsbD k.val := by
  unfold Reactive.appended
  rw [Reactive.pack_selected_bit]
  simp only [Expr.eval, high_sampled c i s word]
  by_cases h : Reactive.entryRxLength.eval i s = BitVec.ofNat 6 k.val
  all_goals simp [h]
  done

/-- On an actual accepted RX append edge, the circuit writes the selected
preedge stage2 bit at exactly the next prefix index and holds all other bits.
The guards concern one real circuit edge; this is not a global relation premise.
-/
theorem high_rx_step (c : SpiSource.Config) (i : Values Reactive.Input)
    (s : Values Reactive.Register) (word : Reactive.entryWord.eval i s = SpiSource.word c 1)
    (owner : Reactive.clearOwner.eval i s = 0) (append : Reactive.appending.eval i s = 1)
    (k : Fin 32) :
    ((Reactive.circuit.step i s) .rxData).getLsbD k.val =
      if Reactive.entryRxLength.eval i s = BitVec.ofNat 6 k.val then (s .stage2).getLsbD 0
      else (if Reactive.starting.eval i s = 1 then 0 else s .rxData).getLsbD k.val := by
  have update : (Reactive.circuit.step i s) .rxData = Reactive.appended.eval i s := by
    simp [Circuit.step, Reactive.circuit, Reactive.next, Expr.eval, owner, append]
  rw [update]
  exact high_append_bit c i s word k
  done

end Pinwheel.Hardware.Buffered.SpiExecution
