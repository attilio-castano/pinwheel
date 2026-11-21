import Pinwheel.Hardware.StreamingReady.Initialization
import Pinwheel.Hardware.StreamingReady.SegmentHandoffFence
import Pinwheel.Hardware.StreamingReady.SegmentLegacy
import Pinwheel.Hardware.StreamingReady.SegmentPathControl

/-! The segmented instruction store can be reprogrammed at a free cut.
The loader handles the encoded words of any checked image, independent of
the instructions that ran in the previous owner's session. -/
namespace Pinwheel.Hardware.StreamingReady.SegmentReload

open Pinwheel.Hardware SegmentCore
open Pinwheel.Program.StreamingReadySegments (Row Image)
open Pinwheel.Program.StreamingReady (Pins)

/-- The loader's entry cut. Both normal RELEASE and warm cancellation can
produce this cut. -/
structure Free (registered : Bool) (s : Values (Register a)) : Prop where
  phase : s (.base .phase) = 0#3
  openTX : s .txClosed = 0#1
  coherent : registered = true → SegmentStore.Coherent s

theorem Free.ofFence (h : SegmentHandoffFence.FreeCut registered s) : Free registered s :=
  ⟨h.phase, h.empty.txClosed, h.coherent⟩

/-- A source-bound delivery trace with quiet clocks between the writes. -/
inductive Upload (words : List (BitVec 64)) : Nat → List (Values Core.Input) → Prop
  | nil : Upload words 0 []
  | idle (before : Upload words n trace) (i : Values Core.Input)
      (cold : i .initialize = 0#1) (command : i .command = 0#4) :
      Upload words n (trace ++ [@i])
  | write (before : Upload words n trace) (i : Values Core.Input)
      (selected : words[n]? = some data)
      (input : Initialization.Write i (BitVec.ofNat 6 n) data) :
      Upload words (n + 1) (trace ++ [@i])

structure Commit (rows : List Row) (idle : Pins) (i : Values Core.Input) : Prop where
  cold : i .initialize = 0#1
  command : i .command = 2#4
  count : i .count = BitVec.ofNat 7 rows.length
  levels : i .idleLevels = idle.levels
  enabled : i .idleEnabled = idle.enabled

structure Start (generation count : BitVec 16) (i : Values Core.Input) : Prop where
  cold : i .initialize = 0#1
  command : i .command = 3#4
  expected : i .expectedGeneration = generation
  count : i .startCount = count

structure InstalledCut (registered : Bool) (rows : List Row) (idle : Pins)
    (s installed : Values (Register a)) : Prop where
  free : Free registered installed
  image : SegmentPathControl.Installed rows installed
  pending : installed (.base .pending) = 0#1
  idleLevels : installed (.base .idleLevels) = idle.levels
  idleEnabled : installed (.base .idleEnabled) = idle.enabled
  generation : installed (.base .generation) = s (.base .generation) + 1
  transfer : installed (.base .transfer) = s (.base .transfer)
  tail : ∀ k : BitVec 6, rows.length ≤ k.toNat → installed (.base (.word k)) = s (.base (.word k))

structure StartedCut (registered : Bool) (rows : List Row) (idle : Pins) (count : BitVec 16)
    (s started : Values (Register a)) : Prop where
  entry : SegmentPathControl.AtBoundary registered rows 0 none started
  generation : started (.base .generation) = s (.base .generation) + 1
  transfer : started (.base .transfer) = s (.base .transfer) + 1
  total : started (.base .total) = count
  remaining : started (.base .remaining) = count
  empty : SegmentHandoffFence.EmptyCustody started
  levels : started (.base .levels) = idle.levels
  enabled : started (.base .enabled) = idle.enabled

private theorem free_step (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (free : Free registered s) (port : Core.Register a w) :
    (circuit a registered).step i s (.base port) =
      (Streaming.Core.circuit a).step i (project s) port := by
  have legacy := SegmentLegacy.core_step registered i s free.openTX
    (SegmentLegacy.edge_of_not_fetch registered i s (by simp [free.phase])) free.coherent
  exact (congrArg (fun state : Values (Core.Register a) => state port) legacy.1).trans
    (LoaderEquivalence.free_step_equal i (project s) free.phase port)

private theorem no_reset (i : Values Core.Input) (s : Values (Register a))
    (cold : i .initialize = 0#1) (warm : i .command ≠ 15#4) :
    Streaming.Core.resetting.eval i (project s) = 0#1 := by
  simp [Streaming.Core.resetting, Streaming.Core.cold, Streaming.Core.warm, Streaming.Core.cmd,
    Streaming.Core.both, Streaming.Core.either, Expr.eval, cold, warm]

private theorem free_flag (i : Values Core.Input) (s : Values (Register a))
    (phase : s (.base .phase) = 0#3) (reset : Streaming.Core.resetting.eval i (project s) = 0#1) :
    Streaming.Core.free.eval i (project s) = 1#1 := by
  simp [Streaming.Core.free, Streaming.Core.both, Expr.eval, reset, project, phase]

private structure LoaderStep (registered : Bool) (i : Values Core.Input)
    (s after : Values (Register a)) (writing committing : Bool) : Prop where
  free : Free registered after
  transfer : after (.base .transfer) = s (.base .transfer)
  generation : after (.base .generation) =
    if committing then s (.base .generation) + 1 else s (.base .generation)
  word : ∀ k, after (.base (.word k)) =
    if writing && (i .address == k) then i .word else s (.base (.word k))
  written : after (.base .written) =
    if writing then s (.base .written) ||| (1#64 <<< (i .address).toNat) else s (.base .written)
  pending : after (.base .pending) =
    if writing then 1#1 else if committing then 0#1 else s (.base .pending)
  valid : after (.base .valid) =
    if writing then 0#1 else if committing then 1#1 else s (.base .valid)
  count : after (.base .count) = if committing then i .count else s (.base .count)
  idleLevels : after (.base .idleLevels) = if committing then i .idleLevels else s (.base .idleLevels)
  idleEnabled : after (.base .idleEnabled) = if committing then i .idleEnabled else s (.base .idleEnabled)

set_option linter.unusedSimpArgs false in
private theorem loader_step (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (free : Free registered s) (cold : i .initialize = 0#1) (warm : i .command ≠ 15#4)
    (noStart : i .command ≠ 3#4) (writing committing : Bool)
    (write : Streaming.Core.writing.eval i (project s) = BitVec.ofBool writing)
    (commit : Streaming.Core.committing.eval i (project s) = BitVec.ofBool committing) :
    LoaderStep registered i s ((circuit a registered).step i s) writing committing := by
  have reset := no_reset i s cold warm
  have starting : Streaming.Core.starting.eval i (project s) = 0#1 := by
    simp [Streaming.Core.starting, Streaming.Core.both, Streaming.Core.cmd, Expr.eval, noStart]
  have legacy := SegmentLegacy.core_step registered i s free.openTX
    (SegmentLegacy.edge_of_not_fetch registered i s (by simp [free.phase])) free.coherent
  have coherent : registered = true → SegmentStore.Coherent ((circuit a registered).step i s) := by
    intro useCache
    subst registered
    exact SegmentStore.coherent_after_edge i s
  refine ⟨⟨?_, legacy.2, coherent⟩, ?_, ?_, fun k => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    rw [free_step registered i s free]
  all_goals
    simp [Streaming.Core.circuit, Circuit.step, Streaming.Core.next, Streaming.Core.nextRaw,
      Streaming.Core.cold, Streaming.Core.releasing, Streaming.Core.hostOwner, Streaming.Core.owned,
      Streaming.Core.busy, Streaming.Core.retained, Streaming.Core.reserving, Streaming.Core.capture,
      Streaming.Core.highEnd, Streaming.Core.fetching, Streaming.Core.isPhase,
      Streaming.Core.either, Streaming.Core.both, Expr.eval, reset, starting, write, commit,
      Streaming.SourceRefinement.inc_eval, free.phase, project, cold, decide_eq_true_eq]
  case refine_4 => by_cases equal : i .address = k <;> simp [equal]
  case refine_5 =>
    by_cases on : writing = true
    · simp only [on, if_true]
      exact Streaming.Initialization.written_write i (project s)
    · simp [on]
  all_goals done

private theorem quiet_step (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (free : Free registered s) (cold : i .initialize = 0#1) (command : i .command = 0#4) :
    LoaderStep registered i s ((circuit a registered).step i s) false false := by
  have write : Streaming.Core.writing.eval i (project s) = 0#1 := by
    simp [Streaming.Core.writing, Streaming.Core.both, Streaming.Core.cmd, Expr.eval, command]
  have commit : Streaming.Core.committing.eval i (project s) = 0#1 := by
    simp [Streaming.Core.committing, Streaming.Core.both, Streaming.Core.cmd, Expr.eval, command]
  exact loader_step registered i s free cold (by simp [command]) (by simp [command])
    false false write commit

private theorem run_snoc (registered : Bool) (s : Values (Register a))
    (trace : List (Values Core.Input)) (i : Values Core.Input) :
    @SegmentTiming.run a registered s (trace ++ [@i]) =
      @Circuit.step _ _ _ (circuit a registered) i (SegmentTiming.run registered s trace) := by
  rw [SegmentTiming.run_append]
  rfl

structure UploadedCut (registered : Bool) (words : List (BitVec 64)) (n : Nat)
    (s uploaded : Values (Register a)) : Prop where
  free : Free registered uploaded
  generation : uploaded (.base .generation) = s (.base .generation)
  transfer : uploaded (.base .transfer) = s (.base .transfer)
  writtenWords : ∀ k : Fin 64, k.val < n →
    words[k.val]? = some (uploaded (.base (.word (BitVec.ofNat 6 k.val))))
  covered : ∀ k : Fin 64, k.val < n → (uploaded (.base .written)).getLsbD k.val = true
  pending : 0 < n → uploaded (.base .pending) = 1#1 ∧ uploaded (.base .valid) = 0#1
  tail : ∀ k : BitVec 6, n ≤ k.toNat → uploaded (.base (.word k)) = s (.base (.word k))

/-- Ordered WRITE delivery establishes the new prefix even if stale words and
coverage bits were present in the old bank. -/
theorem Upload.run (upload : Upload words n trace) (capacity : words.length ≤ 64)
    (registered : Bool) (s : Values (Register a)) (free : Free registered s) :
    UploadedCut registered words n s (SegmentTiming.run registered s trace) := by
  induction upload with
  | nil =>
    exact ⟨free, rfl, rfl, fun _ h => by omega, fun _ h => by omega,
      fun h => by omega, fun _ _ => rfl⟩
  | @idle n trace previous i cold command ih =>
    rw [run_snoc]
    let before : Values (Register a) := SegmentTiming.run registered s trace
    have edge := quiet_step registered i before ih.free cold command
    refine ⟨edge.free, ?_, edge.transfer.trans ih.transfer, ?_, ?_, ?_, ?_⟩
    · simpa using edge.generation.trans ih.generation
    · intro k live
      rw [edge.word]
      simpa using ih.writtenWords k live
    · intro k live
      rw [edge.written]
      simpa using ih.covered k live
    · intro live
      rw [edge.pending, edge.valid]
      simpa using ih.pending live
    · intro k outside
      rw [edge.word]
      simpa using ih.tail k outside
  | @write n trace data previous i selected input ih =>
    rw [run_snoc]
    let before : Values (Register a) := SegmentTiming.run registered s trace
    have reset := no_reset i before input.cold (by simp [input.command])
    have available := free_flag i before ih.free.phase reset
    have write : Streaming.Core.writing.eval i (project before) = 1#1 := by
      simp [Streaming.Core.writing, Streaming.Core.both, Streaming.Core.cmd, Expr.eval,
        input.command, available]
    have commit : Streaming.Core.committing.eval i (project before) = 0#1 := by
      simp [Streaming.Core.committing, Streaming.Core.both, Streaming.Core.cmd, Expr.eval, input.command]
    have edge := loader_step registered i before ih.free input.cold
      (by simp [input.command]) (by simp [input.command]) true false write commit
    have bound : n < 64 := Nat.lt_of_lt_of_le (List.getElem?_eq_some_iff.mp selected).1 capacity
    refine ⟨edge.free, ?_, edge.transfer.trans ih.transfer, ?_, ?_, ?_, ?_⟩
    · simpa using edge.generation.trans ih.generation
    · intro k live
      rw [edge.word]
      by_cases last : k.val = n
      · simp [last, input.address, input.word, selected]
      · have old : k.val < n := by omega
        have distinct : BitVec.ofNat 6 n ≠ BitVec.ofNat 6 k.val := by
          intro equal
          apply last
          have values := congrArg BitVec.toNat equal
          simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound, Nat.mod_eq_of_lt k.isLt] using values.symm
        have different : ¬ (true && (i .address == BitVec.ofNat 6 k.val)) = true := by
          simpa only [Bool.true_and, beq_iff_eq, input.address] using distinct
        rw [if_neg different]
        exact ih.writtenWords k old
    · intro k live
      rw [edge.written]
      simp only [if_true]
      rw [Streaming.Initialization.mark_bit]
      by_cases last : k.val = n
      · simp [input.address, last]
      · have old : k.val < n := by omega
        exact Bool.or_eq_true_iff.mpr (.inl (ih.covered k old))
    · intro _
      exact ⟨edge.pending, edge.valid⟩
    · intro k outside
      have distinct : BitVec.ofNat 6 n ≠ k := by
        intro equal
        have values := congrArg BitVec.toNat equal
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound] at values
        omega
      rw [edge.word]
      simpa [input.address, distinct] using ih.tail k (by omega)

private theorem checked_bounds (image : Image rows budget) : 0 < rows.length ∧ rows.length ≤ 64 := by
  have checked := image.checked
  unfold Pinwheel.Program.StreamingReadySegments.check at checked
  split at checked
  · rename_i inside
    simp only [Bool.and_eq_true, decide_eq_true_eq] at inside
    exact inside.1
  · contradiction

/-- The original loader only uses the word count when deciding to commit.
Use a geometry of that size to reuse its coverage and range proofs. -/
private def geometry (rows : List Row) (positive : 0 < rows.length) (capacity : rows.length ≤ 64)
    : Program.Streaming.Program :=
  { memory := Vector.replicate 64 .halt
    lengthMinusOne := ⟨rows.length - 1, by omega⟩ }

private theorem geometry_length (rows : List Row) (positive : 0 < rows.length)
    (capacity : rows.length ≤ 64) : (geometry rows positive capacity).length = rows.length := by
  simp only [geometry, Program.Streaming.Program.length]
  omega

/-- After explicit WRITE delivery, COMMIT publishes exactly the checked
image and its declared idle pads. Unaddressed higher rows stay untouched
and are fenced by the installed count. -/
theorem install (registered : Bool) (s : Values (Register a))
    (rows : List Row) (idle : Pins) (trace : List (Values Core.Input))
    (positive : 0 < rows.length) (capacity : rows.length ≤ 64)
    (upload : Upload (rows.map Row.encode) rows.length trace) (free : Free registered s)
    (commit : Values Core.Input) (committing : Commit rows idle commit)
    (generationRoom : s (.base .generation) ≠ 65535#16) :
    InstalledCut registered rows idle s (SegmentTiming.run registered s (trace ++ [@commit])) := by
  have wordCapacity : (rows.map Row.encode).length ≤ 64 := by
    simpa only [List.length_map] using capacity
  let uploaded : Values (Register a) := SegmentTiming.run registered s trace
  have uploadedCut := upload.run wordCapacity registered s free
  have reset := no_reset commit uploaded committing.cold (by simp [committing.command])
  have available := free_flag commit uploaded uploadedCut.free.phase reset
  have write : Streaming.Core.writing.eval commit (project uploaded) = 0#1 := by
    simp [Streaming.Core.writing, Streaming.Core.both, Streaming.Core.cmd, Expr.eval, committing.command]
  let shape := geometry rows positive capacity
  have size : shape.length = rows.length := geometry_length rows positive capacity
  have count : commit .count = BitVec.ofNat 7 shape.length := by rw [size, committing.count]
  have coverage := Streaming.Initialization.covered_prefix shape commit (project uploaded) count
    (fun k live => uploadedCut.covered k (size ▸ live))
  have countValid := Streaming.Initialization.count_valid shape commit (project uploaded) count
  have pending : uploaded (.base .pending) = 1#1 := (uploadedCut.pending positive).1
  have room : uploaded (.base .generation) ≠ 65535#16 := by
    change (SegmentTiming.run registered s trace (.base .generation)) ≠ _
    rw [uploadedCut.generation]
    exact generationRoom
  have commitFlag : Streaming.Core.committing.eval commit (project uploaded) = 1#1 := by
    simp [Streaming.Core.committing, Streaming.Core.both, Streaming.Core.cmd, Streaming.Core.space,
      Expr.eval, available, committing.command, countValid, coverage, project, pending, room]
  have edge := loader_step registered commit uploaded uploadedCut.free committing.cold
    (by simp [committing.command]) (by simp [committing.command]) false true write commitFlag
  rw [run_snoc]
  refine ⟨edge.free, ⟨capacity, ?_, edge.valid, ?_⟩, edge.pending, ?_, ?_,
    ?_, edge.transfer.trans uploadedCut.transfer, ?_⟩
  · rw [edge.count, if_pos rfl, committing.count, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  · intro k
    have live : k.val < 64 := Nat.lt_of_lt_of_le k.isLt capacity
    have bank := uploadedCut.writtenWords ⟨k.val, live⟩ k.isLt
    rw [edge.word]
    simpa [List.getElem?_map, List.getElem?_eq_getElem k.isLt] using bank.symm
  · exact edge.idleLevels.trans committing.levels
  · exact edge.idleEnabled.trans committing.enabled
  · exact edge.generation.trans (congrArg (· + 1) uploadedCut.generation)
  · intro k outside
    exact (edge.word k).trans (uploadedCut.tail k outside)

private theorem installed_preserved {s old after : Values (Register a)}
    (state : InstalledCut registered rows idle s old) (free : Free registered after)
    (image : SegmentPathControl.ImageFrame old after)
    (pending : after (.base .pending) = old (.base .pending))
    (levels : after (.base .idleLevels) = old (.base .idleLevels))
    (enabled : after (.base .idleEnabled) = old (.base .idleEnabled))
    (transfer : after (.base .transfer) = old (.base .transfer)) :
    InstalledCut registered rows idle s after :=
  ⟨free, image.installed state.image, pending.trans state.pending, levels.trans state.idleLevels,
    enabled.trans state.idleEnabled, image.generation.trans state.generation,
    transfer.trans state.transfer, fun k outside => (image.word k).trans (state.tail k outside)⟩

/-- Reply and inter-command clocks can separate COMMIT from START. Those
clocks preserve the new descriptor while the input samplers keep running. -/
theorem InstalledCut.idle_run {s installed : Values (Register a)}
    (state : InstalledCut registered rows idle s installed) (trace : List (Values Core.Input))
    (quiet : ∀ i ∈ trace, i .initialize = 0#1 ∧ i .command = 0#4) :
    InstalledCut registered rows idle s (SegmentTiming.run registered installed trace) := by
  induction trace generalizing installed with
  | nil => exact state
  | cons i rest ih =>
    obtain ⟨cold, command⟩ := quiet i (by simp)
    have edge := quiet_step registered i installed state.free cold command
    exact ih (installed_preserved state edge.free ⟨edge.count, edge.valid, edge.word, edge.generation⟩
      edge.pending edge.idleLevels edge.idleEnabled edge.transfer)
      (fun sample h => quiet sample (List.mem_cons_of_mem _ h))

/-- A rejected stale START keeps the newly installed image ready for a fresh
START and causes no ownership change. -/
theorem InstalledCut.reject_stale {s installed : Values (Register a)}
    (state : InstalledCut registered rows idle s installed) (i : Values Core.Input)
    (cold : i .initialize = 0#1) (command : i .command = 3#4)
    (stale : i .expectedGeneration ≠ s (.base .generation) + 1) :
    (circuit a registered).observe i installed .rejected = 1#1 ∧
      InstalledCut registered rows idle s ((circuit a registered).step i installed) := by
  have staleInstalled : i .expectedGeneration ≠ installed (.base .generation) := by
    rw [state.generation]
    exact stale
  obtain ⟨rejected, unchanged⟩ :=
    SegmentHandoffFence.stale_start registered i installed cold command state.free.phase staleInstalled
  have preserved {w : Nat} (r : Register a w) :=
    congrArg (fun values : Values (Register a) => values r) unchanged
  refine ⟨rejected, installed_preserved state ⟨?_, ?_, ?_⟩
    ⟨preserved (.base .count), preserved (.base .valid), fun k => preserved (.base (.word k)),
      preserved (.base .generation)⟩ (preserved (.base .pending)) (preserved (.base .idleLevels))
      (preserved (.base .idleEnabled)) (preserved (.base .transfer))⟩
  · exact (preserved (.base .phase)).trans state.free.phase
  · exact (preserved .txClosed).trans state.free.openTX
  · intro useCache
    subst registered
    exact SegmentStore.coherent_after_edge i installed

set_option linter.unusedSimpArgs false in
/-- The new generation can start at PC zero with the installed words,
empty custody, and the newly declared idle drive. This operation needs no
assumption about the protocol that produced the preceding free cut. -/
theorem start_installed (registered : Bool) (s installed : Values (Register a))
    (state : InstalledCut registered rows idle s installed) (i : Values Core.Input)
    (transferRoom : s (.base .transfer) ≠ 65535#16)
    (starting : Start (s (.base .generation) + 1) requestedCount i) :
    StartedCut registered rows idle requestedCount s ((circuit a registered).step i installed) := by
  have transferSpace : installed (.base .transfer) ≠ 65535#16 := by rwa [state.transfer]
  have expected : i .expectedGeneration = installed (.base .generation) :=
    starting.expected.trans state.generation.symm
  have admission : Core.starting.eval i (project installed) = 1#1 := by
    simp [Core.starting, Core.free, Core.space, Core.warm, Core.cold, Core.resetting, Core.cmd,
      Core.both, Core.either, Expr.eval, project, state.free.phase, state.image.valid,
      starting.cold, starting.command, expected, transferSpace]
  obtain ⟨entry, epoch, transfer, total, remaining, accepted, consumed, produced⟩ :=
    SegmentPathControl.start_at_boundary registered i installed state.image admission
  have unchanged := SegmentLegacy.core_step registered i installed state.free.openTX
    (SegmentLegacy.edge_of_not_fetch registered i installed (by simp [state.free.phase])) state.free.coherent
  have oldAdmission : Streaming.Core.starting.eval i (project installed) = 1#1 := admission
  have reset := no_reset i installed starting.cold (by simp [starting.command])
  refine ⟨entry, epoch.trans state.generation, transfer.trans (congrArg (· + 1) state.transfer),
    total.trans starting.count, remaining.trans starting.count,
    ⟨?_, ?_, ?_, ?_, accepted, consumed, produced, ?_, unchanged.2, entry.latched⟩, ?_, ?_⟩
  all_goals
    rw [free_step registered i installed state.free]
    simp [Streaming.Core.circuit, Circuit.step, Streaming.Core.next, Streaming.Core.nextRaw,
      Streaming.Core.nextPins, Streaming.Core.either, Streaming.Core.both, Expr.eval, reset,
      oldAdmission, project, state.idleLevels, state.idleEnabled]

theorem upload_start (registered : Bool) (s : Values (Register a))
    (image : Image rows budget) (idle : Pins) (trace : List (Values Core.Input))
    (upload : Upload image.words rows.length trace) (free : Free registered s)
    (commit start : Values Core.Input) (requestedCount : BitVec 16) (committing : Commit rows idle commit)
    (generationRoom : s (.base .generation) ≠ 65535#16)
    (transferRoom : s (.base .transfer) ≠ 65535#16)
    (starting : Start (s (.base .generation) + 1) requestedCount start) :
    let installed : Values (Register a) := SegmentTiming.run registered s (trace ++ [@commit])
    let started : Values (Register a) := (circuit a registered).step start installed
    InstalledCut registered rows idle s installed ∧
      StartedCut registered rows idle requestedCount s started := by
  obtain ⟨positive, capacity⟩ := checked_bounds image
  have loaded := install registered s rows idle trace positive capacity upload free commit committing generationRoom
  exact ⟨loaded, start_installed registered s _ loaded start transferRoom starting⟩

inductive Settlement (i : Values Core.Input) (s : Values (Register a)) : Prop
  | release (accepted : SegmentCustody.AtRelease i s)
  | cancelTimeout (fault : s (.base .phase) = 6#3) (cold : i .initialize = 0#1)
      (command : i .command = 15#4)

/-- Settling a retained owner frees the loader and preserves the last owner tag. -/
theorem Settlement.closes {i : Values Core.Input} {s : Values (Register a)}
    (settlement : Settlement i s) (registered : Bool) :
    let after : Values (Register a) := (circuit a registered).step i s
    SegmentHandoffFence.FreeCut registered after ∧
      after (.base .generation) = s (.base .generation) ∧
      after (.base .transfer) = s (.base .transfer) := by
  cases settlement with
  | release accepted =>
    obtain ⟨free, image, transfer, _, _⟩ := SegmentHandoffFence.release_to_free registered i s accepted
    exact ⟨free, image.generation, transfer⟩
  | cancelTimeout _ cold command =>
    obtain ⟨free, _, generation, transfer⟩ := SegmentHandoffFence.warm_cancel registered i s cold command
    exact ⟨free, generation, transfer⟩

/-- The decoded core edges of a handoff, with the frontend's quiet clocks
retained around the stale START probe. -/
structure HandoffTrace where
  settle : Values Core.Input
  writes : List (Values Core.Input)
  commit : Values Core.Input
  replyClocks : List (Values Core.Input)
  stale : Values Core.Input
  retryClocks : List (Values Core.Input)
  start : Values Core.Input

def HandoffTrace.atSettlement (trace : HandoffTrace) (registered : Bool)
    (s : Values (Register a)) : Values (Register a) :=
  (circuit a registered).step trace.settle s

def HandoffTrace.atStale (trace : HandoffTrace) (registered : Bool)
    (s : Values (Register a)) : Values (Register a) :=
  SegmentTiming.run registered (trace.atSettlement registered s)
    ((trace.writes ++ [@trace.commit]) ++ trace.replyClocks)

def HandoffTrace.atStart (trace : HandoffTrace) (registered : Bool)
    (s : Values (Register a)) : Values (Register a) :=
  SegmentTiming.run registered ((circuit a registered).step trace.stale (trace.atStale registered s))
    trace.retryClocks

structure HandoffDelivery (trace : HandoffTrace) (rows : List Row) (idle : Pins) (count : BitVec 16)
    (s : Values (Register a)) : Prop where
  settlement : Settlement trace.settle s
  writes : Upload (rows.map Row.encode) rows.length trace.writes
  commit : Commit rows idle trace.commit
  reply : ∀ i ∈ trace.replyClocks, i .initialize = 0#1 ∧ i .command = 0#4
  stale : ∃ oldCount, Start (s (.base .generation)) oldCount trace.stale
  retry : ∀ i ∈ trace.retryClocks, i .initialize = 0#1 ∧ i .command = 0#4
  start : Start (s (.base .generation) + 1) count trace.start

structure HandoffResult (trace : HandoffTrace) (registered : Bool) (rows : List Row)
    (idle : Pins) (count : BitVec 16) (s : Values (Register a)) : Prop where
  settled : SegmentHandoffFence.FreeCut registered (trace.atSettlement registered s)
  staleRejected : (circuit a registered).observe trace.stale (trace.atStale registered s) .rejected = 1#1
  installed : InstalledCut registered rows idle (trace.atSettlement registered s) (trace.atStart registered s)
  fresh : StartedCut registered rows idle count s ((circuit a registered).step trace.start
    (trace.atStart registered s))

/-- The same physical loader and owner guarantee applies whether the prior
protocol released normally or explicitly cancelled a retained timeout. -/
theorem handoff (trace : HandoffTrace) (registered : Bool) (s : Values (Register a))
    (delivery : HandoffDelivery trace rows idle requestedCount s)
    (positive : 0 < rows.length) (capacity : rows.length ≤ 64)
    (generationRoom : s (.base .generation) ≠ 65535#16)
    (transferRoom : s (.base .transfer) ≠ 65535#16) :
    HandoffResult trace registered rows idle requestedCount s := by
  obtain ⟨settled, generation, transfer⟩ := delivery.settlement.closes registered
  let freed : Values (Register a) := trace.atSettlement registered s
  let beforeStale : Values (Register a) := trace.atStale registered s
  let beforeStart : Values (Register a) := trace.atStart registered s
  have room : freed (.base .generation) ≠ 65535#16 := by
    change freed (.base .generation) = s (.base .generation) at generation
    rwa [generation]
  have loaded := install registered freed rows idle trace.writes positive capacity delivery.writes
    (Free.ofFence settled) trace.commit delivery.commit room
  have installed : InstalledCut registered rows idle freed beforeStale := by
    change InstalledCut registered rows idle freed
      (SegmentTiming.run registered freed ((trace.writes ++ [@trace.commit]) ++ trace.replyClocks))
    rw [SegmentTiming.run_append]
    exact loaded.idle_run _ delivery.reply
  obtain ⟨_, staleInput⟩ := delivery.stale
  have older : trace.stale .expectedGeneration ≠ freed (.base .generation) + 1 := by
    change freed (.base .generation) = s (.base .generation) at generation
    rw [staleInput.expected, generation]
    intro equal
    have different : (0#16 : BitVec 16) ≠ 1#16 := by decide
    exact different ((BitVec.add_right_inj (s (.base .generation))).mp
      ((BitVec.add_zero _).trans equal))
  obtain ⟨rejected, preserved⟩ :=
    installed.reject_stale trace.stale staleInput.cold staleInput.command older
  have ready : InstalledCut registered rows idle freed beforeStart :=
    preserved.idle_run _ delivery.retry
  change freed (.base .generation) = s (.base .generation) at generation
  change freed (.base .transfer) = s (.base .transfer) at transfer
  have remainingTransfers : freed (.base .transfer) ≠ 65535#16 := by rwa [transfer]
  have freshInput : Start (freed (.base .generation) + 1) requestedCount trace.start := by
    rw [generation]
    exact delivery.start
  have fresh := start_installed registered freed beforeStart ready trace.start remainingTransfers freshInput
  exact ⟨settled, rejected, ready, ⟨fresh.entry, fresh.generation.trans (congrArg (· + 1) generation),
    fresh.transfer.trans (congrArg (· + 1) transfer), fresh.total, fresh.remaining,
    fresh.empty, fresh.levels, fresh.enabled⟩⟩

/-- The bounded segment checker supplies the geometry premises for a
handoff into a checked image. The row-level theorem also serves fixed
protocols whose listening guards have no finite wait limit. -/
theorem handoff_checked (image : Image rows budget) (trace : HandoffTrace) (registered : Bool)
    (s : Values (Register a)) (delivery : HandoffDelivery trace rows idle requestedCount s)
    (generationRoom : s (.base .generation) ≠ 65535#16)
    (transferRoom : s (.base .transfer) ≠ 65535#16) :
    HandoffResult trace registered rows idle requestedCount s :=
  handoff trace registered s delivery (checked_bounds image).1 (checked_bounds image).2
    generationRoom transferRoom

end Pinwheel.Hardware.StreamingReady.SegmentReload
