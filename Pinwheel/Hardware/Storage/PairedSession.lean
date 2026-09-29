import Pinwheel.Hardware.Storage.PairedAdmission

/-! Progress from delivered certified words to an accepted paired commit,
including arbitrary quiet gaps and the actual package transport. -/
namespace Pinwheel.Hardware.Storage.PairedSession
open Pinwheel.Hardware PairedController PairedUpload PairedRunning PairedControl
open PairedCoverage (Tracked graphInputs advance graph_equations)
open Pinwheel.Hardware.Loader.Machine (Quiet Carries Delivers)
set_option backward.isDefEq.respectTransparency false

abbrev CommandInput := Pinwheel.Hardware.Loader.Machine.Inputs

def run (s : Tracked) (history : List CommandInput) : Tracked :=
  history.foldl (fun t i => advance t i.values) s

def Stopped (s : Tracked) : Prop := PairedRuntime.Invariant s ∧ ¬Running s.registers

structure Staging (words : List (BitVec 64)) (s : Tracked) : Prop where
  stopped : Stopped s
  pending : (control s.registers).pending = true
  cursor : (control s.registers).cursor.toNat = words.length
  transcript : s.ledger.staged = words

theorem stopped_inputs (s : Tracked) (i : CommandInput) (hs : ¬Running s.registers)
    (hi : i.init = false) (hr : i.reset = false) (hc : i.command ≠ 7) :
    inputs (graphInputs i.values s) s.registers = ⟨false, false, false, i.command, i.data⟩ := by
  have hb : busy.eval (graphInputs i.values s) s.registers = 0 :=
    PairedControl.bool_value _ false (by simpa [hs] using busy_iff _ _ (graph_equations i.values s))
  simp only [PairedUpload.inputs, init_value _ _ (graph_equations i.values s), PairedEdges.reset_wire _ _ (graph_equations i.values s),
    resetExpr, cmd, either, Expr.eval, hb, data_value _ _ (graph_equations i.values s)]
  simp_all [graphInputs, PairedSemantics.inputs, PairedSemantics.graphValues, PairedClosed.feedback,
    Loader.Machine.Inputs.values]
  done

theorem stopped_next (s : Tracked) (i : CommandInput) (hs : Stopped s) (hc : i.command ≠ 5) :
    Stopped (advance s i.values) := by
  refine ⟨PairedRuntime.invariant_next s i.values hs.1, ?_⟩
  have hb : busy.eval (graphInputs i.values s) s.registers = 0 :=
    PairedControl.bool_value _ false (by simpa [hs.2] using busy_iff _ _ (graph_equations i.values s))
  have he : enteringRun.eval (graphInputs i.values s) s.registers = 0 := by
    simp only [enteringRun_wire _ _ (graph_equations i.values s), enteringRunExpr,
      entering_wire _ _ (graph_equations i.values s), enteringExpr,
      start_wire _ _ (graph_equations i.values s), startExpr,
      dispatch_wire _ _ (graph_equations i.values s), dispatchExpr, both, either, cmd, Expr.eval,
      hb, show graphInputs i.values s (.base .command) = i.command from rfl,
      hc, decide_false, BitVec.ofBool_false]
    bv_normalize
    done
  exact fun hn => (running_cases _ _ (graph_equations i.values s) hn).2.2.2.elim
    (fun h => by simp [he] at h) (fun h => hs.2 h.2)
  done

theorem staging_begin (s : Tracked) (i : CommandInput) (d : BitVec 64)
    (hs : Stopped s) (hc : Carries i 1 d) : Staging [] (advance s i.values) := by
  have hi := Loader.Machine.carries_plain hc (by decide)
  have he := stopped_inputs s i hs.2 hi.1 hi.2.1 (by simp only [hi.2.2.1]; decide)
  refine ⟨stopped_next s i hs (by simp only [hi.2.2.1]; decide), ?_, ?_, ?_⟩
  all_goals simp [advance, control_next _ _ (graph_equations i.values s), he,
    PairedLoader.next, PairedLoader.record, hi.2.2.1]
  all_goals done

theorem staging_quiet (words : List (BitVec 64)) (s : Tracked) (i : CommandInput)
    (hs : Staging words s) (hq : Quiet i) : Staging words (advance s i.values) := by
  have he := stopped_inputs s i hs.stopped.2 hq.1 hq.2.1 (by simp only [hq.2.2]; decide)
  refine ⟨stopped_next s i hs.stopped (by simp only [hq.2.2]; decide), ?_, ?_, ?_⟩
  all_goals simp [advance, control_next _ _ (graph_equations i.values s), he,
    PairedLoader.next, PairedLoader.record, PairedLoader.push, PairedLoader.commit,
    hq.2.2, hs.pending, hs.cursor, hs.transcript]
  all_goals done

theorem staged_parameters (image : PairedImage.Image) (s : Tracked)
    (words rest : List (BitVec 64)) (hs : Staging words s)
    (hw : PairedImage.upload image = words ++ rest) (hk : 32 ≤ (s.registers .cursor).toNat) :
    ∀ k, s.registers (.parameter (!(s.registers .active == 1)) k) = image.parameters[k.toNat] := by
  intro k
  have owned := (hs.stopped.1.1.staged hs.pending).2 (PairedLoader.Slot.parameter k)
    (by have := k.isLt; change k.toNat < (s.registers .cursor).toNat; omega)
  have hlt : k.toNat < words.length := by
    have hc : (s.registers .cursor).toNat = words.length := hs.cursor
    have := k.isLt
    omega
  have he : words.getD k.toNat 0 = (PairedImage.upload image).getD k.toNat 0 := by
    simp [hw, List.getElem?_append, hlt]
  simpa only [banks, PairedUpload.control, hs.transcript, PairedLoader.offset, he,
    PairedAdmission.upload_parameter, BitVec.extractLsb'_setWidth_of_le (by decide : 0 + 20 ≤ 64),
    BitVec.extractLsb'_eq_self] using owned
  done

theorem push_accepted (p : Execution.Image) (image : PairedImage.Image)
    (cert : PairedImage.Corresponds p image) (s : Tracked) (i : CommandInput)
    (words : List (BitVec 64)) (word : BitVec 64) (rest : List (BitVec 64))
    (hs : Staging words s) (hw : PairedImage.upload image = words ++ word :: rest)
    (hc : Carries i 2 word) :
    PairedLoader.push (inputs (graphInputs i.values s) s.registers)
      (admitted (graphInputs i.values s) s.registers) (control s.registers) = true := by
  have hi := Loader.Machine.carries_plain hc (by decide)
  have he := stopped_inputs s i hs.stopped.2 hi.1 hi.2.1 (by simp only [hi.2.2.1]; decide)
  have hlen : words.length < 290 := by
    have h := congrArg List.length hw
    simp only [PairedImage.upload_length, List.length_append, List.length_cons] at h
    omega
  have hcur : (s.registers .cursor).toNat = words.length := hs.cursor
  have hg := PairedAdmission.word_good p image cert _ s.registers (graph_equations i.values s)
    (by simp [accepting_value _ _ (graph_equations i.values s), he, Loader.enabled])
    hi.2.2.1 (by simpa only [PairedUpload.control, beq_iff_eq] using hs.pending)
    (by omega) (by simpa [data_value _ _ (graph_equations i.values s), show graphInputs i.values s (.base .data) = i.data from rfl, hcur, hw] using hi.2.2.2)
    (staged_parameters image s words (word :: rest) hs hw)
  simp [PairedLoader.push, he, admitted, hg, Loader.enabled, hi.2.2.1,
    hs.pending, hs.cursor, hlen]
  done

theorem staging_push (s : Tracked) (i : CommandInput) (words : List (BitVec 64))
    (hs : Staging words s)
    (hp : PairedLoader.push (inputs (graphInputs i.values s) s.registers)
      (admitted (graphInputs i.values s) s.registers) (control s.registers) = true) :
    Staging (words ++ [i.data]) (advance s i.values) := by
  obtain ⟨hi, hr, hb, hc, _, hbound, _⟩ := PairedLoader.push_requires _ _ _ hp
  have hlen : words.length < 290 := by simpa only [hs.cursor] using hbound
  refine ⟨stopped_next s i hs.stopped (by change i.command = 2 at hc; simp only [hc]; decide), ?_, ?_, ?_⟩
  all_goals simp [advance, control_next _ _ (graph_equations i.values s), PairedLoader.push_next _ _ _ hp,
    PairedLoader.record, PairedLoader.commit, hi, hr, hb, hc, hp, hs.pending, hs.cursor,
    hs.transcript, PairedCoverage.input_data, Loader.Machine.Inputs.values]
  omega
  done

theorem commit_accepted (image : PairedImage.Image) (s : Tracked) (i : CommandInput) (d : BitVec 64)
    (hs : Staging (PairedImage.upload image) s) (hc : Carries i 3 d) :
    PairedLifecycle.Accepted s i.values := by
  have hi := Loader.Machine.carries_plain hc (by decide)
  have he := stopped_inputs s i hs.stopped.2 hi.1 hi.2.1 (by simp only [hi.2.2.1]; decide)
  have hcur : (control s.registers).cursor = 290 := by
    have hl := hs.cursor
    simp only [PairedImage.upload_length] at hl
    bv_omega
  simp [PairedLifecycle.Accepted, commit_value _ _ (graph_equations i.values s),
    PairedLoader.commit, he, Loader.enabled, hi.2.2.1, hs.pending, hcur]
  done

theorem staging_commit (p : Execution.Image) (image : PairedImage.Image)
    (cert : PairedImage.Corresponds p image) (s : Tracked) (i : CommandInput) (d : BitVec 64)
    (hs : Staging (PairedImage.upload image) s) (hc : Carries i 3 d) :
    PairedTimed.Related p image (advance s i.values) (Engine.Reactive.reset p) := by
  exact PairedLifecycle.after_commit p image s i.values hs.stopped.1
    (commit_accepted image s i d hs hc) (by exact decide_eq_true ⟨hs.transcript, cert⟩)

theorem related_quiet (p : Execution.Image) (image : PairedImage.Image) (s : Tracked) (i : CommandInput)
    (hs : PairedTimed.Related p image s (Engine.Reactive.reset p)) (hq : Quiet i) :
    PairedTimed.Related p image (advance s i.values) (Engine.Reactive.reset p) := by
  have hnext := (PairedTimed.refinement p image).step i.values s (Engine.Reactive.reset p)
    (by simp [PairedCertified.Rule, Loader.Machine.Inputs.values, hq.1, hq.2.2]) hs
  simpa [PairedTimed.refinement, PairedTimed.tracked, PairedTimed.reference,
    PairedEdges.resetRequested, Loader.Machine.Inputs.values, hq.2.1, hq.2.2,
    Engine.Reactive.step, Engine.Reactive.reset, Engine.Reactive.stop, Engine.Reactive.busy] using hnext
  done

theorem quiet_run (p : Execution.Image) (image : PairedImage.Image) (history : List CommandInput)
    (s : Tracked) (hs : PairedTimed.Related p image s (Engine.Reactive.reset p))
    (hd : Delivers history []) : PairedTimed.Related p image (run s history) (Engine.Reactive.reset p) := by
  induction history generalizing s with
  | nil => exact hs
  | cons i rest ih =>
    cases hd with
    | quiet hq hd => exact ih _ (related_quiet p image s i hs hq) hd

theorem finish_upload (p : Execution.Image) (image : PairedImage.Image)
    (cert : PairedImage.Corresponds p image) (d : BitVec 64) (history : List CommandInput)
    (s : Tracked) (words rest : List (BitVec 64)) (hw : PairedImage.upload image = words ++ rest)
    (hs : Staging words s)
    (hd : Delivers history (rest.map (fun word => ((2 : BitVec 3), word)) ++ [(3, d)])) :
    PairedTimed.Related p image (run s history) (Engine.Reactive.reset p) := by
  induction history generalizing s words rest with
  | nil =>
    cases rest with
    | nil => simp only [List.map_nil, List.nil_append] at hd; cases hd
    | cons word rest => simp only [List.map_cons, List.cons_append] at hd; cases hd
  | cons i tail ih =>
    cases rest with
    | nil =>
      simp only [List.map_nil, List.nil_append, List.append_nil] at hd hw
      cases hd with
      | quiet hq hd =>
        exact ih (advance s i.values) words [] (by simpa using hw) (staging_quiet words s i hs hq)
          (by simpa using hd)
      | command hc hd =>
        exact quiet_run p image tail _ (staging_commit p image cert s i d (hw ▸ hs) hc) hd
    | cons word rest =>
      simp only [List.map_cons, List.cons_append] at hd
      cases hd with
      | quiet hq hd =>
        exact ih (advance s i.values) words (word :: rest) hw (staging_quiet words s i hs hq)
          (by simpa using hd)
      | command hc hd =>
        have hp := staging_push s i words hs (push_accepted p image cert s i words word rest hs hw hc)
        exact ih (advance s i.values) (words ++ [word]) rest (by simpa using hw)
          (by simpa only [hc.2.2.2] using hp) hd
        done

/-- Every correctly delivered certified image reaches accepted commit and
ready E64 state. There is no assumed admission decision or accepted ledger. -/
theorem upload_admitted (p : Execution.Image) (image : PairedImage.Image)
    (cert : PairedImage.Corresponds p image) (d₀ d₁ : BitVec 64)
    (history : List CommandInput) (s : Tracked) (hs : Stopped s)
    (hd : Delivers history (Loader.Machine.uploadCommands (PairedImage.upload image) d₀ d₁)) :
    PairedTimed.Related p image (run s history) (Engine.Reactive.reset p) := by
  induction history generalizing s with
  | nil => cases hd
  | cons i tail ih =>
    cases hd with
    | quiet hq hd =>
      exact ih _ (stopped_next s i hs (by simp only [hq.2.2]; decide)) hd
    | command hc hd =>
      exact finish_upload p image cert d₁ tail (advance s i.values) [] (PairedImage.upload image)
        rfl (staging_begin s i d₀ hs hc) hd

/-- Delivered certified upload, then every execution/result-observation edge
of the retained package. The mailbox and initial storage may be arbitrary. -/
theorem retained_upload_segment (p : Execution.Image) (image : PairedImage.Image)
    (cert : PairedImage.Corresponds p image)
    (n : Netlist Register (SramController.Out Loader.Machine.Output) Input) (hn : PairedValidation.core = .ok n)
    (memory : Memory.SinglePort.Contract S 9 64) (s : PairedPackage.State S) (storage : Tracked)
    (hview : PairedCoverage.view memory s.core = storage.physical) (hs : Stopped storage)
    (d₀ d₁ : BitVec 64) (uploadPins : List Chip.Pins)
    (hd : Delivers (Chip.consumed s.adapters uploadPins)
      (Loader.Machine.uploadCommands (PairedImage.upload image) d₀ d₁)) (pins : List Chip.Pins)
    (hi : ∀ i ∈ Chip.consumed ((PairedPackage.interpreted memory).run s uploadPins).adapters pins,
      PairedCertified.Rule i.values) :
    (PairedPackage.executable (PairedComposition.package n).component memory).trace
        ((PairedPackage.executable (PairedComposition.package n).component memory).run s.physical uploadPins) pins =
      (PairedHost.reference p).trace
        ⟨run storage (Chip.consumed s.adapters uploadPins), Engine.Reactive.reset p,
          ((PairedPackage.interpreted memory).run s uploadPins).adapters,
          ((PairedPackage.interpreted memory).run s uploadPins).result⟩ pins := by
  rw [PairedPackage.retained_run n hn, PairedPackage.retained_trace n hn]
  exact PairedHost.interpreted_trace p image memory _ _
    ⟨PairedHost.run_storage memory s storage hview uploadPins,
      upload_admitted p image cert d₀ d₁ _ storage hs hd, rfl, rfl⟩ pins hi
  done

theorem reset_prepares (memory : Memory.SinglePort.Contract S 9 64) (s : PairedPackage.State S)
    (resetPin idlePin : Chip.Pins) (hr : resetPin.rstN = false)
    (hi : idlePin.rstN = true) (hc : idlePin.uiIn.getLsbD 2 = true) :
    let prepared := (PairedPackage.interpreted memory).run s [resetPin, resetPin, resetPin, idlePin, idlePin]
    ∃ storage : Tracked, PairedCoverage.view memory prepared.core = storage.physical ∧
      Stopped storage ∧ prepared.adapters.receiver.count = 0 ∧ prepared.adapters.receiver.fire = false ∧
      Serial.Idle prepared.adapters.first ∧ Serial.Idle prepared.adapters.second := by
  let initial : Tracked := ⟨s.core.1, memory.view s.core.2, {}⟩
  refine ⟨run initial (Chip.consumed s.adapters [resetPin, resetPin, resetPin, idlePin, idlePin]),
    PairedHost.run_storage memory s initial rfl _, ⟨?_, ?_⟩, ?_⟩
  case refine_1 =>
    apply PairedRuntime.invariant_initialize
    change BitVec.ofBool (!resetPin.rstN) = 1
    simp [hr]
    done
  case refine_2 =>
    apply not_running_initialize _ _ (graph_equations _ _)
    rw [init_value _ _ (graph_equations _ _)]
    change BitVec.ofBool (!resetPin.rstN) = 1
    simp [hr]
    done
  case refine_3 =>
    simp [Timed.Component.run, PairedPackage.interpreted, PairedPackage.adaptersNext,
      Serial.next, Serial.taking, Serial.Idle, Chip.wired, hr, hi, hc]
    done

/-- Arbitrary represented power-up state, sampled reset/release, a qualified
serial upload, then E64 execution through all package outputs. Delivery and the
source certificate imply acceptance; the SRAM behavior law stays explicit. -/
theorem retained_initialized_session (p : Execution.Image) (image : PairedImage.Image)
    (cert : PairedImage.Corresponds p image)
    (n : Netlist Register (SramController.Out Loader.Machine.Output) Input) (hn : PairedValidation.core = .ok n)
    (memory : Memory.SinglePort.Contract S 9 64) (initial : PairedPackage.State S)
    (resetPin idlePin : Chip.Pins) (hr : resetPin.rstN = false)
    (hi : idlePin.rstN = true) (hc : idlePin.uiIn.getLsbD 2 = true)
    (d₀ d₁ : BitVec 64) (uploadPins : List Chip.Pins) (a b : Chip.Pins)
    (hd : Serial.Session (uploadPins.map Chip.wired)
      (Loader.Machine.uploadCommands (PairedImage.upload image) d₀ d₁)) (pins : List Chip.Pins) :
    let prepared := (PairedPackage.interpreted memory).run initial
      [resetPin, resetPin, resetPin, idlePin, idlePin]
    let uploaded := (PairedPackage.interpreted memory).run prepared (uploadPins ++ [a, b])
    (∀ i ∈ Chip.consumed uploaded.adapters pins, PairedCertified.Rule i.values) →
    ∃ storage : Tracked, PairedTimed.Related p image storage (Engine.Reactive.reset p) ∧
      (PairedPackage.executable (PairedComposition.package n).component memory).trace
        ((PairedPackage.executable (PairedComposition.package n).component memory).run
          ((PairedPackage.executable (PairedComposition.package n).component memory).run initial.physical
            [resetPin, resetPin, resetPin, idlePin, idlePin]) (uploadPins ++ [a, b])) pins =
        (PairedHost.reference p).trace
          ⟨storage, Engine.Reactive.reset p, uploaded.adapters, uploaded.result⟩ pins := by
  dsimp only
  intro rule
  obtain ⟨storage, hview, hs, hcount, hfire, hfirst, hsecond⟩ :=
    reset_prepares memory initial resetPin idlePin hr hi hc
  have delivered := Chip.session_delivers _ hcount hfire hfirst hsecond uploadPins a b _ hd
  refine ⟨_, upload_admitted p image cert d₀ d₁ _ storage hs delivered, ?_⟩
  simpa only [PairedPackage.retained_run n hn] using
    retained_upload_segment p image cert n hn memory _ storage hview hs d₀ d₁
      (uploadPins ++ [a, b]) delivered pins rule
  done

end Pinwheel.Hardware.Storage.PairedSession
