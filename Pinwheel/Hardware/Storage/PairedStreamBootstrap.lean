import Pinwheel.Hardware.Storage.PairedStreamPackage
import Pinwheel.Hardware.Storage.PairedStreamOwnership

/-! Actual sampled reset and certified serial upload for the stream package.
The delivery contract determines the accepted transcript; memory Q is supplied
only by the lawful implementation and the accepted-write coverage invariant. -/
namespace Pinwheel.Hardware.Storage.PairedStreamBootstrap
open Pinwheel.Hardware
set_option backward.isDefEq.respectTransparency false
abbrev State := PairedStreamPackage.State
abbrev Tracked := PairedStreamOwnership.Tracked

def run (storage : Tracked) (history : List Loader.Machine.Inputs) : Tracked :=
  history.foldl PairedStreamOwnership.advance storage

def Related (memory : Memory.SinglePort.Contract S 9 64) (s : State S) (storage : Tracked) : Prop :=
  PairedCoverage.view memory s.core = storage.inner.physical ∧ s.enabled = storage.enabled

theorem adapters_cons (x : Chip.State) (pins : Chip.Pins) (history : List Chip.Pins) :
    Chip.advance x (pins :: history) = Chip.advance (PairedPackage.adaptersNext pins x) history := by
  rfl

theorem adapters_run (memory : Memory.SinglePort.Contract S 9 64)
    (s : State S) (history : List Chip.Pins) :
    ((PairedStreamPackage.interpreted memory).run s history).adapters = Chip.advance s.adapters history := by
  induction history generalizing s with
  | nil => rfl
  | cons pins rest ih =>
    simpa only [Timed.Component.run, adapters_cons, PairedStreamPackage.interpreted]
      using ih ((PairedStreamPackage.interpreted memory).step pins s)
  done

theorem adapters_drained (x : Chip.State) (pins : List Chip.Pins) (a b : Chip.Pins) :
    Chip.advance x (pins ++ [a, b]) =
      ⟨Chip.wired b, Chip.wired a,
        Serial.run x.receiver (x.second :: x.first :: pins.map Chip.wired)⟩ := by
  induction pins generalizing x with
  | nil => rfl
  | cons i rest ih =>
    simpa only [List.cons_append, adapters_cons, PairedPackage.adaptersNext,
      List.map_cons, Serial.run] using ih (PairedPackage.adaptersNext i x)
  done

theorem settled_session (memory : Memory.SinglePort.Contract S 9 64) (s : State S)
    (count : s.adapters.receiver.count = 0) (fire : s.adapters.receiver.fire = false)
    (first : Serial.Idle s.adapters.first) (second : Serial.Idle s.adapters.second)
    (pins : List Chip.Pins) (a b : Chip.Pins) (ha : Serial.Idle (Chip.wired a))
    (hb : Serial.Idle (Chip.wired b)) (commands : List (BitVec 3 × BitVec 64))
    (session : Serial.Session (pins.map Chip.wired) commands) :
    let after := (PairedStreamPackage.interpreted memory).run s (pins ++ [a, b])
    after.adapters.receiver.count = 0 ∧ after.adapters.receiver.fire = false ∧
      Serial.Idle after.adapters.first ∧ Serial.Idle after.adapters.second := by
  have ready := (Serial.session_delivers (.idle second (.idle first session))
    s.adapters.receiver count fire).2
  simpa only [adapters_run, adapters_drained] using ⟨ready.1, ready.2, hb, ha⟩
  done

theorem policy_agrees (memory : Memory.SinglePort.Contract S 9 64)
    (s : State S) (storage : Tracked) (h : Related memory s storage) :
    PairedStreamPackage.policy s =
      PairedStreamOwnership.policy storage (PairedStreamPackage.rawInput s) := by
  have registers := congrArg Prod.fst h.1
  simp only [PairedCoverage.view, PairedCoverage.Tracked.physical] at registers
  simp only [PairedStreamPackage.policy, PairedStreamOwnership.policy,
    PairedStreamOwnership.status, registers, h.2]
  done

theorem related_next (memory : Memory.SinglePort.Contract S 9 64)
    (s : State S) (storage : Tracked) (h : Related memory s storage) (pins : Chip.Pins) :
    Related memory ((PairedStreamPackage.interpreted memory).step pins s)
      (PairedStreamOwnership.advance storage (PairedStreamPackage.rawInput s)) := by
  refine ⟨?_, ?_⟩
  case refine_1 =>
    simpa only [PairedStreamPackage.interpreted, PairedStreamOwnership.advance,
      PairedStreamPackage.effective, PairedStreamOwnership.effective, policy_agrees memory s storage h,
      PairedTimed.physical_refinement, PairedTimed.executable, PairedTimed.tracked]
      using (PairedTimed.physical_refinement memory).step
        (PairedStreamOwnership.effective storage (PairedStreamPackage.rawInput s)).values s.core storage.inner h.1
  case refine_2 =>
    exact congrArg (fun p : PairedStream.Transition => p.state.enabled) (policy_agrees memory s storage h)
  done

theorem run_storage (memory : Memory.SinglePort.Contract S 9 64)
    (s : State S) (storage : Tracked) (h : Related memory s storage) (pins : List Chip.Pins) :
    Related memory ((PairedStreamPackage.interpreted memory).run s pins)
      (run storage (Chip.consumed s.adapters pins)) := by
  induction pins generalizing s storage with
  | nil => exact h
  | cons i rest ih =>
    simpa only [Timed.Component.run, PairedHost.consumed_cons, run, List.foldl_cons,
      PairedStreamPackage.rawInput, PairedStreamPackage.interpreted]
      using ih ((PairedStreamPackage.interpreted memory).step i s)
        (PairedStreamOwnership.advance storage (PairedStreamPackage.rawInput s))
        (related_next memory s storage h i)
  done

theorem reset_prepares (memory : Memory.SinglePort.Contract S 9 64) (s : State S)
    (resetPin idlePin : Chip.Pins) (hr : resetPin.rstN = false)
    (hi : idlePin.rstN = true) (hc : idlePin.uiIn.getLsbD 2 = true) :
    let prepared := (PairedStreamPackage.interpreted memory).run s
      [resetPin, resetPin, resetPin, idlePin, idlePin]
    ∃ storage : Tracked, Related memory prepared storage ∧
      PairedSession.Stopped storage.inner ∧ storage.enabled = false ∧
      prepared.adapters.receiver.count = 0 ∧ prepared.adapters.receiver.fire = false ∧
      Serial.Idle prepared.adapters.first ∧ Serial.Idle prepared.adapters.second := by
  let initial : Tracked := ⟨⟨s.core.1, memory.view s.core.2, {}⟩, s.enabled⟩
  refine ⟨run initial (Chip.consumed s.adapters [resetPin, resetPin, resetPin, idlePin, idlePin]),
    run_storage memory s initial ⟨rfl, rfl⟩ _, ⟨?_, ?_⟩, ?_, ?_⟩
  case refine_1 =>
    apply PairedStreamOwnership.invariant_initialize
    change (!resetPin.rstN : Bool) = true
    simp [hr]
    done
  case refine_2 =>
    apply PairedRunning.not_running_initialize _ _ (PairedCoverage.graph_equations _ _)
    rw [PairedUpload.init_value _ _ (PairedCoverage.graph_equations _ _)]
    change BitVec.ofBool (!resetPin.rstN) = 1
    simp [hr]
  case refine_4 =>
    simp [Timed.Component.run, PairedStreamPackage.interpreted, PairedPackage.adaptersNext,
      Serial.next, Serial.taking, Serial.Idle, Chip.wired, hr, hi, hc]
    done
  case refine_3 =>
    apply PairedStreamOwnership.initialize_disables
    change (!resetPin.rstN : Bool) = true
    simp [hr]
    done
  done

/-- Reset and the qualified delivered transcript establish a certified resident
image from arbitrary represented power-up state. COMMIT acceptance is derived. -/
theorem initialized_upload (p : Execution.Image) (image : PairedImage.Image)
    (cert : PairedImage.Corresponds p image)
    (memory : Memory.SinglePort.Contract S 9 64) (initial : State S)
    (resetPin idlePin : Chip.Pins) (hr : resetPin.rstN = false)
    (hi : idlePin.rstN = true) (hc : idlePin.uiIn.getLsbD 2 = true)
    (d₀ d₁ : BitVec 64) (uploadPins : List Chip.Pins) (a b : Chip.Pins)
    (hd : Serial.Session (uploadPins.map Chip.wired)
      (Loader.Machine.uploadCommands (PairedImage.upload image) d₀ d₁)) :
    let prepared := (PairedStreamPackage.interpreted memory).run initial
      [resetPin, resetPin, resetPin, idlePin, idlePin]
    let uploaded := (PairedStreamPackage.interpreted memory).run prepared (uploadPins ++ [a, b])
    ∃ storage : Tracked, Related memory uploaded storage ∧
      PairedTimed.Related p image storage.inner (Engine.Reactive.reset p) ∧ storage.enabled = false := by
  dsimp only
  obtain ⟨storage, hs, stopped, disabled, count, fire, first, second⟩ :=
    reset_prepares memory initial resetPin idlePin hr hi hc
  have delivered := Chip.session_delivers _ count fire first second uploadPins a b _ hd
  exact ⟨_, run_storage memory _ storage hs _,
    PairedStreamOwnership.upload_admitted p image cert d₀ d₁ _ storage stopped disabled delivered⟩
  done

/-- The same accepted-write proof applies at a stopped reload boundary. The
physical result observer follows its actual controls throughout the upload. -/
theorem qualified_upload (p : Execution.Image) (image : PairedImage.Image)
    (cert : PairedImage.Corresponds p image) (memory : Memory.SinglePort.Contract S 9 64)
    (s : State S) (storage : Tracked) (h : Related memory s storage)
    (stopped : PairedSession.Stopped storage.inner) (disabled : storage.enabled = false)
    (count : s.adapters.receiver.count = 0) (fire : s.adapters.receiver.fire = false)
    (first : Serial.Idle s.adapters.first) (second : Serial.Idle s.adapters.second)
    (d₀ d₁ : BitVec 64) (pins : List Chip.Pins) (a b : Chip.Pins)
    (session : Serial.Session (pins.map Chip.wired)
      (Loader.Machine.uploadCommands (PairedImage.upload image) d₀ d₁)) :
    let after := (PairedStreamPackage.interpreted memory).run s (pins ++ [a, b])
    ∃ next : Tracked, Related memory after next ∧
      PairedTimed.Related p image next.inner (Engine.Reactive.reset p) ∧ next.enabled = false := by
  have delivered := Chip.session_delivers _ count fire first second pins a b _ session
  exact ⟨_, run_storage memory s storage h _,
    PairedStreamOwnership.upload_admitted p image cert d₀ d₁ _ storage stopped disabled delivered⟩
  done

end Pinwheel.Hardware.Storage.PairedStreamBootstrap
