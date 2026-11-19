import Pinwheel.Hardware.StreamingReady.EthernetBoot
import Pinwheel.Hardware.StreamingReady.InitializedCustody
import Pinwheel.Hardware.StreamingReady.PublicPins
import Pinwheel.Program.StreamingEthernetScheduleProof

/-! A complete minimum-frame transmit from sampled quad requests to the
serial PHY interface of the typed Ready package. -/
namespace Pinwheel.Hardware.StreamingReady.EthernetSession
open Pinwheel.Program.StreamingReady Pinwheel.Program.StreamingEthernetCore
open Pinwheel.Program.StreamingEthernetFrame Pinwheel.Program.StreamingEthernetSchedule
open Pinwheel.Hardware.StreamingReady.InitializedCustody

set_option maxHeartbeats 5000000

theorem standard_words : (image.words, idlePins) =
    ([11258999081009156, 5629499546796036, 1125899919425540, 5629499546796036,
      4617315536027516929, 2], ⟨0, 3⟩) := by
  decide +kernel

def afterBoot (startup : Package.State 1) : Package.State 1 :=
  startup.run (Package.Components.typed 1)
    (SessionCorrespondence.pins BootPins.coldPin :: bootPins.map SessionCorrespondence.pins)

def beforeWire (startup : Package.State 1) : Package.State 1 :=
  let initial := (afterBoot startup).run (Package.Components.typed 1)
    (beforeStart.map SessionCorrespondence.pins)
  let active := initial.step (Package.Components.typed 1) (SessionCorrespondence.pins startPin)
  active.run (Package.Components.typed 1) (afterStart.map SessionCorrespondence.pins)

def phyPinTrace (startup : Package.State 1) (width : Nat) : List Pins :=
  PublicPins.driveTrace (beforeWire startup) (bodyPins width ++ releaseClocked width)

private theorem runtime_append (s : Session.State 1) (left right : List Session.Pins)
    (first : Session.RuntimeTrace program false s left)
    (last : Session.RuntimeTrace program false (s.run program false left) right) :
    Session.RuntimeTrace program false s (left ++ right) := by
  induction left generalizing s with
  | nil => exact last
  | cons pin rest ih => exact ⟨first.1, ih _ first.2 last⟩

private theorem source_pin_at (s : State 1) (inputs : List Input) (k : Nat) (inside : k ≤ inputs.length) :
    (pinTrace program s inputs)[k]? = some (run program s (inputs.take k)).pins := by
  induction inputs generalizing s k with
  | nil =>
    have zero : k = 0 := by simpa using inside
    subst k
    rfl
  | cons i rest ih =>
    cases k with
    | zero => rfl
    | succ k => exact ih (step program i s) k (by simpa using inside)

private theorem input_prefix (s : Session.State 1) (pins : List Session.Pins) (k : Nat) :
    (s.runtimeInputs program false pins).take k = s.runtimeInputs program false (pins.take k) := by
  induction pins generalizing s k with
  | nil => cases k <;> rfl
  | cons pin rest ih =>
    cases k with
    | zero => rfl
    | succ k => simp only [Session.State.runtimeInputs, List.take_succ_cons, ih]

theorem beforeWire_matches (startup : Package.State 1) :
    Reached image (beforeWire startup) preloaded (started.traceRun program false {} afterStart) := by
  let actualBoot := afterBoot startup
  have init : BootCorrespondence.Initialized image actualBoot seed := EthernetBoot.initialized startup
  have entered := started_and_preloaded
  let actualReady := actualBoot.run (Package.Components.typed 1) (beforeStart.map SessionCorrespondence.pins)
  have readyEq : actualReady = SessionCorrespondence.values (Initialization.compiledImage image) ready :=
    initialized_run_eq image actualBoot seed init beforeStart (by decide) entered.before
  have accepted : ActualStart actualReady startPin := by
    rw [readyEq]
    unfold ActualStart
    rw [SessionCorrespondence.core_inputs]
    change Core.starting.eval (Pinwheel.Hardware.Streaming.HostCorrespondence.commandValues (ready.command startPin))
      (SourceRefinement.values (Initialization.compiledImage image) ready.core) = 1
    rw [InputCorrespondence.command_eval _ InputCorrespondence.starting_runtime,
      SourceRefinement.starting_eval _ _ _ entered.startRuntime]
    simp [entered.command, entered.admitted]
  exact started_run image actualBoot seed init beforeStart startPin afterStart (by decide)
    entered.before entered.startRuntime accepted entered.after

private theorem trace_at (startup : Package.State 1) (width k : Nat)
    (ok : Executed width) (inside : k ≤ (bodyPins width ++ releaseClocked width).length) :
    (phyPinTrace startup width)[k]? =
      some (preloaded.run program false ((bodyPins width ++ releaseClocked width).take k)).core.pins := by
  let all := bodyPins width ++ releaseClocked width
  let commands := preloaded.runtimeInputs program false all
  have reached := beforeWire_matches startup
  have ordinary := runtime_append preloaded (bodyPins width) (releaseClocked width) ok.body_runtime ok.release_runtime
  have driven : phyPinTrace startup width = pinTrace program preloaded.core commands := by
    unfold phyPinTrace
    rw [reached.package]
    simpa only [compiled_pending] using PublicPins.driveTrace_eq (Initialization.compiledImage image)
      preloaded all (by decide) (by simpa only [compiled_pending] using ordinary) reached.custody.structural
  rw [driven]
  have commandCount : commands.length = all.length := by
    have raw := congrArg List.length (preloaded.runtime_rawInputs program false all)
    simpa only [commands, List.length_map] using raw
  rw [source_pin_at _ _ k (by rwa [commandCount])]
  change some (run program preloaded.core ((preloaded.runtimeInputs program false all).take k)).pins = _
  rw [input_prefix, ← preloaded.run_core]

private theorem body_pad_at (startup : Package.State 1) (width k : Nat)
    (ok : Executed width) (inside : k ≤ wireLength) :
    ((phyPinTrace startup width)[k]?).getD {} = (wireAt width k).core.pins := by
  have body : k ≤ (bodyPins width).length := by rwa [body_length]
  have bound : k ≤ (bodyPins width ++ releaseClocked width).length := by
    simp only [List.length_append]
    omega
  rw [trace_at startup width k ok bound, Option.getD_some, List.take_append_of_le_length body]
  rfl

theorem phy_sample (startup : Package.State 1) (width : Nat) (legal : width = 1 ∨ width = 2)
    (k : Nat) (inside : k < 576) :
    let pads := ((phyPinTrace startup width)[firstSample + 6 * k]?).getD {}
    pads.enabled = 3 ∧ pads.levels[1] = true ∧ pads.levels[0] = frameBits[k]?.getD false := by
  have ok := executed legal
  have bound : firstSample + 6 * k ≤ wireLength := by unfold firstSample wireLength; omega
  dsimp only
  rw [body_pad_at startup width _ ok bound]
  exact ok.phy_sample k inside

/-- The bit is already driven at the pre-edge cut after reservation. -/
theorem setup_sample (startup : Package.State 1) (width : Nat) (legal : width = 1 ∨ width = 2)
    (k : Nat) (inside : k < 576) :
    let pads := ((phyPinTrace startup width)[firstSample + 6 * k - 1]?).getD {}
    pads.enabled = 3 ∧ pads.levels[1] = true ∧ pads.levels[0] = frameBits[k]?.getD false := by
  have ok := executed legal
  have bound : firstSample + 6 * k - 1 ≤ wireLength := by unfold firstSample wireLength; omega
  dsimp only
  rw [body_pad_at startup width _ ok bound]
  exact ok.setup_sample k inside

theorem tx_enable (startup : Package.State 1) (width : Nat) (legal : width = 1 ∨ width = 2)
    (cut : Nat) (inside : cut < wireLength) :
    let pads := ((phyPinTrace startup width)[cut]?).getD {}
    pads.enabled = 3 ∧ pads.levels[1] = decide (firstSample - 2 ≤ cut ∧ cut < wireLength) := by
  have ok := executed legal
  dsimp only
  rw [body_pad_at startup width cut ok (Nat.le_of_lt inside)]
  exact ok.enable_at cut inside

theorem next_phy_idle (startup : Package.State 1) (width : Nat) (legal : width = 1 ∨ width = 2) :
    let pads := ((phyPinTrace startup width)[wireLength + 1]?).getD {}
    pads.enabled = 3 ∧ pads.levels[1] = false := by
  have ok := executed legal
  have bound : wireLength + 1 ≤ (bodyPins width ++ releaseClocked width).length := by
    simp only [List.length_append, body_length, release_length]
    omega
  have split : (bodyPins width ++ releaseClocked width).take (wireLength + 1) =
      bodyPins width ++ (releaseClocked width).take 1 := by
    rw [List.take_append, List.take_of_length_le (by rw [body_length]; omega), body_length]
    rw [show wireLength + 1 - wireLength = 1 by omega]
  dsimp only
  rw [trace_at startup width _ ok bound, Option.getD_some, split]
  rw [show preloaded.run program false (bodyPins width ++ (releaseClocked width).take 1) =
      (wireComplete width).run program false ((releaseClocked width).take 1) from List.foldl_append]
  exact ok.next_phy_idle

theorem owner_released (startup : Package.State 1) (width : Nat) (legal : width = 1 ∨ width = 2) :
    let wireEnd := (beforeWire startup).run (Package.Components.typed 1) ((bodyPins width).map SessionCorrespondence.pins)
    let final := wireEnd.run (Package.Components.typed 1) ((releaseClocked width).map SessionCorrespondence.pins)
    wireEnd = SessionCorrespondence.values (Initialization.compiledImage image) (wireComplete width) ∧
    final = SessionCorrespondence.values (Initialization.compiledImage image) (released width) ∧
    (wireComplete width).core.phase = .completed ∧ (wireComplete width).core.drained = true ∧
    (wireComplete width).core.txAccepted = 576 ∧ (wireComplete width).core.txConsumed = 576 ∧
    (released width).core.phase = .free ∧ (released width).core.transfer = 1 ∧ (released width).host.code = 0 := by
  intro wireEnd final
  have ok := executed legal
  have reached := (beforeWire_matches startup).run (bodyPins width) (by decide) ok.body_runtime
  have done := reached.run (releaseClocked width) (by decide) ok.release_runtime
  exact ⟨reached.package, done.package, ok.completed, ok.drained, ok.accepted, ok.consumed,
    ok.free, ok.transfer, ok.releasedCode⟩

end Pinwheel.Hardware.StreamingReady.EthernetSession
