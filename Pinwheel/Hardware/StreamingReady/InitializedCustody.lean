import Pinwheel.Hardware.StreamingReady.BootCorrespondence
import Pinwheel.Program.StreamingReadyOwnerCut

/-! Concrete physical initialization, actual START admission and reached
runtime custody share one source session and one sampled package recurrence. -/
namespace Pinwheel.Hardware.StreamingReady.InitializedCustody
open Pinwheel.Hardware Pinwheel.Program.StreamingReady Initialization
open Pinwheel.Hardware.Streaming
set_option linter.unusedSimpArgs false

private theorem ofBool_eq_one (b : Bool) : BitVec.ofBool b = 1#1 ↔ b = true := by
  cases b <;> decide

theorem initialized_control (initialized : BootCorrespondence.Initialized image actual source) :
    source.host.ControlSafe := by
  constructor
  · intro _
    exact initialized.phase
  · intro two
    rw [initialized.phase] at two
    contradiction
  · intro one
    rw [initialized.phase] at one
    contradiction

theorem control_run (s : Session.State a) (p : Program) (pending : Bool) (pins : List Session.Pins)
    (safe : s.host.ControlSafe) : (s.run p pending pins).host.ControlSafe := by
  induction pins generalizing s with
  | nil => exact safe
  | cons pin rest ih => exact ih (s.step p pending pin) (s.host.controlSafe_step _ safe)

def ActualStart (actual : Package.State a) (pin : Session.Pins) : Prop :=
  Core.starting.eval (actual.coreInputs (Package.Components.typed a) (SessionCorrespondence.pins pin)) actual.core = 1

def ActualRelease (actual : Package.State a) (pin : Session.Pins) : Prop :=
  Core.releasing.eval (actual.coreInputs (Package.Components.typed a) (SessionCorrespondence.pins pin)) actual.core = 1

theorem start_source (image : SourceRefinement.Image p) (s : Session.State a) (pin : Session.Pins)
    (runtime : Session.RuntimeInput s pin)
    (start : ActualStart (SessionCorrespondence.values image s) pin) :
    ((s.command pin).runtime.command == 3 && s.core.canStart (s.command pin).runtime) = true := by
  unfold ActualStart at start
  rw [SessionCorrespondence.core_inputs] at start
  change Core.starting.eval (HostCorrespondence.commandValues (s.command pin))
    (SourceRefinement.values image s.core) = 1#1 at start
  rw [InputCorrespondence.command_eval _ InputCorrespondence.starting_runtime,
    SourceRefinement.starting_eval image s.core (s.command pin).runtime runtime] at start
  exact (ofBool_eq_one _).mp start

theorem release_source (image : SourceRefinement.Image p) (s : Session.State a) (pin : Session.Pins)
    (ha : a ≤ 3) (runtime : Session.RuntimeInput s pin)
    (release : ActualRelease (SessionCorrespondence.values image s) pin) :
    (s.command pin).runtime.command = 4#4 ∧ s.core.canRelease (s.command pin).runtime = true := by
  unfold ActualRelease at release
  rw [SessionCorrespondence.core_inputs] at release
  change Core.releasing.eval (HostCorrespondence.commandValues (s.command pin))
    (SourceRefinement.values image s.core) = 1#1 at release
  rw [InputCorrespondence.command_eval _ InputCorrespondence.releasing_runtime,
    SourceRefinement.releasing_eval image s.core (s.command pin).runtime ha runtime] at release
  have accepted := (ofBool_eq_one _).mp release
  simpa only [Bool.and_eq_true,beq_iff_eq,BitVec.ofNat_eq_ofNat] using accepted

structure Reached (image : Compiled source idle) (actual : Package.State a)
    (s : Session.State a) (trace : BitTrace) : Prop where
  package : actual = SessionCorrespondence.values (compiledImage image) s
  custody : s.Custody trace
  freeExport : s.FreeExport

theorem Reached.receipt_valid (reached : Reached image actual s trace) :
    s.host.receipt.Valid s.core.rxProduced.toNat s.core.rxPopped.toNat :=
  reached.custody.receipt_valid s trace

theorem Reached.release_all_bits {a : Nat} {actual : Package.State a} {s : Session.State a}
    (reached : Reached image actual s trace)
    (pin : Session.Pins) (ha : a ≤ 3) (runtime : Session.RuntimeInput s pin)
    (release : ActualRelease actual pin) :
    trace.accepted = trace.consumed ∧ trace.captured = trace.exported ∧
      trace.exported.length = s.host.ackOffset.toNat ∧ s.host.exportBits.toNat = 0 := by
  rw [reached.package] at release
  have accepted := release_source (compiledImage image) s pin ha runtime release
  exact reached.custody.release_all_bits s pin trace accepted.1 accepted.2

theorem Reached.unacknowledged_blocks_release (reached : Reached image actual s trace)
    (pin : Session.Pins) (unacknowledged : 0 < s.host.exportBits.toNat) :
    (s.command pin).runtime.command ≠ 4#4 :=
  reached.custody.unacknowledged_blocks_release s pin trace unacknowledged

theorem Reached.next_start_empty (reached : Reached image actual s trace)
    (pin : Session.Pins) (runtime : Session.RuntimeInput s pin) (start : ActualStart actual pin) :
    s.host.exportBits = 0#7 ∧ s.host.unacknowledged = false := by
  rw [reached.package] at start
  have admitted := start_source (compiledImage image) s pin runtime start
  simp only [Bool.and_eq_true] at admitted
  exact reached.freeExport.start_empty s pin reached.custody.interval admitted.2

theorem compiled_pending (image : Compiled source idle) : (compiledImage image).pending.getLsbD 0 = false := by
  change (0#1).getLsbD 0 = false
  decide +kernel

/-- The pre-START source state and its bounds are reached from concrete boot.
The START premise is the actual circuit admission flag, not source agreement. -/
theorem started_run (image : Compiled source idle) (actualBoot : Package.State a) (boot : Session.State a)
    (initialized : BootCorrespondence.Initialized image actualBoot boot)
    (before : List Session.Pins) (startPin : Session.Pins) (after : List Session.Pins)
    (ha : a ≤ 3) (beforeRuntime : Session.RuntimeTrace image.program false boot before)
    (startRuntime : Session.RuntimeInput (boot.run image.program false before) startPin)
    (start : ActualStart (actualBoot.run (Package.Components.typed a) (before.map SessionCorrespondence.pins)) startPin)
    (afterRuntime : Session.RuntimeTrace image.program false
      ((boot.run image.program false before).step image.program false startPin) after) :
    Reached image
      (((actualBoot.run (Package.Components.typed a) (before.map SessionCorrespondence.pins)).step (Package.Components.typed a)
        (SessionCorrespondence.pins startPin)).run (Package.Components.typed a) (after.map SessionCorrespondence.pins))
      (((boot.run image.program false before).step image.program false startPin).run image.program false after)
      (((boot.run image.program false before).step image.program false startPin).traceRun image.program false {} after) := by
  have control := control_run boot image.program false before (initialized_control initialized)
  have structural := boot.run_structural image.program false before initialized.structural
  have beforePackage : actualBoot.run (Package.Components.typed a) (before.map SessionCorrespondence.pins) =
      SessionCorrespondence.values (compiledImage image) (boot.run image.program false before) := by
    rw [initialized.package]
    simpa only [compiled_pending] using SessionCorrespondence.run_correct (compiledImage image) boot before
      ha (by simpa only [compiled_pending] using beforeRuntime) initialized.structural
  have admitted := start
  rw [beforePackage] at admitted
  have sourceStart := start_source (compiledImage image) _ startPin startRuntime admitted
  have custody := Session.State.Custody.started (boot.run image.program false before) image.program false
    startPin startRuntime control sourceStart
  have freeExport := Session.State.FreeExport.started (boot.run image.program false before) image.program false
    startPin startRuntime sourceStart
  constructor
  · rw [beforePackage]
    have first := SessionCorrespondence.step_correct (compiledImage image) (boot.run image.program false before)
      startPin ha startRuntime structural
    simp only [compiled_pending] at first
    rw [first]
    simpa only [compiled_pending] using SessionCorrespondence.run_correct (compiledImage image)
      ((boot.run image.program false before).step image.program false startPin) after ha
      (by simpa only [compiled_pending] using afterRuntime) custody.structural
  · exact custody.run _ image.program false after {} ha afterRuntime
  · exact freeExport.run _ image.program false after {} ha afterRuntime custody

/-- Every admissible physical prefix, one actual START edge and every following
runtime prefix have reached ownership, exact receipts and a safe reuse boundary. -/
def Pipeline (image : Compiled source idle) (actualBoot : Package.State a) (boot : Session.State a) : Prop :=
  ∀ (before : List Session.Pins) (startPin : Session.Pins) (after : List Session.Pins),
    a ≤ 3 →
    Session.RuntimeTrace image.program false boot before →
    Session.RuntimeInput (boot.run image.program false before) startPin →
    ActualStart (actualBoot.run (Package.Components.typed a) (before.map SessionCorrespondence.pins)) startPin →
    Session.RuntimeTrace image.program false
      ((boot.run image.program false before).step image.program false startPin) after →
    Reached image
      (((actualBoot.run (Package.Components.typed a) (before.map SessionCorrespondence.pins)).step (Package.Components.typed a)
        (SessionCorrespondence.pins startPin)).run (Package.Components.typed a) (after.map SessionCorrespondence.pins))
      (((boot.run image.program false before).step image.program false startPin).run image.program false after)
      (((boot.run image.program false before).step image.program false startPin).traceRun image.program false {} after)

theorem pipeline (initialized : BootCorrespondence.Initialized image actualBoot boot) :
    Pipeline image actualBoot boot :=
  fun before start after ha ordinary first accepted later =>
    started_run image actualBoot boot initialized before start after ha ordinary first accepted later

theorem compiled_session (image : Compiled source idle) (pins : List Session.Pins)
    (certificate : BootPins.Certified image.words idle BootPins.initialControl 0 false pins)
    (startup : Package.State a) :
    ∃ boot : Session.State a,
      BootCorrespondence.Initialized image
        (startup.run (Package.Components.typed a) (SessionCorrespondence.pins BootPins.coldPin :: pins.map SessionCorrespondence.pins)) boot ∧
      Pipeline image
        (startup.run (Package.Components.typed a) (SessionCorrespondence.pins BootPins.coldPin :: pins.map SessionCorrespondence.pins)) boot := by
  obtain ⟨boot,initialized⟩ := BootCorrespondence.compiled_initialized image pins certificate startup
  exact ⟨boot,initialized,pipeline initialized⟩

theorem i2c_session (startup : Package.State a) :
    ∃ boot : Session.State a,
      BootCorrespondence.Initialized (i2cImage .standard)
        (startup.run (Package.Components.typed a)
          (SessionCorrespondence.pins BootPins.coldPin :: BootPins.i2c.map SessionCorrespondence.pins)) boot ∧
      Pipeline (i2cImage .standard)
        (startup.run (Package.Components.typed a)
          (SessionCorrespondence.pins BootPins.coldPin :: BootPins.i2c.map SessionCorrespondence.pins)) boot :=
  compiled_session (i2cImage .standard) BootPins.i2c BootPins.i2c_certified startup

end Pinwheel.Hardware.StreamingReady.InitializedCustody
