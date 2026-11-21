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

theorem idle_control (s : Session.State a) (phase : s.host.phase = 0#3) :
    s.host.ControlSafe := by
  constructor
  · intro _
    exact phase
  · intro two
    rw [phase] at two
    contradiction
  · intro one
    rw [phase] at one
    contradiction

theorem initialized_control (initialized : BootCorrespondence.Initialized image actual source) :
    source.host.ControlSafe :=
  idle_control source initialized.phase

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

/-- The physical representation can retain older words beyond the installed
    program length. Runtime steps preserve that representation and custody. -/
structure Reached (image : Compiled source idle) (actual : Package.State a)
    (s : Session.State a) (trace : BitTrace)
    (rep : SourceRefinement.Image image.program := compiledImage image) : Prop where
  package : actual = SessionCorrespondence.values rep s
  custody : s.Custody trace
  freeExport : s.FreeExport
  installed : rep.pending = 0#1

variable {rows : List Instruction} {idle : Pins} {image : Compiled rows idle}
  {rep : SourceRefinement.Image image.program}

theorem Reached.receipt_valid (reached : Reached image actual s trace rep) :
    s.host.receipt.Valid s.core.rxProduced.toNat s.core.rxPopped.toNat :=
  reached.custody.receipt_valid s trace

theorem Reached.release_all_bits {a : Nat} {actual : Package.State a} {s : Session.State a}
    (reached : Reached image actual s trace rep)
    (pin : Session.Pins) (ha : a ≤ 3) (runtime : Session.RuntimeInput s pin)
    (release : ActualRelease actual pin) :
    trace.accepted = trace.consumed ∧ trace.captured = trace.exported ∧
      trace.exported.length = s.host.ackOffset.toNat ∧ s.host.exportBits.toNat = 0 := by
  rw [reached.package] at release
  have accepted := release_source rep s pin ha runtime release
  exact reached.custody.release_all_bits s pin trace accepted.1 accepted.2

theorem Reached.unacknowledged_blocks_release (reached : Reached image actual s trace rep)
    (pin : Session.Pins) (unacknowledged : 0 < s.host.exportBits.toNat) :
    (s.command pin).runtime.command ≠ 4#4 :=
  reached.custody.unacknowledged_blocks_release s pin trace unacknowledged

theorem Reached.next_start_empty (reached : Reached image actual s trace rep)
    (pin : Session.Pins) (runtime : Session.RuntimeInput s pin) (start : ActualStart actual pin) :
    s.host.exportBits = 0#7 ∧ s.host.unacknowledged = false := by
  rw [reached.package] at start
  have admitted := start_source rep s pin runtime start
  simp only [Bool.and_eq_true] at admitted
  exact reached.freeExport.start_empty s pin reached.custody.interval admitted.2

theorem compiled_pending (image : Compiled source idle) : (compiledImage image).pending.getLsbD 0 = false := by
  change (0#1).getLsbD 0 = false
  decide +kernel

theorem Reached.run {a : Nat} {actual : Package.State a} {s : Session.State a}
    (reached : Reached image actual s trace rep) (pins : List Session.Pins) (ha : a ≤ 3)
    (runtime : Session.RuntimeTrace image.program false s pins) :
    Reached image
      (actual.run (Package.Components.typed a) (pins.map SessionCorrespondence.pins))
      (s.run image.program false pins) (s.traceRun image.program false trace pins) rep := by
  have pending : rep.pending.getLsbD 0 = false := by rw [reached.installed]; rfl
  constructor
  · rw [reached.package]
    simpa only [pending] using SessionCorrespondence.run_correct rep
      s pins ha (by simpa only [pending] using runtime) reached.custody.structural
  · exact reached.custody.run s image.program false pins trace ha runtime
  · exact reached.freeExport.run s image.program false pins trace ha runtime reached.custody
  · exact reached.installed

theorem ready_run_eq (p : Program) (rep : SourceRefinement.Image p) (actualBoot : Package.State a)
    (boot : Session.State a) (package : actualBoot = SessionCorrespondence.values rep boot)
    (installed : rep.pending = 0#1) (structural : boot.core.Structural)
    (pins : List Session.Pins) (ha : a ≤ 3) (runtime : Session.RuntimeTrace p false boot pins) :
    actualBoot.run (Package.Components.typed a) (pins.map SessionCorrespondence.pins) =
      SessionCorrespondence.values rep (boot.run p false pins) := by
  rw [package]
  have pending : rep.pending.getLsbD 0 = false := by rw [installed]; rfl
  simpa only [pending] using SessionCorrespondence.run_correct rep
    boot pins ha (by simpa only [pending] using runtime) structural

theorem initialized_run_eq (image : Compiled source idle) (actualBoot : Package.State a)
    (boot : Session.State a) (initialized : BootCorrespondence.Initialized image actualBoot boot)
    (pins : List Session.Pins) (ha : a ≤ 3) (runtime : Session.RuntimeTrace image.program false boot pins) :
    actualBoot.run (Package.Components.typed a) (pins.map SessionCorrespondence.pins) =
      SessionCorrespondence.values (compiledImage image) (boot.run image.program false pins) :=
  ready_run_eq image.program (compiledImage image) actualBoot boot initialized.package rfl
    initialized.structural pins ha runtime

/-- An admitted physical START and later runtime samples retain custody for
any installed representation of the image, including one with older tail rows. -/
theorem started_run_from (image : Compiled source idle) (rep : SourceRefinement.Image image.program)
    (actualBoot : Package.State a) (boot : Session.State a)
    (package : actualBoot = SessionCorrespondence.values rep boot) (installed : rep.pending = 0#1)
    (structural : boot.core.Structural) (phase : boot.host.phase = 0#3)
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
      (((boot.run image.program false before).step image.program false startPin).traceRun image.program false {} after) rep := by
  have control := control_run boot image.program false before (idle_control boot phase)
  have beforeStructural := boot.run_structural image.program false before structural
  have beforePackage := ready_run_eq image.program rep actualBoot boot package installed structural
    before ha beforeRuntime
  have admitted := start
  rw [beforePackage] at admitted
  have sourceStart := start_source rep _ startPin startRuntime admitted
  have custody := Session.State.Custody.started (boot.run image.program false before) image.program false
    startPin startRuntime control sourceStart
  have freeExport := Session.State.FreeExport.started (boot.run image.program false before) image.program false
    startPin startRuntime sourceStart
  have pending : rep.pending.getLsbD 0 = false := by rw [installed]; rfl
  constructor
  · rw [beforePackage]
    have first := SessionCorrespondence.step_correct rep (boot.run image.program false before)
      startPin ha startRuntime beforeStructural
    simp only [pending] at first
    rw [first]
    simpa only [pending] using SessionCorrespondence.run_correct rep
      ((boot.run image.program false before).step image.program false startPin) after ha
      (by simpa only [pending] using afterRuntime) custody.structural
  · exact custody.run _ image.program false after {} ha afterRuntime
  · exact freeExport.run _ image.program false after {} ha afterRuntime custody
  · exact installed

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
      (((boot.run image.program false before).step image.program false startPin).traceRun image.program false {} after) :=
  started_run_from image (compiledImage image) actualBoot boot initialized.package rfl
    initialized.structural initialized.phase before startPin after ha beforeRuntime startRuntime start afterRuntime

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
