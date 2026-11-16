import Pinwheel.Hardware.StreamingReady.InitializedCustody
import Pinwheel.Hardware.StreamingReady.PublicPins
import Pinwheel.Program.StreamingJTAGTrace

/-! An initialized sampled-ready package, the compiled JTAG scan, and the
host's acknowledged receive stream use the same execution. -/
namespace Pinwheel.Hardware.StreamingReady.JTAGSession
open Pinwheel.Hardware Pinwheel.Program.StreamingReady
open Pinwheel.Program.StreamingJTAG
open Pinwheel.Hardware.StreamingReady.InitializedCustody

/-- The existing, kernel-checked upload waveform uses duration three. -/
theorem boot (startup : Package.State a) :
    let actual := startup.run (Package.Components.typed a)
      (SessionCorrespondence.pins BootPins.coldPin ::
        Pinwheel.Program.Streaming.BootPins.jtag.map SessionCorrespondence.pins)
    ∃ source : Session.State a,
      BootCorrespondence.Initialized (image 3) actual source ∧ Pipeline (image 3) actual source := by
  apply compiled_session
  rw [original_words]
  exact Pinwheel.Program.Streaming.BootPins.jtag_certified

private theorem canonical_wiring : Wiring.Certificate a (Wiring.canonical a) := by
  constructor <;> intros <;> rfl

private def publicLevels (s : Package.State a) : BitVec 8 :=
  (TinyWiring.canonical a).observe (Wiring.canonical a) (Package.Components.typed a)
    s (PublicPins.embed {}) .uio

private def publicStep (s : Package.State a) (i : Session.Pins) : Package.State a :=
  (TinyWiring.canonical a).step (Wiring.canonical a) (Package.Components.typed a)
    s (PublicPins.embed i)

private theorem publicStep_eq (s : Package.State a) (i : Session.Pins) :
    publicStep s i = s.step (Package.Components.typed a) (SessionCorrespondence.pins i) := by
  unfold publicStep TinyWiring.Description.step
  rw [PublicPins.engine_embed]
  exact canonical_wiring.step_eq _ _ _

private theorem publicLevels_eq (im : SourceRefinement.Image p) (s : Session.State a) :
    publicLevels (SessionCorrespondence.values im s) = 0#5 ++ s.core.pins.levels := by
  unfold publicLevels TinyWiring.Description.observe
  rw [PublicPins.engine_embed]
  have pins : ((Wiring.canonical a).observe (Package.Components.typed a)
      (SessionCorrespondence.values im s) (SessionCorrespondence.pins {}) : Values Package.Output) =
      (fun {w} => @Package.State.observe a (SessionCorrespondence.values im s)
        (Package.Components.typed a) (SessionCorrespondence.pins {}) w) := by
    funext w port
    exact canonical_wiring.observe_eq _ _ _ port
  rw [pins]
  have level (outputs : Values Package.Output) :
      (TinyWiring.canonical a).pads (PublicPins.embed {}) outputs .uio =
        0#5 ++ outputs .levels := by
    change (TinyWiring.canonicalOutput .uio).eval
      (TinyWiring.inputs (PublicPins.embed {}) outputs) TinyWiring.registers = _
    have active : TinyWiring.active.eval (TinyWiring.inputs (PublicPins.embed {}) outputs)
        TinyWiring.registers = (1 : BitVec 1) := by
      change (1#1 &&& 1#1) = 1#1
      decide +kernel
    rw [TinyWiring.canonicalOutput,Expr.eval,if_pos active]
    rfl
  rw [level]
  rfl

/-- TMS on uio_out[2] at each rising edge of uio_out[1]. Every observation
uses an enabled package. Normal runtime samples preserve that condition. -/
def publicTms (s : Package.State a) : List Session.Pins → List Bool
  | [] => []
  | i :: rest =>
    let next := publicStep s i
    let prevPins := publicLevels s
    let nextPins := publicLevels next
    (if !prevPins.getLsbD 1 && nextPins.getLsbD 1 then [nextPins.getLsbD 2] else []) ++ publicTms next rest

theorem publicTms_eq (d : Fin 256) (s : Session.State a) (pins : List Session.Pins)
    (ha : a ≤ 3) (ordinary : Session.RuntimeTrace (image d).program false s pins)
    (structural : s.core.Structural) :
    publicTms (SessionCorrespondence.values (Initialization.compiledImage (image d)) s) pins =
      (wireRun d s.core (s.runtimeInputs (image d).program false pins)).map ScanClock.tms := by
  induction pins generalizing s with
  | nil => rfl
  | cons i rest ih =>
    have next := SessionCorrespondence.step_correct (Initialization.compiledImage (image d)) s
      i ha ordinary.1 structural
    rw [compiled_pending] at next
    simp only [publicTms,publicStep_eq,next,publicLevels_eq,Session.State.runtimeInputs,wireRun,
      List.map_append]
    have tail := ih _ ordinary.2 (s.step_structural (image d).program false i structural)
    change _ = List.map ScanClock.tms (wireRun d (step (image d).program (s.command i).runtime s.core)
      ((s.step (image d).program false i).runtimeInputs (image d).program false rest)) at tail
    rw [← tail]
    congr 1
    simp only [BitVec.getLsbD_append,show 1 < 3 by decide,show 2 < 3 by decide,if_true]
    change (if !s.core.pins.levels[1] &&
        (step (image d).program (s.command i).runtime s.core).pins.levels[1] then
      [(step (image d).program (s.command i).runtime s.core).pins.levels[2]] else []) = _
    simp only [observed,rose,tck]
    by_cases rise : (!s.core.pins.levels[1] &&
        (step (image d).program (s.command i).runtime s.core).pins.levels[1]) = true <;>
      simp only [rise,↓reduceIte,Bool.false_eq_true,List.map_cons,List.map_nil]
    cases s.core.captures <;> rfl

private theorem trace_core (s : Session.State a) (p : Program) (pins : List Session.Pins)
    (trace : BitTrace) :
    s.traceRun p false trace pins = traceRun p s.core trace (s.runtimeInputs p false pins) := by
  induction pins generalizing s trace with
  | nil => rfl
  | cons i rest ih => exact ih (s.step p false i) (trace.step s.core (s.command i).runtime)

private theorem start_core (s : Session.State a) (p : Program) (pin : Session.Pins)
    (runtime : Session.RuntimeInput s pin)
    (admitted : ((s.command pin).runtime.command == 3 && s.core.canStart (s.command pin).runtime) = true) :
    (s.step p false pin).core = s.core.start p (s.command pin).runtime := by
  simp only [Bool.and_eq_true,beq_iff_eq] at admitted
  simp [Session.State.step,step,runtime.1,admitted.1,admitted.2]

/-- From a reached boot, actual START admission to actual RELEASE admission
preserves the TAP trace and the ordered TDO samples through acknowledged drain. -/
theorem completed_release (d : Fin 256) (actualBoot : Package.State a) (bootState : Session.State a)
    (initialized : BootCorrespondence.Initialized (image d) actualBoot bootState)
    (before : List Session.Pins) (startPin : Session.Pins) (after : List Session.Pins)
    (releasePin : Session.Pins) (ha : a ≤ 3)
    (beforeRuntime : Session.RuntimeTrace (image d).program false bootState before) :
    let p := (image d).program
    let ready := bootState.run p false before
    let actualReady := actualBoot.run (Package.Components.typed a) (before.map SessionCorrespondence.pins)
    let started := ready.step p false startPin
    let actualStarted := actualReady.step (Package.Components.typed a) (SessionCorrespondence.pins startPin)
    let final := started.run p false after
    let actualFinal := actualStarted.run (Package.Components.typed a) (after.map SessionCorrespondence.pins)
    let inputs := started.runtimeInputs p false after
    let trace := started.traceRun p false {} after
    let count := (ready.command startPin).runtime.startCount.toNat
    Session.RuntimeInput ready startPin →
    ActualStart actualReady startPin →
    Session.RuntimeTrace p false started after →
    (∀ i ∈ inputs, i.command ≠ 4#4) →
    Session.RuntimeInput final releasePin →
    ActualRelease actualFinal releasePin →
    0 < count →
    (∀ tap, walk tap (publicTms actualStarted after) =
      (.idle,count + if tap = .shiftDR then 1 else 0)) ∧
    trace.exported = tdoRun d started.core inputs ∧
    final.host.ackOffset.toNat = count ∧ final.host.exportBits.toNat = 0 := by
  dsimp only
  intro startRuntime start afterRuntime noRelease releaseRuntime release positive
  let p := (image d).program
  let ready := bootState.run p false before
  let actualReady := actualBoot.run (Package.Components.typed a) (before.map SessionCorrespondence.pins)
  let started := ready.step p false startPin
  let actualStarted := actualReady.step (Package.Components.typed a) (SessionCorrespondence.pins startPin)
  let final := started.run p false after
  let inputs := started.runtimeInputs p false after
  let trace := started.traceRun p false {} after
  let startCommand := (ready.command startPin).runtime
  let count := startCommand.startCount.toNat
  change (∀ tap, walk tap (publicTms actualStarted after) =
      (.idle,count + if tap = .shiftDR then 1 else 0)) ∧
    trace.exported = tdoRun d started.core inputs ∧
    final.host.ackOffset.toNat = count ∧ final.host.exportBits.toNat = 0
  have initial := started_run (image d) actualBoot bootState initialized before startPin [] ha
    beforeRuntime startRuntime start trivial
  have reached := started_run (image d) actualBoot bootState initialized before startPin after ha
    beforeRuntime startRuntime start afterRuntime
  have released := reached.release_all_bits releasePin ha releaseRuntime release
  have releaseEq := release
  rw [reached.package] at releaseEq
  have releaseAccepted := release_source (Initialization.compiledImage (image d)) final releasePin
    ha releaseRuntime releaseEq
  have beforeEq : actualReady = SessionCorrespondence.values (Initialization.compiledImage (image d)) ready := by
    unfold actualReady ready
    rw [initialized.package]
    simpa only [compiled_pending] using
      SessionCorrespondence.run_correct (Initialization.compiledImage (image d)) bootState before ha
        (by simpa only [compiled_pending] using beforeRuntime) initialized.structural
  have admission := start
  change ActualStart actualReady startPin at admission
  rw [beforeEq] at admission
  have accepted := start_source (Initialization.compiledImage (image d)) ready startPin startRuntime admission
  have coreStart : started.core = ready.core.start p startCommand :=
    start_core ready p startPin startRuntime accepted
  have ordinary : ∀ i ∈ inputs, Unreleased i := fun i member =>
    ⟨afterRuntime.runtimeInputs p false started after i member,noRelease i member⟩
  have endCore : final.core = run p started.core inputs := started.run_core p false after
  have positions := (run_schedule d started.core inputs
    (coreStart ▸ positioned_start d ready.core startCommand : Positioned d started.core) ordinary).1
  have retained : (run p started.core inputs).phase.retained = true := by
    have admittedRelease := releaseAccepted.2
    simp only [State.canRelease,Bool.and_eq_true] at admittedRelease
    exact endCore ▸ admittedRelease.1.1
  have completed : (run p started.core inputs).phase = .completed := by
    change (run (image d).program started.core inputs).phase = .completed
    change (run (image d).program started.core inputs).phase.retained = true at retained
    rcases positions.phase with phase | (phase | phase | phase) | phase <;>
      simp [phase,Phase.retained] at retained ⊢
  have completed' : (run p (ready.core.start p startCommand) inputs).phase = .completed :=
    coreStart ▸ completed
  have scan := completed_scan d ready.core startCommand inputs ordinary completed' positive
  have samples := completed_tdo_count d ready.core startCommand inputs ordinary completed' positive
  have pinTrace := publicTms_eq d started after ha afterRuntime initial.custody.structural
  have initialEq : actualStarted = SessionCorrespondence.values (Initialization.compiledImage (image d)) started :=
    initial.package
  rw [← initialEq] at pinTrace
  constructor
  · intro tap
    rw [pinTrace,coreStart]
    exact Prod.ext (scan.2 tap).1 (scan.2 tap).2
  · have captured : trace.captured = tdoRun d started.core inputs := by
      simpa only [trace,inputs,trace_core,List.nil_append] using
        tdo_trace d started.core inputs {}
          (coreStart ▸ positioned_start d ready.core startCommand : Positioned d started.core) ordinary
    have exported := released.2.1.symm.trans captured
    refine ⟨exported,?_,released.2.2.2⟩
    rw [← released.2.2.1,exported,coreStart]
    exact samples

end Pinwheel.Hardware.StreamingReady.JTAGSession
