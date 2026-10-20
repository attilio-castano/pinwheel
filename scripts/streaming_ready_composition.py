"""Generate joins of independently reconstructed sampled-ready streaming artifacts.

The factory prints theorem statements and ordinary proof terms. Fresh workers
must compile and audit them against the exact raw component and wrapper files;
Python return values do not qualify any behavioral claim.
"""


def generate(addr_bits):
    if type(addr_bits) is not int or addr_bits not in (1,2):
        raise ValueError('Qualified streaming address width must be 1 or 2')
    depth = str(2**addr_bits)
    source = r'''import ReadyCoreD@D@Proof
import ReadyQuadFrontendProof
import StreamingReadyWrappersD@D@
import Pinwheel.Hardware.StreamingReady.SessionCorrespondence
import Pinwheel.Hardware.StreamingReady.InitializedSession
import Pinwheel.Hardware.StreamingReady.WarmReset
import Pinwheel.Hardware.StreamingReady.PublicPins
import Pinwheel.Hardware.StreamingReady.BootCorrespondence
import Pinwheel.Hardware.StreamingReady.BootUpload
import Pinwheel.Hardware.StreamingReady.InitializedCustody
import Pinwheel.Program.StreamingReadyTiming
import Pinwheel.Program.StreamingReadyCustodySession
import Pinwheel.Program.StreamingReadyOwnerCut
import Pinwheel.Program.StreamingReadyEventualService
import Pinwheel.Program.StreamingReadySessionService

namespace Pinwheel.Artifact.StreamingReadySessionD@D@
open Pinwheel.Hardware Pinwheel.Hardware.StreamingReady
open Pinwheel.Program.StreamingReady

def components : Package.Components @A@ :=
  ⟨Pinwheel.Artifact.StreamingReadyFrontend.behavior,
    Pinwheel.Artifact.StreamingReadyCoreD@D@.behavior⟩

theorem components_correct : Package.Correct components where
  frontend_step := by intro i s w r; exact Pinwheel.Artifact.StreamingReadyFrontend.step_correct i s r
  frontend_observe := by intro i s w o; exact Pinwheel.Artifact.StreamingReadyFrontend.observe_correct i s o
  core_step := by intro i s w r; exact Pinwheel.Artifact.StreamingReadyCoreD@D@.step_correct i s r
  core_observe := by intro i s w o; exact Pinwheel.Artifact.StreamingReadyCoreD@D@.observe_correct i s o

abbrev actualPackage := Pinwheel.Artifact.StreamingReadyWrappersD@D@.actualPackage
abbrev actualTiny := Pinwheel.Artifact.StreamingReadyWrappersD@D@.actualTiny

def physicalStep (s : Package.State @A@) (i : TinyWiring.Pins) : Package.State @A@ :=
  actualTiny.step actualPackage components s i

def physicalObserve (s : Package.State @A@) (i : TinyWiring.Pins) : TinyWiring.Pad → BitVec 8 :=
  actualTiny.observe actualPackage components s i

def physicalRun (s : Package.State @A@) (inputs : List TinyWiring.Pins) : Package.State @A@ :=
  inputs.foldl physicalStep s

theorem physical_step_correct (s : Package.State @A@) (i : TinyWiring.Pins) :
    physicalStep s i = s.step (Package.Components.typed @A@)
      (TinyWiring.Description.enginePins (TinyWiring.canonical @A@) i) := by
  rw [physicalStep, Pinwheel.Artifact.StreamingReadyWrappersD@D@.tiny_correct.step_eq
    Pinwheel.Artifact.StreamingReadyWrappersD@D@.package_correct]
  exact Package.State.step_correct components_correct s _

theorem physical_observe_correct (s : Package.State @A@) (i : TinyWiring.Pins) (port : TinyWiring.Pad) :
    physicalObserve s i port = TinyWiring.Description.pads (TinyWiring.canonical @A@) i
      (s.observe (Package.Components.typed @A@) (TinyWiring.Description.enginePins (TinyWiring.canonical @A@) i)) port := by
  rw [physicalObserve,Pinwheel.Artifact.StreamingReadyWrappersD@D@.tiny_correct.observe_eq
    Pinwheel.Artifact.StreamingReadyWrappersD@D@.package_correct]
  rw [components_correct.eq_typed]

theorem physical_run_correct (s : Package.State @A@) (inputs : List TinyWiring.Pins) :
    physicalRun s inputs = s.run (Package.Components.typed @A@)
      (inputs.map (TinyWiring.Description.enginePins (TinyWiring.canonical @A@))) := by
  induction inputs generalizing s with
  | nil => rfl
  | cons i rest ih =>
    change physicalRun (physicalStep s i) rest =
      (s.step (Package.Components.typed @A@) (TinyWiring.Description.enginePins (TinyWiring.canonical @A@) i)).run
        (Package.Components.typed @A@) (rest.map (TinyWiring.Description.enginePins (TinyWiring.canonical @A@)))
    rw [physical_step_correct]
    exact ih _

theorem source_runtime_step_correct (image : SourceRefinement.Image p)
    (s : Session.State @A@) (i : TinyWiring.Pins)
    (hi : Session.RuntimeInput s (SessionCorrespondence.physicalPins i)) (hs : s.core.Structural) :
    physicalStep (SessionCorrespondence.values image s) i =
      SessionCorrespondence.values image
        (s.step p (image.pending.getLsbD 0) (SessionCorrespondence.physicalPins i)) := by
  rw [physical_step_correct,SessionCorrespondence.physical_pins_correct]
  exact SessionCorrespondence.step_correct image s _ (by decide) hi hs

theorem source_runtime_run_correct (image : SourceRefinement.Image p)
    (s : Session.State @A@) (inputs : List TinyWiring.Pins)
    (hi : Session.RuntimeTrace p (image.pending.getLsbD 0) s
      (inputs.map SessionCorrespondence.physicalPins)) (hs : s.core.Structural) :
    physicalRun (SessionCorrespondence.values image s) inputs =
      SessionCorrespondence.values image
        (s.run p (image.pending.getLsbD 0) (inputs.map SessionCorrespondence.physicalPins)) := by
  rw [physical_run_correct]
  have map : inputs.map (TinyWiring.Description.enginePins (TinyWiring.canonical @A@)) =
      (inputs.map SessionCorrespondence.physicalPins).map SessionCorrespondence.pins := by
    rw [List.map_map]
    apply List.map_congr_left
    intro i _
    exact SessionCorrespondence.physical_pins_correct i
  rw [map]
  exact SessionCorrespondence.run_correct image s _ (by decide) hi hs

theorem source_runtime_observe_correct (image : SourceRefinement.Image p)
    (s : Session.State @A@) (i : TinyWiring.Pins) (port : TinyWiring.Pad)
    (hi : Session.RuntimeInput s (SessionCorrespondence.physicalPins i)) (hs : s.core.Structural) :
    physicalObserve (SessionCorrespondence.values image s) i port =
      TinyWiring.Description.pads (TinyWiring.canonical @A@) i
        (SessionCorrespondence.outputs s (image.pending.getLsbD 0)
          (SessionCorrespondence.physicalPins i)) port := by
  rw [physical_observe_correct,SessionCorrespondence.physical_pins_correct]
  have outputs :
      (fun {w} => (SessionCorrespondence.values image s).observe (Package.Components.typed @A@)
        (SessionCorrespondence.pins (SessionCorrespondence.physicalPins i)) (w := w)) =
      @SessionCorrespondence.outputs @A@ s (image.pending.getLsbD 0)
        (SessionCorrespondence.physicalPins i) := by
    funext w out
    exact SessionCorrespondence.outputs_correct image s _ (by decide) hi hs out
  exact congrArg (fun f : Values Package.Output =>
    TinyWiring.Description.pads (TinyWiring.canonical @A@) i f port) outputs

abbrev enginePins : TinyWiring.Pins → Package.Pins :=
  TinyWiring.Description.enginePins (TinyWiring.canonical @A@)

theorem physical_warm_reset_correct (s : Package.State @A@) (i : TinyWiring.Pins)
    (cold : (enginePins i).initialize = 0)
    (command : (s.coreInputs components (enginePins i)) .command = 15) :
    physicalStep s i =
      ⟨Pinwheel.Hardware.Streaming.HostCorrespondence.values (Pinwheel.Program.Streaming.Host.step (WarmReset.frontendInput s (enginePins i))
        (WarmReset.frontendState s)),
        Initialization.values (WarmReset.metadata s.core) (WarmReset.runtime s.core)⟩ := by
  rw [physicalStep,Pinwheel.Artifact.StreamingReadyWrappersD@D@.tiny_correct.step_eq
    Pinwheel.Artifact.StreamingReadyWrappersD@D@.package_correct]
  exact WarmReset.package_step_correct components components_correct s _ cold command

/-- Actual TT/raw startup and physical frontend upload derive all source state. -/
theorem initialized_upload_correct (image : Compiled source idle) (startup : Package.State @A@)
    (coldPin : TinyWiring.Pins) (cold : (enginePins coldPin).initialize = 1)
    (uploadPins : List TinyWiring.Pins)
    (upload : Initialization.Upload image.program image.program.length
      (InitializedSession.coreHistory (InitializedSession.coldState @A@ (enginePins coldPin))
        (uploadPins.map enginePins)))
    (commitPin : TinyWiring.Pins) (commit : Initialization.Commit image.program
      (fun {w} => ((InitializedSession.coldState @A@ (enginePins coldPin)).run (Package.Components.typed @A@)
        (uploadPins.map enginePins)).coreInputs (Package.Components.typed @A@) (enginePins commitPin) (w := w))) :
    physicalRun startup (coldPin :: (uploadPins ++ [commitPin])) =
      SessionCorrespondence.values (Initialization.compiledImage image)
        (InitializedSession.sourceState image (enginePins coldPin)
          (uploadPins.map enginePins) (enginePins commitPin)) := by
  rw [physical_run_correct]
  simpa only [List.map_cons,List.map_append,List.map_singleton,List.map_nil] using
    InitializedSession.initialized_upload_correct image startup (enginePins coldPin) cold
      (uploadPins.map enginePins) upload (enginePins commitPin) commit

/-- Initialization and every following runtime physical prefix compose without
an assumed image/register agreement or supplied structural invariant. -/
theorem initialized_runtime_correct (image : Compiled source idle) (startup : Package.State @A@)
    (coldPin : TinyWiring.Pins) (cold : (enginePins coldPin).initialize = 1)
    (uploadPins : List TinyWiring.Pins)
    (upload : Initialization.Upload image.program image.program.length
      (InitializedSession.coreHistory (InitializedSession.coldState @A@ (enginePins coldPin))
        (uploadPins.map enginePins)))
    (commitPin : TinyWiring.Pins) (commit : Initialization.Commit image.program
      (fun {w} => ((InitializedSession.coldState @A@ (enginePins coldPin)).run (Package.Components.typed @A@)
        (uploadPins.map enginePins)).coreInputs (Package.Components.typed @A@) (enginePins commitPin) (w := w)))
    (runtimePins : List TinyWiring.Pins)
    (runtime : Session.RuntimeTrace image.program false
      (InitializedSession.sourceState (a := @A@) image (enginePins coldPin)
        (uploadPins.map enginePins) (enginePins commitPin))
      (runtimePins.map SessionCorrespondence.physicalPins)) :
    physicalRun startup ((coldPin :: (uploadPins ++ [commitPin])) ++ runtimePins) =
      SessionCorrespondence.values (Initialization.compiledImage image)
        ((InitializedSession.sourceState image (enginePins coldPin) (uploadPins.map enginePins)
          (enginePins commitPin)).run image.program false (runtimePins.map SessionCorrespondence.physicalPins)) := by
  rw [physical_run_correct,List.map_append]
  have map : runtimePins.map enginePins =
      (runtimePins.map SessionCorrespondence.physicalPins).map SessionCorrespondence.pins := by
    rw [List.map_map]
    apply List.map_congr_left
    intro i _
    exact SessionCorrespondence.physical_pins_correct i
  rw [map]
  simpa only [List.map_cons,List.map_append,List.map_singleton,List.map_nil] using
    InitializedSession.initialized_runtime_correct image startup (enginePins coldPin) cold
      (uploadPins.map enginePins) upload (enginePins commitPin) commit
      (runtimePins.map SessionCorrespondence.physicalPins) runtime (by decide)

def i2cBootPins : List TinyWiring.Pins :=
  (BootPins.coldPin :: BootPins.i2c).map PublicPins.embed

theorem embedded_engine_pins (pins : List Session.Pins) :
    (pins.map PublicPins.embed).map enginePins = pins.map SessionCorrespondence.pins := by
  rw [List.map_map]
  apply List.map_congr_left
  intro i _
  exact PublicPins.engine_embed @A@ i

/-- Actual TT/raw power-up follows all 1,961 concrete public-pin boot samples. -/
theorem concrete_i2c_initialized (startup : Package.State @A@) :
    ∃ final : Session.State @A@, BootCorrespondence.Initialized (i2cImage .standard)
      (physicalRun startup i2cBootPins) final := by
  rw [physical_run_correct,i2cBootPins,embedded_engine_pins,List.map_cons]
  exact BootCorrespondence.i2c_initialized startup

theorem physical_run_append (startup : Package.State @A@) (before after : List TinyWiring.Pins) :
    physicalRun startup (before ++ after) = physicalRun (physicalRun startup before) after :=
  List.foldl_append

theorem physical_run_source_pins (startup : Package.State @A@) (inputs : List TinyWiring.Pins) :
    physicalRun startup inputs = startup.run (Package.Components.typed @A@)
      ((inputs.map SessionCorrespondence.physicalPins).map SessionCorrespondence.pins) := by
  rw [physical_run_correct,List.map_map]
  have map : inputs.map enginePins = inputs.map
      (SessionCorrespondence.pins ∘ SessionCorrespondence.physicalPins) := by
    apply List.map_congr_left
    intro i _
    exact SessionCorrespondence.physical_pins_correct i
  exact congrArg (startup.run (Package.Components.typed @A@)) map

def PhysicalCustody (image : Compiled source idle) (actualBoot : Package.State @A@)
    (boot : Session.State @A@) : Prop :=
  ∀ (before : List TinyWiring.Pins) (start : TinyWiring.Pins) (after : List TinyWiring.Pins),
    Session.RuntimeTrace image.program false boot (before.map SessionCorrespondence.physicalPins) →
    Session.RuntimeInput (boot.run image.program false (before.map SessionCorrespondence.physicalPins))
      (SessionCorrespondence.physicalPins start) →
    InitializedCustody.ActualStart (physicalRun actualBoot before) (SessionCorrespondence.physicalPins start) →
    Session.RuntimeTrace image.program false
      ((boot.run image.program false (before.map SessionCorrespondence.physicalPins)).step image.program false
        (SessionCorrespondence.physicalPins start)) (after.map SessionCorrespondence.physicalPins) →
    InitializedCustody.Reached image (physicalRun actualBoot (before ++ start :: after))
      (((boot.run image.program false (before.map SessionCorrespondence.physicalPins)).step image.program false
        (SessionCorrespondence.physicalPins start)).run image.program false (after.map SessionCorrespondence.physicalPins))
      (((boot.run image.program false (before.map SessionCorrespondence.physicalPins)).step image.program false
        (SessionCorrespondence.physicalPins start)).traceRun image.program false {} (after.map SessionCorrespondence.physicalPins))

theorem physical_custody (initialized : BootCorrespondence.Initialized image actualBoot boot) :
    PhysicalCustody image actualBoot boot := by
  intro before start after ordinary first accepted later
  rw [physical_run_source_pins] at accepted
  have reached := InitializedCustody.started_run image actualBoot boot initialized
    (before.map SessionCorrespondence.physicalPins) (SessionCorrespondence.physicalPins start)
    (after.map SessionCorrespondence.physicalPins) (by decide) ordinary first accepted later
  rw [physical_run_source_pins,List.map_append,List.map_cons,List.map_append,List.map_cons]
  simpa only [Package.State.run,Streaming.Package.State.run,List.foldl_append,List.foldl_cons] using reached

theorem concrete_i2c_custody (startup : Package.State @A@) :
    ∃ boot : Session.State @A@,
      BootCorrespondence.Initialized (i2cImage .standard) (physicalRun startup i2cBootPins) boot ∧
      PhysicalCustody (i2cImage .standard) (physicalRun startup i2cBootPins) boot := by
  obtain ⟨boot,initialized⟩ := concrete_i2c_initialized startup
  exact ⟨boot,initialized,physical_custody initialized⟩

def PhysicalProgress (image : Compiled source idle) (actualBoot : Package.State @A@)
    (boot : Session.State @A@) : Prop :=
  ∀ (before : List TinyWiring.Pins) (start : TinyWiring.Pins) (incoming : Nat → TinyWiring.Pins),
    let sourceBefore := boot.run image.program false (before.map SessionCorrespondence.physicalPins)
    let sourceStart := sourceBefore.step image.program false (SessionCorrespondence.physicalPins start)
    let sampled := SessionCorrespondence.physicalPins ∘ incoming
    Session.RuntimeTrace image.program false boot (before.map SessionCorrespondence.physicalPins) →
    Session.RuntimeInput sourceBefore (SessionCorrespondence.physicalPins start) →
    InitializedCustody.ActualStart (physicalRun actualBoot before) (SessionCorrespondence.physicalPins start) →
    SessionService.Runtime image.program false sourceStart sampled →
    SessionService.Fair image.program false sourceStart sampled →
    ∃ edges : Nat,
      let physical := (List.range edges).map incoming
      let final := sourceStart.run image.program false (physical.map SessionCorrespondence.physicalPins)
      InitializedCustody.Reached image (physicalRun actualBoot (before ++ start :: physical)) final
        (sourceStart.traceRun image.program false {} (physical.map SessionCorrespondence.physicalPins)) ∧
      final.core.phase.retained = true ∧
      ((physicalRun actualBoot (before ++ start :: physical)).core .phase = 5#3 ∨
       (physicalRun actualBoot (before ++ start :: physical)).core .phase = 6#3)

theorem physical_progress (initialized : BootCorrespondence.Initialized image actualBoot boot) :
    PhysicalProgress image actualBoot boot := by
  intro before start incoming
  dsimp only
  intro ordinary first accepted runtime fair
  let sourceBefore := boot.run image.program false (before.map SessionCorrespondence.physicalPins)
  have agreeBefore : physicalRun actualBoot before =
      SessionCorrespondence.values (Initialization.compiledImage image) sourceBefore := by
    rw [initialized.package]
    simpa only [InitializedCustody.compiled_pending] using
      source_runtime_run_correct (Initialization.compiledImage image) boot before
        (by simpa only [InitializedCustody.compiled_pending] using ordinary) initialized.structural
  have actual := accepted
  rw [agreeBefore] at actual
  have admitted := InitializedCustody.start_source (Initialization.compiledImage image)
    sourceBefore (SessionCorrespondence.physicalPins start) first actual
  obtain ⟨edges,retained⟩ := SessionService.admitted_start image.program false sourceBefore
    (SessionCorrespondence.physicalPins start) (SessionCorrespondence.physicalPins ∘ incoming)
    first admitted runtime fair
  have later := SessionService.Runtime.runtimeTrace image.program false
    (sourceBefore.step image.program false (SessionCorrespondence.physicalPins start))
    (SessionCorrespondence.physicalPins ∘ incoming) runtime edges
  have map : ((List.range edges).map incoming).map SessionCorrespondence.physicalPins =
      SessionService.clocks (SessionCorrespondence.physicalPins ∘ incoming) edges := by
    rw [List.map_map]
    rfl
  rw [← map] at later retained
  have reached := physical_custody initialized before start ((List.range edges).map incoming)
    ordinary first accepted later
  refine ⟨edges,reached,retained,?_⟩
  rw [reached.package]
  have code : ∀ phase : Phase, phase.retained = true → phase.code = 5#3 ∨ phase.code = 6#3 := by
    intro phase retained
    cases phase <;> simp_all [Phase.retained,Phase.code]
  exact code _ retained

/-- Reached host-credit fairness and unbounded-peer-guard fairness imply a
finite retained success or fault. Bounded guards need no readiness fairness. -/
theorem concrete_i2c_progress (startup : Package.State @A@) :
    ∃ boot : Session.State @A@,
      BootCorrespondence.Initialized (i2cImage .standard) (physicalRun startup i2cBootPins) boot ∧
      PhysicalProgress (i2cImage .standard) (physicalRun startup i2cBootPins) boot := by
  obtain ⟨boot,initialized⟩ := concrete_i2c_initialized startup
  exact ⟨boot,initialized,physical_progress initialized⟩

/-- Concrete initialization and arbitrary source-legal physical runtime compose.
The independent source state and its structural invariant are both derived. -/
theorem concrete_i2c_runtime (startup : Package.State @A@) :
    ∃ final : Session.State @A@,
      BootCorrespondence.Initialized (i2cImage .standard) (physicalRun startup i2cBootPins) final ∧
      ∀ inputs : List TinyWiring.Pins,
        Session.RuntimeTrace (i2cImage .standard).program false final
          (inputs.map SessionCorrespondence.physicalPins) →
        physicalRun startup (i2cBootPins ++ inputs) =
          SessionCorrespondence.values (Initialization.compiledImage (i2cImage .standard))
            (final.run (i2cImage .standard).program false (inputs.map SessionCorrespondence.physicalPins)) := by
  obtain ⟨final,initialized⟩ := concrete_i2c_initialized startup
  refine ⟨final,initialized,?_⟩
  intro inputs runtime
  rw [physical_run_append,initialized.package]
  exact source_runtime_run_correct _ final inputs runtime initialized.structural

end Pinwheel.Artifact.StreamingReadySessionD@D@
'''
    source = source.replace('@D@',depth).replace('@A@',str(addr_bits))
    return {'StreamingReadySessionD'+depth:source}
