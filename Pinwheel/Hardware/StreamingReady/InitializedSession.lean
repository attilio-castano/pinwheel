import Pinwheel.Hardware.StreamingReady.Initialization
import Pinwheel.Hardware.StreamingReady.SessionCorrespondence

/-! Physical frontend upload grammar to an initialized joint source session.
No initial register, bank or source-execution agreement is assumed. The grammar
constrains delivered commands to the compiled rows and an actual COMMIT. -/
namespace Pinwheel.Hardware.StreamingReady.InitializedSession
open Pinwheel.Hardware Pinwheel.Program.StreamingReady
open Pinwheel.Hardware.Streaming
set_option linter.unusedSimpArgs false

theorem state_ext {left right : Package.State a}
    (frontend : (fun {w} => left.frontend (w := w)) = (fun {w} => right.frontend (w := w)))
    (core : (fun {w} => left.core (w := w)) = (fun {w} => right.core (w := w))) : left = right := by
  cases left with
  | mk lf lc =>
    cases right with
    | mk rf rc =>
      change @lf = @rf at frontend
      change @lc = @rc at core
      cases frontend
      cases core
      rfl

private theorem bit_roundtrip : ∀ x : BitVec 1, BitVec.ofBool (x.getLsbD 0) = x := by
  decide +kernel

def coldHost (i : Package.Pins) : Pinwheel.Program.Streaming.Host.State :=
  { sckPrev := i.sck.getLsbD 0, csnPrev := i.csn.getLsbD 0 }

def coldState (a : Nat) (i : Package.Pins) : Package.State a :=
  ⟨HostCorrespondence.values (coldHost i),Initialization.values {} ({} : Initialization.Carrier a)⟩

theorem cold_core_input (s : Package.State a) (i : Package.Pins) :
    s.coreInputs (Package.Components.typed a) i .initialize = i.initialize := rfl

theorem cold_frontend (s : Package.State a) (i : Package.Pins) (cold : i.initialize = 1) :
    @Circuit.step _ _ _ Frontend.circuit (s.frontendInputs (Package.Components.typed a) i) s.frontend =
      @HostCorrespondence.values (coldHost i) := by
  funext w register
  cases register <;> simp [Frontend.circuit,Circuit.step,Frontend.next,Expr.eval,
    Package.State.frontendInputs,Streaming.Package.State.frontendInputs,Package.Pins.inputs,Streaming.Package.Pins.inputs,cold,HostCorrespondence.values,coldHost]
  all_goals exact (bit_roundtrip _).symm

theorem cold_correct (s : Package.State a) (i : Package.Pins) (cold : i.initialize = 1) :
    s.step (Package.Components.typed a) i = coldState a i := by
  apply state_ext
  · exact cold_frontend s i cold
  · exact Initialization.cold_values _ s.core ((cold_core_input s i).trans cold)

/-- Exact pre-edge commands from the actual typed frontend and feedback. -/
def coreHistory (s : Package.State a) : List Package.Pins → List (Values Core.Input)
  | [] => []
  | i::rest => (fun {w} => s.coreInputs (Package.Components.typed a) i (w := w)) :: coreHistory (s.step (Package.Components.typed a) i) rest

def frontendHistory (s : Package.State a) : List Package.Pins → List (Values Frontend.Input)
  | [] => []
  | i::rest => (fun {w} => s.frontendInputs (Package.Components.typed a) i (w := w)) :: frontendHistory (s.step (Package.Components.typed a) i) rest

theorem core_history_append (s : Package.State a) (first rest : List Package.Pins) :
    coreHistory s (first ++ rest) = coreHistory s first ++ coreHistory (s.run (Package.Components.typed a) first) rest := by
  induction first generalizing s with
  | nil => rfl
  | cons i first ih =>
    change _ :: coreHistory (s.step (Package.Components.typed a) i) (first ++ rest) = _
    rw [ih]
    rfl

theorem run_core (s : Package.State a) (samples : List Package.Pins) :
    (fun {w} => (s.run (Package.Components.typed a) samples).core (w := w)) =
      @Initialization.rawRun a s.core (coreHistory s samples) := by
  induction samples generalizing s with
  | nil => rfl
  | cons i rest ih =>
    change (fun {w} => ((s.step (Package.Components.typed a) i).run (Package.Components.typed a) rest).core (w := w)) =
      @Initialization.rawRun a (s.step (Package.Components.typed a) i).core (coreHistory (s.step (Package.Components.typed a) i) rest)
    exact ih _

theorem run_frontend (s : Package.State a) (samples : List Package.Pins) :
    (fun {w} => (s.run (Package.Components.typed a) samples).frontend (w := w)) =
      @HostCorrespondence.rawRun s.frontend (frontendHistory s samples) := by
  induction samples generalizing s with
  | nil => rfl
  | cons i rest ih =>
    change (fun {w} => ((s.step (Package.Components.typed a) i).run (Package.Components.typed a) rest).frontend (w := w)) =
      @HostCorrespondence.rawRun (s.step (Package.Components.typed a) i).frontend (frontendHistory (s.step (Package.Components.typed a) i) rest)
    exact ih _

theorem run_append (s : Package.State a) (first rest : List Package.Pins) :
    s.run (Package.Components.typed a) (first ++ rest) = (s.run (Package.Components.typed a) first).run (Package.Components.typed a) rest := by
  simp only [Package.State.run,Streaming.Package.State.run,List.foldl_append]

theorem frontend_source_roundtrip (s : Pinwheel.Program.Streaming.Host.State) :
    HostCorrespondence.stateFromValues (HostCorrespondence.values s) = s := by
  cases s
  simp only [HostCorrespondence.stateFromValues,HostCorrespondence.values,BitVec.getLsbD_ofBool,
    decide_true,Bool.true_and]

def sourceState (_image : Compiled source idle) (cold : Package.Pins)
    (upload : List Package.Pins) (commit : Package.Pins) : Session.State a :=
  { host := Pinwheel.Program.Streaming.Host.run (coldHost cold)
      ((frontendHistory (coldState a cold) (upload ++ [commit])).map HostCorrespondence.inputFromValues)
    core := Initialization.installedState
      (coreHistory (coldState a cold) upload) commit.rawInputs }

theorem source_structural (image : Compiled source idle) (cold : Package.Pins)
    (upload : List Package.Pins) (commit : Package.Pins) :
    (sourceState (a := a) image cold upload commit).core.Structural :=
  Initialization.initialized_structural _ _

/-- An actual pin prefix whose delivered command grammar uploads the compiled
image derives the complete initialized frontend/core source representation. -/
theorem initialized_upload_correct (image : Compiled source idle) (startup : Package.State a)
    (coldPin : Package.Pins) (cold : coldPin.initialize = 1) (uploadPins : List Package.Pins)
    (upload : Initialization.Upload image.program image.program.length
      (coreHistory (coldState a coldPin) uploadPins))
    (commitPin : Package.Pins) (commit : Initialization.Commit image.program
      (fun {w} => ((coldState a coldPin).run (Package.Components.typed a) uploadPins).coreInputs
        (Package.Components.typed a) commitPin (w := w))) :
    startup.run (Package.Components.typed a) (coldPin :: (uploadPins ++ [commitPin])) =
      SessionCorrespondence.values (Initialization.compiledImage image)
        (sourceState image coldPin uploadPins commitPin) := by
  have initialized : startup.step (Package.Components.typed a) coldPin = coldState a coldPin := cold_correct startup coldPin cold
  apply state_ext
  · change (fun {w} => ((startup.step (Package.Components.typed a) coldPin).run (Package.Components.typed a)
        (uploadPins ++ [commitPin])).frontend (w := w)) = _
    rw [initialized,run_frontend,HostCorrespondence.run_fromRaw]
    have roundtrip := frontend_source_roundtrip (coldHost coldPin)
    change HostCorrespondence.stateFromValues (coldState a coldPin).frontend = coldHost coldPin at roundtrip
    rw [roundtrip]
    rfl
  · rw [run_core]
    have history : coreHistory startup (coldPin :: (uploadPins ++ [commitPin])) =
        (fun {w} => startup.coreInputs (Package.Components.typed a) coldPin (w := w)) ::
          (coreHistory (coldState a coldPin) uploadPins ++
            [(fun {w} => ((coldState a coldPin).run (Package.Components.typed a) uploadPins).coreInputs
              (Package.Components.typed a) commitPin (w := w))]) := by
      change _ :: coreHistory (startup.step (Package.Components.typed a) coldPin) (uploadPins ++ [commitPin]) = _
      rw [initialized,core_history_append]
      rfl
    rw [history]
    exact Initialization.compiled_upload_correct image startup.core
      (startup.coreInputs (Package.Components.typed a) coldPin) ((cold_core_input startup coldPin).trans cold)
      _ upload _ commit


/-- Cold initialization, compiler-bound physical upload and every runtime pin
prefix compose directly. Structural bounds are established by the upload. -/
theorem initialized_runtime_correct (image : Compiled source idle) (startup : Package.State a)
    (coldPin : Package.Pins) (cold : coldPin.initialize = 1) (uploadPins : List Package.Pins)
    (upload : Initialization.Upload image.program image.program.length
      (coreHistory (coldState a coldPin) uploadPins))
    (commitPin : Package.Pins) (commit : Initialization.Commit image.program
      (fun {w} => ((coldState a coldPin).run (Package.Components.typed a) uploadPins).coreInputs
        (Package.Components.typed a) commitPin (w := w)))
    (runtimePins : List Session.Pins) (runtime : Session.RuntimeTrace image.program false
      (sourceState (a := a) image coldPin uploadPins commitPin) runtimePins) (ha : a ≤ 3) :
    startup.run (Package.Components.typed a) ((coldPin :: (uploadPins ++ [commitPin])) ++
      runtimePins.map SessionCorrespondence.pins) =
      SessionCorrespondence.values (Initialization.compiledImage image)
        ((sourceState image coldPin uploadPins commitPin).run image.program false runtimePins) := by
  rw [run_append,initialized_upload_correct image startup coldPin cold uploadPins upload commitPin commit]
  have pending : (Initialization.compiledImage image).pending.getLsbD 0 = false := by
    change (0#1).getLsbD 0 = false
    decide +kernel
  simpa only [pending] using SessionCorrespondence.run_correct (Initialization.compiledImage image)
    (sourceState (a := a) image coldPin uploadPins commitPin) runtimePins ha
    (by simpa only [pending] using runtime) (source_structural image coldPin uploadPins commitPin)

end Pinwheel.Hardware.StreamingReady.InitializedSession
