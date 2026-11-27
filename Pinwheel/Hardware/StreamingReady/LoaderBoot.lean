import Pinwheel.Hardware.StreamingReady.BootCorrespondence
import Pinwheel.Program.StreamingReadyLoader

/-! A concrete upload with idle raw inputs determines the whole source session
it leaves behind: the frontend computed by `Loader` and the installed engine.
Any image's boot pins can use this to name a concrete starting state. -/
namespace Pinwheel.Hardware.StreamingReady.LoaderBoot
open Pinwheel.Hardware Pinwheel.Hardware.Streaming.HostCorrespondence
open Pinwheel.Program.StreamingReady Initialization BootCorrespondence

set_option maxHeartbeats 5000000

private def carrier (installed : Bool) : Carrier 1 :=
  {generation := if installed then 1 else 0}

private theorem carrier_core (loader : Loader.State) : ofCarrier (carrier loader.installed) = Loader.core loader := by
  cases loader with
  | mk host written installed => cases installed <;> rfl

private theorem metadata_valid (p : Program) (n : Nat) : (metadataAfter p n).valid = 0 := by
  cases n <;> rfl

set_option linter.unusedSimpArgs false in
private theorem loader_status (image : Compiled source idle) (loader : Loader.State) (n : Nat) (pin : Session.Pins) (i : Values Core.Input)
    (written : loader.written = decide (0 < n))
    (rejected : (Core.circuit 1).observe i (Initialization.values
      (metadata image.program n loader.installed) (carrier loader.installed)) .rejected = 0) :
    (fun {w} (port : Core.Output w) => (Core.circuit 1).observe i (Initialization.values
      (metadata image.program n loader.installed) (carrier loader.installed)) port) =
      @statusValues (Loader.status loader pin) := by
  funext w port
  cases port <;> try rfl
  case valid =>
    change (metadata image.program n loader.installed).valid = BitVec.ofBool loader.installed
    cases loader.installed
    · exact metadata_valid image.program n
    · rfl
  case pending =>
    change (metadata image.program n loader.installed).pending = BitVec.ofBool (loader.written && !loader.installed)
    rw [written]
    cases loader.installed <;> cases n <;> rfl
  case rejected => exact rejected
  all_goals
    have boundary : (Phase.free == Phase.boundary) = false := by decide +kernel
    have waiting : (Phase.free == Phase.waiting) = false := by decide +kernel
    simp [Core.circuit, Circuit.observe, Core.output, Core.busy, Core.retained, Core.isPhase,
      Core.both, Core.either, Expr.eval, Initialization.values, Pinwheel.Hardware.Streaming.Initialization.values,
      carrier, Pinwheel.Program.Streaming.Phase.code, statusValues, Loader.status, Loader.core,
      State.status, Phase.busy, Phase.retained, boundary, waiting]

private structure Matches (image : Compiled source idle) (control : BootPins.Control) (n : Nat) (installed : Bool)
    (actual : Package.State 1) (loader : Loader.State) : Prop where
  core : Related image control n installed actual (carrier installed)
  host : stateFromValues actual.frontend = loader.host
  installed : loader.installed = installed
  written : loader.written = decide (0 < n)

private theorem next_matches (image : Compiled source idle) {control : BootPins.Control} (actual : Package.State 1) (loader : Loader.State) (pin : Session.Pins)
    (same : Matches image control n installed actual loader) (raw : pin.rawInputs = 0)
    (safe : Pinwheel.Program.Streaming.Host.BootControl.Safe control)
    (delivery : BootPins.Delivery image.words idle n installed
      (Pinwheel.Program.Streaming.Host.BootControl.command (pin.host {}) control) nextN nextInstalled) :
    Matches image (Pinwheel.Program.Streaming.Host.BootControl.step false (pin.host {}) control)
      nextN nextInstalled (actual.step (Package.Components.typed 1) (SessionCorrespondence.pins pin))
      (Loader.step loader pin) := by
  let c := Pinwheel.Program.Streaming.Host.BootControl.command (pin.host {}) control
  have input := BootCorrespondence.core_inputs actual pin control same.core.project
  have command : loader.host.command (pin.host {}) = c := by
    rw [← same.host, Pinwheel.Program.Streaming.Host.BootControl.command_correct, same.core.project]
  obtain ⟨after, effects⟩ := delivery_effects image n installed c (carrier installed) same.core.phase
    same.core.generation same.core.structural same.core.within same.core.complete delivery
  have rejected : actual.status (Package.Components.typed 1) (SessionCorrespondence.pins pin) .rejected = 0 := by
    unfold Package.State.status Pinwheel.Hardware.Streaming.Package.State.status
    rw [input, same.core.core]
    exact effects.rejected
  have state : after = carrier nextInstalled := by
    have commandRaw : c.runtime.rawInputs = 0 := raw
    rw [effects.carrier, commandRaw]
    cases delivery with
    | quiet _ quiet => rw [quiet]; cases installed <;> rfl
    | write _ off _ write _ _ => rw [write, off]; rfl
    | commit _ off _ commit _ _ => rw [commit, off]; rfl
  have status : (fun {w} (port : Core.Output w) =>
      actual.status (Package.Components.typed 1) (SessionCorrespondence.pins pin) port) =
      @statusValues (Loader.status loader pin) := by
    unfold Package.State.status Pinwheel.Hardware.Streaming.Package.State.status
    rw [input, same.core.core, ← same.installed]
    exact loader_status image loader n pin (commandValues c) same.written (same.installed.symm ▸ effects.rejected)
  have front : (fun {w} (port : Pinwheel.Hardware.Streaming.Frontend.Input w) =>
      actual.frontendInputs (Package.Components.typed 1) (SessionCorrespondence.pins pin) port) =
      @inputs (pin.host (Loader.status loader pin)) := by
    unfold Package.State.frontendInputs Pinwheel.Hardware.Streaming.Package.State.frontendInputs
    rw [status]
    exact SessionCorrespondence.host_inputs pin (Loader.status loader pin)
  constructor
  · constructor
    · exact BootCorrespondence.frontend_project actual pin control same.core.project safe rejected
    · change @Circuit.step _ _ _ (Core.circuit 1)
        (actual.coreInputs (Package.Components.typed 1) (SessionCorrespondence.pins pin)) actual.core = _
      rw [input, same.core.core, effects.step, state]
    · exact state ▸ effects.phase
    · exact state ▸ effects.generation
    · exact (state ▸ effects.transfer).trans same.core.transfer
    · exact state ▸ effects.structural
    · exact effects.within
    · exact effects.complete
  · change stateFromValues (@Circuit.step _ _ _ Pinwheel.Hardware.Streaming.Frontend.circuit
        (actual.frontendInputs (Package.Components.typed 1) (SessionCorrespondence.pins pin)) actual.frontend) = _
    rw [front, ← state_roundtrip actual.frontend, same.host, step_values,
      InitializedSession.frontend_source_roundtrip]
    rfl
  · change (loader.installed || (loader.host.command (pin.host {})).runtime.command == 2) = nextInstalled
    rw [command, same.installed]
    cases delivery with
    | quiet _ eq => rw [eq]; cases installed <;> rfl
    | write _ off _ eq _ _ => rw [eq, off]; rfl
    | commit _ off _ eq _ _ => rw [eq, off]; rfl
  · change (loader.written || (loader.host.command (pin.host {})).runtime.command == 1) = decide (0 < nextN)
    rw [command, same.written]
    cases delivery with
    | quiet _ eq => rw [eq]; simp
    | write _ _ _ eq _ _ => rw [eq]; simp
    | commit _ _ _ eq _ _ => rw [eq]; simp

private theorem loader_run (image : Compiled source idle) {control : BootPins.Control} (actual : Package.State 1) (loader : Loader.State) (pins : List Session.Pins)
    (same : Matches image control n installed actual loader) (raw : ∀ pin ∈ pins, pin.rawInputs = 0)
    (certified : BootPins.Certified image.words idle control n installed pins) :
    let final := pins.foldl Loader.step loader
    Initialized image (actual.run (Package.Components.typed 1) (pins.map SessionCorrespondence.pins))
      ⟨final.host, Loader.core final⟩ := by
  induction certified generalizing actual loader with
  | nil control n installed complete done phase ready active =>
    have allRows : n = image.program.length := complete.trans (image_length image)
    have project : Pinwheel.Program.Streaming.Host.BootControl.project loader.host = control :=
      same.host ▸ same.core.project
    change Initialized image actual ⟨loader.host, Loader.core loader⟩
    have coreEq : ofCarrier (carrier installed) = Loader.core loader := same.installed ▸ carrier_core loader
    refine ⟨?_, coreEq ▸ same.core.structural, rfl, ?_, rfl, ?_, ?_, ?_⟩
    · apply InitializedSession.state_ext
      · change (fun {w} => actual.frontend (w := w)) = @values loader.host
        rw [← same.host, state_roundtrip]
      · rw [same.core.core]
        simp only [metadata, done, if_true, allRows]
        rw [values_installed image.program (@compiledCanonical _ _ image), ← coreEq, done]
        rfl
    · change (Loader.core loader).generation = 1
      simp [Loader.core, same.installed, done]
    · exact (congrArg Pinwheel.Program.Streaming.Host.BootControl.State.phase project).trans phase
    · exact (congrArg Pinwheel.Program.Streaming.Host.BootControl.State.ready project).trans ready
    · exact (congrArg Pinwheel.Program.Streaming.Host.BootControl.State.active project).trans active
  | cons safe delivery after ih =>
    exact ih _ _ (next_matches image _ _ _ same (raw _ List.mem_cons_self) safe delivery)
      (fun pin member => raw pin (List.mem_cons_of_mem _ member))

/-- From arbitrary power-up registers, the cold pin and a certified upload with
idle raw inputs reach `Loader.seed pins`. -/
theorem initialized (image : Compiled source idle) (pins : List Session.Pins)
    (noRaw : ∀ pin ∈ pins, pin.rawInputs = 0)
    (certified : BootPins.Certified image.words idle BootPins.initialControl 0 false pins)
    (startup : Package.State 1) :
    Initialized image (startup.run (Package.Components.typed 1)
      (SessionCorrespondence.pins BootPins.coldPin :: pins.map SessionCorrespondence.pins)) (Loader.seed pins) := by
  let cold := SessionCorrespondence.pins BootPins.coldPin
  have split := InitializedSession.run_append startup [cold] (pins.map SessionCorrespondence.pins)
  have one : startup.run (Package.Components.typed 1) [cold] = startup.step (Package.Components.typed 1) cold := rfl
  rw [List.singleton_append, one, InitializedSession.cold_correct startup cold rfl] at split
  rw [split]
  have host : stateFromValues (InitializedSession.coldState 1 cold).frontend = ({} : Loader.State).host := by
    decide +kernel
  exact loader_run image (InitializedSession.coldState 1 cold) {} pins
    ⟨cold_related image, host, rfl, rfl⟩ noRaw certified

end Pinwheel.Hardware.StreamingReady.LoaderBoot
