import Pinwheel.Hardware.StreamingReady.LoaderBoot
import Pinwheel.Hardware.StreamingReady.I2CReadSuccess
import Pinwheel.Program.StreamingI2CReadPremises

/-! The I²C read-completion theorem is not vacuous: from any power-up state of
the typed package, the checked boot upload, the scenario host and the scenario
target satisfy every hypothesis of `I2CReadSuccess.completed_from_service`, so
the 64-byte read completes and drains on actual package pins. -/
namespace Pinwheel.Hardware.StreamingReady.I2CReadWitness
open Pinwheel.Program Pinwheel.Program.StreamingReady Pinwheel.Program.StreamingI2CReadWitness
open Pinwheel.Hardware.StreamingReady.InitializedCustody

abbrev image := i2cImage profile

def afterBoot (startup : Package.State 1) : Package.State 1 :=
  startup.run (Package.Components.typed 1)
    (SessionCorrespondence.pins Streaming.BootPins.coldPin :: bootPins.map SessionCorrespondence.pins)

def beforeStart : List Session.Pins := SessionService.clocks (trafficOf initialLoop) startCut

def startPin : Session.Pins := startLoop.pin

/-- The package just after START is accepted. -/
def started (startup : Package.State 1) : Package.State 1 :=
  ((afterBoot startup).run (Package.Components.typed 1) (beforeStart.map SessionCorrespondence.pins)).step
    (Package.Components.typed 1) (SessionCorrespondence.pins startPin)

set_option maxRecDepth 18000 in
theorem boot (startup : Package.State 1) :
    BootCorrespondence.Initialized image (afterBoot startup) seed := by
  have noRaw : ∀ pin ∈ bootPins, pin.rawInputs = 0 := by
    have checked : (bootPins.all fun pin => pin.rawInputs == 0) = true := by decide +kernel
    intro pin member
    exact beq_iff_eq.mp (List.all_eq_true.mp checked _ member)
  exact LoaderBoot.initialized image bootPins noRaw
    (Pinwheel.Program.Streaming.BootPins.check_sound _ _ _ _ _ _ (by decide +kernel)) startup

theorem ready_eq : seed.run program false beforeStart = startLoop.s := run_clocks initialLoop startCut

/-- START is accepted on the package, and the session is then at `origin`. -/
theorem reached (startup : Package.State 1) : Reached image (started startup) origin.s {} := by
  have init := boot startup
  obtain ⟨beforeRuntime, startRuntime, three, can, _⟩ := preStart_parts
  have readyEq := initialized_run_eq image (afterBoot startup) seed init beforeStart (by decide) beforeRuntime
  rw [ready_eq] at readyEq
  have accepted : ActualStart ((afterBoot startup).run (Package.Components.typed 1)
      (beforeStart.map SessionCorrespondence.pins)) startPin := by
    rw [readyEq]
    unfold ActualStart
    rw [SessionCorrespondence.core_inputs]
    change Core.starting.eval (Pinwheel.Hardware.Streaming.HostCorrespondence.commandValues
        (startLoop.s.command startLoop.pin)) (SourceRefinement.values (Initialization.compiledImage image) startLoop.s.core) = 1
    rw [InputCorrespondence.command_eval _ InputCorrespondence.starting_runtime,
      SourceRefinement.starting_eval _ _ _ startRuntime]
    simp [three, can]
  rw [← ready_eq] at startRuntime
  have done := started_run image (afterBoot startup) seed init beforeStart startPin [] (by decide)
    beforeRuntime startRuntime accepted trivial
  rw [ready_eq] at done
  rw [origin_s]
  exact done

/-- The engine state START leaves behind, and the START input itself. -/
theorem started_core : origin.s.core =
    startLoop.s.core.start program (startLoop.s.command startLoop.pin).runtime := by
  obtain ⟨_, startRuntime, three, can, _⟩ := preStart_parts
  rw [origin_s]
  exact Session.State.core_admitted_start _ _ _ _ startRuntime (by simp [three, can])

/-- The target's drive resolves against the package's actual pads. -/
theorem connection (startup : Package.State 1) (edges : Nat) :
    I2CReadSession.PublicConnection (started startup) (SessionService.clocks traffic edges) peer := by
  intro k lt
  have pinsLen : (SessionService.clocks traffic edges).length = edges := by simp [SessionService.clocks]
  rw [pinsLen] at lt
  have runtime : Session.RuntimeTrace program false origin.s (SessionService.clocks traffic edges) :=
    (runtimeTrace_loop origin edges (fun k _ => (good_parts (good_at k)).1)).1
  rw [I2CReadSession.public_trace _ origin.s {} (reached startup) _ (by decide) runtime,
    ← I2CReadSession.runtime_raw_at_for profile origin.s _ k]
  change ((origin.s.runtimeInputs program false (SessionService.clocks traffic edges))[k]?).map _ =
    ((pinTrace program origin.s.core (origin.s.runtimeInputs program false
      (SessionService.clocks traffic edges)))[k]?).map _
  rw [inputs_eq, inputsOf_get origin lt, pinTrace_get _ _ k (by rw [inputsOf_length]; exact Nat.le_of_lt lt),
    inputsOf_take origin (Nat.le_of_lt lt), run_inputsOf]
  rfl

theorem service : I2CReadSuccess.ServiceAssumptions profile origin.s traffic payload peer where
  runtime := runtime
  unreleased := unreleased
  deadlines := deadlines
  credits := fun n _ => credits n
  peerSetup := peerSetup
  hostPrefix := hostPrefix

theorem drain : I2CReadSuccess.DrainService profile origin.s traffic := drainService

/-- Every hypothesis of the completion theorem holds for the scenario, from
any power-up state. -/
theorem premises (startup : Package.State 1) :
    Reached image (started startup) origin.s {} ∧
    origin.s.core = startLoop.s.core.start program (startLoop.s.command startLoop.pin).runtime ∧
    (startLoop.s.command startLoop.pin).runtime.startCount = 585#16 ∧
    payload.length = 64 ∧
    I2CReadSuccess.ServiceAssumptions profile origin.s traffic payload peer ∧
    (∀ edges, I2CReadSession.PublicConnection (started startup) (SessionService.clocks traffic edges) peer) ∧
    I2CReadSuccess.DrainService profile origin.s traffic :=
  ⟨reached startup, started_core, preStart_parts.2.2.2.2, by decide, service, connection startup, drain⟩

/-- The completion theorem's conclusion, instantiated: the read completes on
the package pins, the target's payload is exported, and RELEASE is admitted. -/
theorem completes (startup : Package.State 1) :
    ∃ edges drainPins releasePin, I2CReadSuccess.Result profile (started startup) origin.s
      (SessionService.clocks traffic edges) drainPins releasePin payload peer :=
  I2CReadSuccess.completed_from_service profile (started startup) origin.s (reached startup)
    startLoop.s.core (startLoop.s.command startLoop.pin).runtime started_core preStart_parts.2.2.2.2
    traffic payload (by decide) peer (by decide) service (connection startup) drain

end Pinwheel.Hardware.StreamingReady.I2CReadWitness
