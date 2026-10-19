import Pinwheel.Hardware.StreamingReady.Initialization
import Pinwheel.Hardware.Streaming.WarmReset
import Pinwheel.Hardware.StreamingReady.Package
import Pinwheel.Program.StreamingCustodySession

/-! Warm cancellation returns to an uninstalled loader boundary. It does not
pretend that the invalidated program remains a certified installed image. -/
namespace Pinwheel.Hardware.StreamingReady.WarmReset
open Pinwheel.Hardware Pinwheel.Program.Streaming
open Pinwheel.Hardware.Streaming
set_option linter.unusedSimpArgs false

def metadata (r : Values (Core.Register a)) : Initialization.Metadata :=
  {words := fun k => r (.word k), idle := ⟨r .idleLevels, r .idleEnabled⟩}

def runtime (r : Values (Core.Register a)) : Pinwheel.Program.Streaming.State a :=
  {pins := ⟨r .idleLevels, r .idleEnabled⟩, generation := r .generation, transfer := r .transfer}

theorem resetting (i : Values Core.Input) (r : Values (Core.Register a))
    (cold : i .initialize = 0) (command : i .command = 15) : Core.resetting.eval i r = 1 := by
  simp [Core.resetting, Core.cold, Core.warm, Core.cmd, Core.both, Core.either, Expr.eval, cold, command]

/-- Every raw core register is accounted for; the pre-reset state is arbitrary. -/
theorem warm_step_equal (i : Values Core.Input) (r : Values (Core.Register a))
    (cold : i .initialize = 0) (command : i .command = 15) (port : Core.Register a w) :
    (Core.circuit a).step i r port = (Streaming.Core.circuit a).step i r port := by
  have reset := resetting i r cold command
  have oldReset := Streaming.WarmReset.resetting i r cold command
  cases port <;> simp [Core.circuit,Streaming.Core.circuit,Circuit.step,Core.next,Streaming.Core.next,
    Core.clearedRuntime,Streaming.Core.clearedRuntime,Core.cold,Streaming.Core.cold,
    Core.nextRaw,Streaming.Core.nextRaw,Core.free,Streaming.Core.free,
    Core.writing,Streaming.Core.writing,Core.committing,Streaming.Core.committing,
    Core.starting,Streaming.Core.starting,Core.both,Streaming.Core.both,
    Core.either,Streaming.Core.either,Expr.eval,cold,reset,oldReset]
  done

theorem step_correct (i : Values Core.Input) (r : Values (Core.Register a))
    (cold : i .initialize = 0) (command : i .command = 15) (port : Core.Register a w) :
    (Core.circuit a).step i r port = Initialization.values (metadata r) (runtime r) port :=
  (warm_step_equal i r cold command port).trans (Streaming.WarmReset.step_correct i r cold command port)

theorem step_values (i : Values Core.Input) (r : Values (Core.Register a))
    (cold : i .initialize = 0) (command : i .command = 15) :
    @Circuit.step _ _ _ (Core.circuit a) i r = @Initialization.values a (metadata r) (runtime r) := by
  funext w port
  exact step_correct i r cold command port

theorem rejected_zero (i : Values Core.Input) (r : Values (Core.Register a))
    (cold : i .initialize = 0) (command : i .command = 15) :
    (Core.circuit a).observe i r .rejected = 0 := by
  have reset := resetting i r cold command
  simp [Core.circuit, Circuit.observe, Core.output, Core.rejected, Core.both, Expr.eval, reset]

def frontendInput (s : Package.State a) (pins : Package.Pins) : Host.Input :=
  HostCorrespondence.inputFromValues (s.frontendInputs (Package.Components.typed a) pins)

def frontendState (s : Package.State a) : Host.State := HostCorrespondence.stateFromValues s.frontend

/-- Whole-package warm reset exposes the actual projected frontend transition and
the uninstalled core metadata boundary, from arbitrary raw startup. -/
theorem package_step (s : Package.State a) (pins : Package.Pins)
    (cold : pins.initialize = 0) (command : (s.coreInputs (Package.Components.typed a) pins) .command = 15) :
    s.step (Package.Components.typed a) pins =
      ⟨HostCorrespondence.values (Host.step (frontendInput s pins) (frontendState s)),
        Initialization.values (metadata s.core) (runtime s.core)⟩ := by
  have front := HostCorrespondence.step_fromRaw (s.frontendInputs (Package.Components.typed a) pins) s.frontend
  have core := step_values (s.coreInputs (Package.Components.typed a) pins) s.core cold command
  change Streaming.Package.State.mk (@Circuit.step _ _ _ Frontend.circuit (s.frontendInputs (Package.Components.typed a) pins) s.frontend)
    (@Circuit.step _ _ _ (Core.circuit a) (s.coreInputs (Package.Components.typed a) pins) s.core) = _
  rw [front, core]
  rfl

theorem package_warm_status (s : Package.State a) (pins : Package.Pins)
    (cold : pins.initialize = 0) (command : (s.coreInputs (Package.Components.typed a) pins) .command = 15) :
    (frontendInput s pins).status.rejected = false := by
  have reject := rejected_zero (s.coreInputs (Package.Components.typed a) pins) s.core cold command
  change ((Core.circuit a).observe (s.coreInputs (Package.Components.typed a) pins) s.core .rejected).getLsbD 0 = false
  rw [reject]
  rfl

theorem projected_command (s : Package.State a) (pins : Package.Pins) (port : Core.Input w) :
    HostCorrespondence.commandValues ((frontendState s).command (frontendInput s pins)) port =
      (s.coreInputs (Package.Components.typed a) pins) port := by
  have front := HostCorrespondence.coreInput_eval (frontendInput s pins) (frontendState s) port
  have projected : Frontend.circuit.observe (s.frontendInputs (Package.Components.typed a) pins) s.frontend (.core port) =
      HostCorrespondence.commandValues ((frontendState s).command (frontendInput s pins)) port := by
    change (Frontend.coreInput port).eval (s.frontendInputs (Package.Components.typed a) pins) s.frontend = _
    simpa only [frontendInput, frontendState, HostCorrespondence.input_roundtrip,
      HostCorrespondence.state_roundtrip] using front
  exact projected.symm.trans (Streaming.Package.coreInput_independent pins s.frontend _ _ port)

theorem canonical_warm_clears_custody (s : Package.State a) (pins : Package.Pins)
    (cold : pins.initialize = 0) (command : (s.coreInputs (Package.Components.typed a) pins) .command = 15)
    (opcode : (frontendState s).opcode = 7#4) :
    (s.step (Package.Components.typed a) pins).frontend .exportData = 0 ∧
      (s.step (Package.Components.typed a) pins).frontend .exportStart = 0 ∧
      (s.step (Package.Components.typed a) pins).frontend .exportBits = 0 ∧
      (s.step (Package.Components.typed a) pins).frontend .ackOffset = 0 := by
  have sourceCommand : ((frontendState s).command (frontendInput s pins)).runtime.command = 15#4 :=
    (projected_command s pins .command).trans command
  have delivering : (frontendState s).delivering = true := by
    simp [Host.State.command, opcode] at sourceCommand
    exact sourceCommand
  have sourceCold : (frontendInput s pins).initialize = false := by
    change pins.initialize.getLsbD 0 = false
    rw [cold]
    rfl
  have clear : (frontendState s).clearingExport (frontendInput s pins).status = true := by
    simp [Host.State.clearingExport, delivering, opcode, package_warm_status s pins cold command]
  rw [package_step s pins cold command]
  simp [HostCorrespondence.values, Host.step, sourceCold, clear]

theorem owner_cancelled (i : Values Core.Input) (r : Values (Core.Register a))
    (cold : i .initialize = 0) (command : i .command = 15) :
    (Core.circuit a).step i r .phase = 0 ∧
      (Core.circuit a).step i r .valid = 0 ∧
      (Core.circuit a).step i r .written = 0 ∧
      (Core.circuit a).step i r .pending = 0 ∧
      (Core.circuit a).step i r .count = 0 ∧
      (Core.circuit a).step i r .generation = r .generation ∧
      (Core.circuit a).step i r .transfer = r .transfer := by
  simp [step_correct i r cold command, Initialization.values, Streaming.Initialization.values, metadata, runtime, Phase.code]

theorem runtime_free (r : Values (Core.Register a)) (input : Pinwheel.Program.Streaming.Input) :
    (runtime r).owned input = false ∧ (runtime r).drained = true := by
  simp [runtime, State.owned, Phase.busy, Phase.retained, State.drained, Queue.empty]

theorem package_step_correct (components : Package.Components a) (correct : Package.Correct components)
    (s : Package.State a) (pins : Package.Pins)
    (cold : pins.initialize = 0) (command : (s.coreInputs components pins) .command = 15) :
    s.step components pins =
      ⟨HostCorrespondence.values (Host.step (frontendInput s pins) (frontendState s)),
        Initialization.values (metadata s.core) (runtime s.core)⟩ := by
  rw [correct.eq_typed] at command ⊢
  exact package_step s pins cold command

end Pinwheel.Hardware.StreamingReady.WarmReset
