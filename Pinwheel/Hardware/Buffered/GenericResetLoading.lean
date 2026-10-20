import Pinwheel.Hardware.Buffered.I2cGeometry
import Pinwheel.Hardware.Buffered.GenericInstalledSram
import Pinwheel.Hardware.Buffered.LifecycleAdmission

/-! Both reset kinds reestablish an unknown accepted-upload ledger. SRAM cells
remain arbitrary; fresh coverage and accepted source uploads establish the next
certified resident image. Warm reset need not clear the physical arrays. -/
namespace Pinwheel.Hardware.Buffered.SramResetLoading
open Pinwheel.Hardware Pinwheel.Program

set_option backward.isDefEq.respectTransparency false in
theorem reset_graph (s : SramState.State) (i : Values Reactive.Input)
    (reset : Reactive.resetting.eval i s.core = 1) :
    SramCoverage.resetting.eval (s.inputs i) s.registers = 1 := by
  simpa only [SramCoverage.resetting, SramCoverage.control_correct,
    SharedBranches.resetting, SharedBranches.raw_correct, Reactive.resetting,
    Reactive.cold, Reactive.warm, Reactive.cmd, Reactive.both, Reactive.either,
    Expr.eval, SramCoverage.baseInput, SramState.State.inputs] using reset

theorem established_reset (s : SramState.State) (i : Values Reactive.Input)
    (reset : Reactive.resetting.eval i s.core = 1) :
    SramCorrespondence.Established (s.step i) SramLoading.Ledger.initial := by
  have valid : (s.step i).registers (.core .valid) = 0 := (Lifecycle.reset_ownership s i reset).1
  have masks := SramCoverage.masks_reset (s.inputs i) s.registers (reset_graph s i reset)
  refine ⟨SramLoading.agrees_initial _, SramLoading.coherent_initial, ?_, ?_, ?_⟩
  · constructor
    all_goals simp [SramState.State.step, masks.1, masks.2]
  · intro asserted
    exact False.elim ((by decide : (0 : BitVec 1) ≠ 1) (valid.symm.trans asserted))
  · intro asserted
    exact False.elim ((by decide : (0 : BitVec 1) ≠ 1) (valid.symm.trans asserted))

theorem ready_reset (s : SramState.State) (i : Values Reactive.Input)
    (reset : Reactive.resetting.eval i s.core = 1) :
    SramCorrespondence.ReadyWhenValid (s.step i) SramLoading.Ledger.initial := by
  intro asserted
  change (s.step i).core .valid = 1 at asserted
  rw [(Lifecycle.reset_ownership s i reset).1] at asserted
  contradiction

end Pinwheel.Hardware.Buffered.SramResetLoading
