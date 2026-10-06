import Pinwheel.Hardware.Storage.PairedStreamBootstrap
import Pinwheel.Hardware.HostResultBuffer

/-! Disabled reloads cannot generate execution results. The observer still
performs its actual consume, clear and external-flush events on old packets. -/
namespace Pinwheel.Hardware.Storage.PairedStreamDormant
open Pinwheel.Hardware PairedController
open PairedCoverage (graph_equations graphInputs)
set_option backward.isDefEq.respectTransparency false

theorem mode_next (s : PairedCoverage.Tracked) (i : Loader.Machine.Inputs)
    (mode : s.registers .mode = 0) (command : i.command ≠ 5) :
    (PairedCoverage.advance s i.values).registers .mode = 0 := by
  simp only [BitVec.ofNat_eq_ofNat] at command
  simp only [PairedCoverage.advance, Circuit.step, body, PairedController.next,
    PairedRunning.nextMode_wire _ _ (graph_equations i.values s), nextModeExpr, Expr.eval, mode]
  simp [PairedControl.ending_wire _ _ (graph_equations i.values s), endingExpr,
    PairedRunning.entering_wire _ _ (graph_equations i.values s), enteringExpr,
    PairedRunning.start_wire _ _ (graph_equations i.values s), startExpr,
    PairedRunning.dispatch_wire _ _ (graph_equations i.values s), dispatchExpr,
    PairedRunning.busy_wire _ _ (graph_equations i.values s), busyExpr, both, either, cmd,
    Expr.eval, mode, show graphInputs i.values s (.base .command) = i.command from rfl, command]
  done

theorem core_mode (memory : Memory.SinglePort.Contract S 9 64)
    (s : PairedStreamPackage.State S) :
    PairedStreamPackage.coreOutput memory s (.core (.state .mode)) = s.core.1 .mode := rfl

theorem no_arrival (memory : Memory.SinglePort.Contract S 9 64)
    (s : PairedStreamPackage.State S) (mode : s.core.1 .mode = 0) :
    HostResultBuffer.arrival (PairedStreamPackage.coreOutput memory s) s.result = none := by
  simp [HostResultBuffer.arrival, HostResult.arriving, core_mode, mode]
  done

def Dormant (memory : Memory.SinglePort.Contract S 9 64)
    (s : PairedStreamPackage.State S) (storage : PairedStreamOwnership.Tracked) : Prop :=
  PairedStreamBootstrap.Related memory s storage ∧ storage.enabled = false ∧ storage.inner.registers .mode = 0

theorem dormant_next (memory : Memory.SinglePort.Contract S 9 64)
    (s : PairedStreamPackage.State S) (storage : PairedStreamOwnership.Tracked)
    (h : Dormant memory s storage) (pins : Chip.Pins)
    (start : (PairedStreamPackage.rawInput s).command ≠ 5)
    (arm : (PairedStreamPackage.rawInput s).command ≠ 6) :
    Dormant memory ((PairedStreamPackage.interpreted memory).step pins s)
      (PairedStreamOwnership.advance storage (PairedStreamPackage.rawInput s)) := by
  have pass := PairedStreamOwnership.disabled_pass storage (PairedStreamPackage.rawInput s) h.2.1 arm
  refine ⟨PairedStreamBootstrap.related_next memory s storage h.1 pins, pass.2, ?_⟩
  simpa only [PairedStreamOwnership.advance, pass.1] using
    mode_next storage.inner (PairedStreamPackage.rawInput s) h.2.2 start
  done

theorem dormant_no_arrival (memory : Memory.SinglePort.Contract S 9 64)
    (s : PairedStreamPackage.State S) (storage : PairedStreamOwnership.Tracked)
    (h : Dormant memory s storage) :
    HostResultBuffer.arrival (PairedStreamPackage.coreOutput memory s) s.result = none := by
  exact no_arrival memory s ((congrArg (fun pair : Values Register × Memory.Sram.State 9 64 =>
    pair.1 .mode) h.1.1).trans h.2.2)

def silentCommand (pins : Chip.Pins) (host : HostResult.State) : HostResultBuffer.Retained.Command α :=
  if HostResult.resetting pins host then .reset else
    .cycle none (HostResult.consuming host) (HostResult.clearing host)

theorem dormant_command (memory : Memory.SinglePort.Contract S 9 64)
    (s : PairedStreamPackage.State S) (storage : PairedStreamOwnership.Tracked)
    (h : Dormant memory s storage) (pins : Chip.Pins) :
    HostResultBuffer.command pins (PairedStreamPackage.coreOutput memory s) s.result =
      silentCommand pins s.result := by
  simp only [HostResultBuffer.command, silentCommand, dormant_no_arrival memory s storage h]
  done

def LoaderHistory (history : List Loader.Machine.Inputs) : Prop :=
  ∀ i ∈ history, i.command ≠ 5 ∧ i.command ≠ 6

theorem dormant_run (memory : Memory.SinglePort.Contract S 9 64)
    (s : PairedStreamPackage.State S) (storage : PairedStreamOwnership.Tracked)
    (h : Dormant memory s storage) (pins : List Chip.Pins)
    (commands : LoaderHistory (Chip.consumed s.adapters pins)) :
    Dormant memory ((PairedStreamPackage.interpreted memory).run s pins)
      (PairedStreamBootstrap.run storage (Chip.consumed s.adapters pins)) := by
  induction pins generalizing s storage with
  | nil => exact h
  | cons i rest ih =>
    simp only [PairedHost.consumed_cons, LoaderHistory, List.forall_mem_cons] at commands
    simpa only [Timed.Component.run, PairedStreamBootstrap.run, PairedHost.consumed_cons,
      List.foldl_cons, PairedStreamPackage.rawInput, PairedStreamPackage.interpreted] using
      ih ((PairedStreamPackage.interpreted memory).step i s)
        (PairedStreamOwnership.advance storage (PairedStreamPackage.rawInput s))
        (dormant_next memory s storage h i commands.1.1 commands.1.2) commands.2
  done

def controls (memory : Memory.SinglePort.Contract S 9 64) :
    PairedStreamPackage.State S → List Chip.Pins → List (HostResultBuffer.Retained.Command α)
  | _, [] => []
  | s, pins :: rest => silentCommand pins s.result ::
    controls memory ((PairedStreamPackage.interpreted memory).step pins s) rest

theorem controls_no_arrivals (memory : Memory.SinglePort.Contract S 9 64)
    (s : PairedStreamPackage.State S) (pins : List Chip.Pins) :
    HostResultBuffer.Retained.arrivals (controls memory s pins :
      List (HostResultBuffer.Retained.Command α)) = [] := by
  induction pins generalizing s with
  | nil => rfl
  | cons i rest ih =>
    change (silentCommand i s.result : HostResultBuffer.Retained.Command α).arrival.toList ++
      HostResultBuffer.Retained.arrivals
        (controls memory ((PairedStreamPackage.interpreted memory).step i s) rest) = []
    simp [silentCommand, HostResultBuffer.Retained.Command.arrival, ih]
    cases HostResult.resetting i s.result <;> simp
  done

theorem delivered_no_start {history : List Loader.Machine.Inputs}
    {commands : List (BitVec 3 × BitVec 64)}
    (delivery : Loader.Machine.Delivers history commands) (hc : ∀ c ∈ commands, c.1 ≠ 5) :
    ∀ i ∈ history, i.command ≠ 5 := by
  induction delivery with
  | nil => simp
  | quiet hq _ ih =>
    simp only [List.forall_mem_cons]
    exact ⟨by simp [hq.2.2], ih hc⟩
  | command carries _ ih =>
    simp only [List.forall_mem_cons] at hc ⊢
    refine ⟨?_, ih hc.2⟩
    rw [carries.2.2.1]
    split <;> simp_all
    done

theorem upload_history (image : PairedImage.Image) (d₀ d₁ : BitVec 64)
    (history : List Loader.Machine.Inputs)
    (delivery : Loader.Machine.Delivers history
      (Loader.Machine.uploadCommands (PairedImage.upload image) d₀ d₁)) : LoaderHistory history := by
  exact fun i hi => ⟨delivered_no_start delivery (by simp [Loader.Machine.uploadCommands]; grind) i hi,
    PairedStreamOwnership.delivered_no_arm delivery (by simp [Loader.Machine.uploadCommands]; grind) i hi⟩

end Pinwheel.Hardware.Storage.PairedStreamDormant
