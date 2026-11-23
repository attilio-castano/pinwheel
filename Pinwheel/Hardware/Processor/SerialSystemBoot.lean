import Pinwheel.Hardware.Processor.SerialSystemCircuitProofs

namespace Pinwheel.Hardware.Processor.SerialSystemCircuit

open SerialSystemInterface
set_option backward.isDefEq.respectTransparency false

/-- During loading the UART is held in reset. Its completion, arrival, data and
framing-error feedback to the processor are all zero. -/
def loaderPins (i : Values (Input aw)) : Values (LoadableSystem.Input aw)
  | _, .left (.at ⟨0,_⟩) => i reset
  | _, .left (.at ⟨1,_⟩) => i gpio
  | _, .left (.at ⟨2,_⟩) | _, .left (.at ⟨3,_⟩) | _, .left (.at ⟨4,_⟩) | _, .left (.at ⟨5,_⟩) => 0
  | _, .left (.at ⟨k+6,h⟩) => False.elim (by change k+6 < 6 at h; omega)
  | _, .right (.at ⟨0,_⟩) => i mode
  | _, .right (.at ⟨1,_⟩) => i valid
  | _, .right (.at ⟨2,_⟩) => i address
  | _, .right (.at ⟨3,_⟩) => i data
  | _, .right (.at ⟨k+4,h⟩) => False.elim (by change k+4 < 4 at h; omega)

variable (layout : AddressMap.Layout rw aw) (rom : SystemModel.Rom rw)
  (romFits : rw ≤ 30) (ramFits : aw ≤ 30) (d : Uart.Timing)

private theorem serial_held (i : Values (Input aw)) (s : Values (Register aw d))
    (h : i reset = 1 ∨ i mode = 1) : serialPins layout i s SerialInterface.reset = 1 := by
  rw [serial_reset]
  rcases BitVec.eq_zero_or_eq_one (i reset) with hr | hr <;> simp_all

private theorem loading_pins (i : Values (Input aw)) (s : Values (Register aw d)) (hm : i mode = 1) :
    @Eq (Values (LoadableSystem.Input aw)) (loadablePins layout d i s) (loaderPins i) := by
  have feedback {b : Nat} (o : Uart.Physical.Output b) :
      (serialOutput layout d (.right o)).eval i s = SerialCircuit.resetValues (.right o) :=
    (serialOutput_eval layout d i s _).trans
      (SerialCircuit.reset_outputs _ _ (serial_held layout d i s (.inr hm)) _)
  funext b p
  match b,p with
  | _, .left (.at ⟨0,_⟩) | _, .left (.at ⟨1,_⟩) => rfl
  | _, .left (.at ⟨2,_⟩) => exact feedback Uart.Physical.txComplete
  | _, .left (.at ⟨3,_⟩) => exact feedback Uart.Physical.rxValid
  | _, .left (.at ⟨4,_⟩) => exact feedback Uart.Physical.rxData
  | _, .left (.at ⟨5,_⟩) => exact feedback Uart.Physical.framingError
  | _, .left (.at ⟨k+6,h⟩) => exact False.elim (by change k+6 < 6 at h; omega)
  | _, .right (.at ⟨0,_⟩) | _, .right (.at ⟨1,_⟩) | _, .right (.at ⟨2,_⟩) | _, .right (.at ⟨3,_⟩) => rfl
  | _, .right (.at ⟨k+4,h⟩) => exact False.elim (by change k+4 < 4 at h; omega)

private theorem serial_recovery (i : Values (Input aw)) (s : Values (Register aw d))
    (held : i reset = 1 ∨ i mode = 1) :
    let next : Values (Register aw d) := (circuit layout rom romFits ramFits d).step i s
    SerialCircuit.Valid d (serialState next) ∧ (view next).uart = Uart.initial := by
  have hr := serial_held layout d i s held
  constructor
  · dsimp only
    rw [serial_state_step]
    exact SerialCircuit.reset_valid _ _ hr
  · change Uart.Structural.view (uartState ((circuit layout rom romFits ramFits d).step i s)) = _
    rw [uart_state_step]
    exact congrArg SerialModel.State.uart (SerialCircuit.reset_view _ _ hr)

def resetCertificate : (implementation layout rom romFits ramFits d).Reset reset where
  initial := fun s => SerialSystemModel.initial ((view s).system.ram.memory.contents) ((view s).system.ram.memory.q)
  reset_valid i s h := by
    constructor
    · change SystemCircuit.Valid layout rom (systemState _)
      rw [system_state_step]
      exact LoadableSystem.reset_valid layout rom romFits ramFits _ _ h
    · exact (serial_recovery layout rom romFits ramFits d i s (.inl h)).1
  reset_view i s h := by
    change SerialSystemModel.State.mk _ _ = _
    congr 1
    · rw [system_state_step]
      exact LoadableSystem.reset_view layout rom romFits ramFits _ _ h
    · exact (serial_recovery layout rom romFits ramFits d i s (.inl h)).2

theorem trace_after_reset (i : Values (Input aw)) (s : Values (Register aw d))
    (hr : i reset = 1) (traffic : List (Values (Input aw))) :
    (circuit layout rom romFits ramFits d).component.trace
      ((circuit layout rom romFits ramFits d).step i s) traffic =
      (spec layout rom d).trace
        (SerialSystemModel.initial (view s).system.ram.memory.contents (view s).system.ram.memory.q) traffic :=
  (resetCertificate layout rom romFits ramFits d).trace_after_reset
    (implementation layout rom romFits ramFits d) reset i s hr traffic

/-- All seven external pins are available to the caller. Only accepted loader
writes constrain the image, and every address must have an accepted write. -/
abbrev ImageWrites (image : BitVec aw → BitVec 32) (loading : List (Values (Input aw))) :=
  LoadableSystem.ImageWrites image (loading.map (@loaderPins aw))

abbrev Covers (loading : List (Values (Input aw))) :=
  LoadableSystem.Covers (loading.map (@loaderPins aw))

private theorem system_run_loading (s : Values (Register aw d)) (loading : List (Values (Input aw)))
    (held : ∀ i ∈ loading, i mode = 1) :
    @Eq (Values (LoadableSystem.Register aw))
      (systemState ((circuit layout rom romFits ramFits d).component.run s loading))
      ((LoadableSystem.circuit layout rom romFits ramFits).component.run
        (systemState s) (loading.map (@loaderPins aw))) := by
  induction loading generalizing s with
  | nil => rfl
  | cons i rest ih =>
    apply (ih ((circuit layout rom romFits ramFits d).step i s)
      (fun j hj => held j (List.mem_cons_of_mem _ hj))).trans
    rw [system_state_step, loading_pins layout d i s (held i List.mem_cons_self)]
    rfl

private theorem serial_run_loading (s : Values (Register aw d)) (loading : List (Values (Input aw)))
    (nonempty : loading ≠ []) (held : ∀ i ∈ loading, i mode = 1) :
    let after : Values (Register aw d) := (circuit layout rom romFits ramFits d).component.run s loading
    SerialCircuit.Valid d (serialState after) ∧ (view after).uart = Uart.initial := by
  induction loading generalizing s with
  | nil => contradiction
  | cons i rest ih =>
    cases rest with
    | nil => exact serial_recovery layout rom romFits ramFits d i s (.inr (held i List.mem_cons_self))
    | cons j tail => exact ih _ (by simp) (fun k hk => held k (List.mem_cons_of_mem _ hk))

theorem trace_after_loading (s : Values (Register aw d)) (loading traffic : List (Values (Input aw)))
    (held : ∀ i ∈ loading, i mode = 1) (image : BitVec aw → BitVec 32)
    (writes : ImageWrites image loading) (covers : Covers loading) :
    (circuit layout rom romFits ramFits d).component.trace
      ((circuit layout rom romFits ramFits d).component.run s loading) traffic =
      (spec layout rom d).trace (SerialSystemModel.initial image (s (system LoadableSystem.q))) traffic := by
  have nonempty := LoadableSystem.covers_nonempty _ covers
  have modes : ∀ i ∈ loading.map (@loaderPins aw), i LoadableSystem.mode = 1 := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    exact held j hj
  have serial := serial_run_loading layout rom romFits ramFits d s loading (by simpa using nonempty) held
  apply (implementation layout rom romFits ramFits d).refinement.trace_eq
  constructor
  · refine ⟨?_, serial.1⟩
    change SystemCircuit.Valid layout rom (systemState _)
    rw [system_run_loading layout rom romFits ramFits d s loading held]
    exact LoadableSystem.run_loading_valid layout rom romFits ramFits _ _ nonempty modes
  · change SerialSystemModel.State.mk _ _ = _
    congr 1
    · rw [system_run_loading layout rom romFits ramFits d s loading held]
      exact LoadableSystem.complete_image layout rom romFits ramFits _ _ modes image writes covers
    · exact serial.2

end Pinwheel.Hardware.Processor.SerialSystemCircuit
