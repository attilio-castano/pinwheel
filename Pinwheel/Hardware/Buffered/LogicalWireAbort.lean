import Pinwheel.Hardware.Buffered.LogicalWireInitialized
import Pinwheel.Hardware.Buffered.SerialWirePrefix

/-! Composable interruptions inside sampled request/read frames. A raw prefix
clocks the same source through every actual quiet controller input; the physical
cold edge then applies ordinary reset to those exact logical buffers. Reload
and arbitrary later trace chunks remain in the same actual pin recurrence. -/
namespace Pinwheel.Hardware.Buffered.LogicalWire.Interrupted
open Pinwheel.Hardware Pinwheel.Program Refinement Serial.Frames
open SerialSourceSession (Frontend)

inductive Event :
    SerialPackage.State → Cursor → Frontend → List SerialPackage.Pins →
      SerialPackage.State → Cursor → Frontend → Type where
  | segment (trace : LogicalWire.Trace before cursor frontend pins after next nextFrontend) :
      Event before cursor frontend pins after next nextFrontend
  | coldAbort (cursor : Cursor) (frontend : Frontend) (rawPrefix : List SerialPackage.Pins)
      (quiet : ∀ input ∈ before.commands rawPrefix, SpiCircuit.Quiet input)
      (coldPin : SerialPackage.Pins) (cold : coldPin.cold = true) (idle : coldPin.csn = true)
      (loading : SerialUpload.Loading ((before.run rawPrefix).step coldPin)) :
      Event before cursor frontend (rawPrefix ++ coldPin :: loading.pins) loading.after
        (.free (LogicalSession.resetLogical (cursor.advance rawPrefix).logical)
          (loading.after.controller.core .transfer).toNat) .available

def Event.abortRequest (request : SerialWire.Request before) (cursor : Cursor) (count : Nat)
    (coldPin : SerialPackage.Pins) (cold : coldPin.cold = true) (idle : coldPin.csn = true)
    (sequence : Nat → BitVec 16 := BitVec.ofNat 16) (raw : BitVec 2 := 0) :
    let rawPrefix := request.pins.take count
    let loading := SerialUpload.concreteLoading ((before.run rawPrefix).step coldPin)
      (SerialUpload.cold_available _ coldPin cold idle) sequence raw
    Event before cursor .available (rawPrefix ++ coldPin :: loading.pins) loading.after
      (.free (LogicalSession.resetLogical (cursor.advance rawPrefix).logical)
        (loading.after.controller.core .transfer).toNat) .available :=
  .coldAbort cursor .available (request.pins.take count) (request.quiet_prefix count)
    coldPin cold idle _

def Event.abortRead (attempt : SerialSourceSession.Attempt before) (cursor : Cursor) (count : Nat)
    (coldPin : SerialPackage.Pins) (cold : coldPin.cold = true) (idle : coldPin.csn = true)
    (sequence : Nat → BitVec 16 := BitVec.ofNat 16) (raw : BitVec 2 := 0) :
    let rawPrefix := attempt.pins.take count
    let loading := SerialUpload.concreteLoading ((before.run rawPrefix).step coldPin)
      (SerialUpload.cold_available _ coldPin cold idle) sequence raw
    Event before cursor .ready (rawPrefix ++ coldPin :: loading.pins) loading.after
      (.free (LogicalSession.resetLogical (cursor.advance rawPrefix).logical)
        (loading.after.controller.core .transfer).toNat) .available :=
  .coldAbort cursor .ready (attempt.pins.take count) (attempt.quiet_prefix count)
    coldPin cold idle _

theorem Event.run_pins (event : Event before cursor frontend pins after next nextFrontend) :
    before.run pins = after := by
  cases event with
  | segment trace => exact trace.run_pins
  | coldAbort rawPrefix quiet coldPin cold idle loading =>
    have loaded := (SerialUpload.cold_install (before.run rawPrefix) coldPin cold idle loading).2.2.2.2.2.2
    change List.foldl SerialPackage.State.step before (rawPrefix ++ coldPin :: loading.pins) = _
    rw [List.foldl_append]
    exact loaded

theorem Event.preserves (event : Event before cursor frontend pins after next nextFrontend)
    (initial : Valid before cursor frontend) : Valid after next nextFrontend := by
  cases event with
  | segment trace => exact trace.preserves initial
  | coldAbort rawPrefix quiet coldPin cold idle loading =>
    obtain ⟨installed,phase,retained,_,_,available,_⟩ :=
      SerialUpload.cold_install (before.run rawPrefix) coldPin cold idle loading
    exact ⟨available,installed,⟨rfl,phase,retained,rfl⟩⟩

def Event.Observed (event : Event before cursor frontend pins after next nextFrontend) : Prop :=
  match event with
  | .segment trace => trace.Observed
  | @Event.coldAbort _ cursor _ rawPrefix _ _ _ _ loading =>
    (cursor.advance rawPrefix).Holds (before.run rawPrefix) ∧
      Transfer.step capacity (cursor.advance rawPrefix).logical .reset =
        ⟨LogicalSession.resetLogical (cursor.advance rawPrefix).logical,.reset⟩ ∧
      (LogicalSession.resetLogical (cursor.advance rawPrefix).logical).epoch =
        (cursor.advance rawPrefix).logical.epoch + 1 ∧
      (LogicalSession.resetLogical (cursor.advance rawPrefix).logical).nextSequence = 1 ∧
      loading.after.controller.core .generation = 1 ∧ loading.after.controller.core .transfer = 0

theorem Event.observed (event : Event before cursor frontend pins after next nextFrontend)
    (initial : Valid before cursor frontend) : event.Observed := by
  cases event with
  | segment trace => exact trace.observed initial
  | coldAbort rawPrefix quiet coldPin cold idle loading =>
    obtain ⟨_,_,_,generation,transfer,_,_⟩ :=
      SerialUpload.cold_install (before.run rawPrefix) coldPin cold idle loading
    exact ⟨Cursor.quiet_run initial.2 rawPrefix quiet,rfl,rfl,rfl,generation,transfer⟩

inductive Trace :
    SerialPackage.State → Cursor → Frontend → List SerialPackage.Pins →
      SerialPackage.State → Cursor → Frontend → Type where
  | nil : Trace before cursor frontend [] before cursor frontend
  | cons (event : Event before cursor frontend first middle next nextFrontend)
      (rest : Trace middle next nextFrontend more after final finalFrontend) :
      Trace before cursor frontend (first ++ more) after final finalFrontend

theorem Trace.run_pins (trace : Trace before cursor frontend pins after final finalFrontend) :
    before.run pins = after := by
  induction trace with
  | nil => rfl
  | cons event rest ih =>
    simp only [SerialPackage.State.run,List.foldl_append]
    change SerialPackage.State.run (SerialPackage.State.run _ _) _ = _
    rw [event.run_pins]
    exact ih

theorem Trace.preserves (trace : Trace before cursor frontend pins after final finalFrontend)
    (initial : Valid before cursor frontend) : Valid after final finalFrontend := by
  induction trace with
  | nil => exact initial
  | cons event rest ih => exact ih (event.preserves initial)

def Trace.Observed : Trace before cursor frontend pins after final finalFrontend → Prop
  | .nil => True
  | .cons event rest => event.Observed ∧ rest.Observed

theorem Trace.observed (trace : Trace before cursor frontend pins after final finalFrontend)
    (initial : Valid before cursor frontend) : trace.Observed := by
  induction trace with
  | nil => trivial
  | cons event rest ih => exact ⟨event.observed initial,ih (event.preserves initial)⟩

/-- Any finite number of wire-session chunks and interior-frame cold aborts
share one actual pin history and one carried ordinary logical owner state. -/
theorem Trace.session (trace : Trace before cursor frontend pins after final finalFrontend)
    (initial : Valid before cursor frontend) :
    before.run pins = after ∧ Valid after final finalFrontend ∧ trace.Observed :=
  ⟨trace.run_pins,trace.preserves initial,trace.observed initial⟩

theorem initialized_session (before : SerialPackage.State) (previous : Transfer.State)
    (coldPin : SerialPackage.Pins) (cold : coldPin.cold = true) (idle : coldPin.csn = true)
    (loading : SerialUpload.Loading (before.step coldPin))
    (trace : Trace loading.after
      (.free (LogicalSession.resetLogical previous) (loading.after.controller.core .transfer).toNat)
      .available pins after final finalFrontend) :
    before.run ((coldPin :: loading.pins) ++ pins) = after ∧
      Transfer.step capacity previous .reset = ⟨LogicalSession.resetLogical previous,.reset⟩ ∧
      Valid after final finalFrontend ∧ trace.Observed := by
  obtain ⟨installed,phase,retained,_,_,available,run⟩ :=
    SerialUpload.cold_install before coldPin cold idle loading
  have aligned : LogicalSession.Aligned loading.after.controller
      (LogicalSession.resetLogical previous) (loading.after.controller.core .transfer).toNat :=
    ⟨rfl,phase,retained,rfl⟩
  have result := trace.session ⟨available,installed,aligned⟩
  refine ⟨?_,rfl,result.2⟩
  change List.foldl SerialPackage.State.step before ((coldPin :: loading.pins) ++ pins) = after
  rw [List.foldl_append]
  exact (congrArg (fun current => current.run pins) run).trans result.1

end Pinwheel.Hardware.Buffered.LogicalWire.Interrupted
