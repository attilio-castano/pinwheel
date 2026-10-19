import Pinwheel.Hardware.StreamingUART.Session
import Pinwheel.Program.StreamingUARTFrameResults

/-! The public UART wire drives an initialized typed package. The host remains
deselected throughout the autonomous frame; all engine clocks are retained. -/
namespace Pinwheel.Hardware.StreamingUART.Frame
open Pinwheel.Program.StreamingReady
open Pinwheel.Program.StreamingUART
set_option linter.unusedSimpArgs false

def incoming (raw : Nat → BitVec 2) (n : Nat) : Input := {rawInputs := raw n}
def pins (raw : Nat → BitVec 2) (edges : Nat) : List Pinwheel.Program.StreamingReady.Session.Pins :=
  (List.range edges).map (fun n => {rawInputs := raw n})

theorem quiet (raw : Nat → BitVec 2) (n : Nat) : QuietTiming.Quiet (incoming raw n) :=
  ⟨rfl,rfl,rfl,rfl⟩

theorem pins_idle (raw : Nat → BitVec 2) (edges : Nat) : ∀ pin ∈ pins raw edges,HostQuiet.Pins pin := by
  intro pin member
  simp only [pins,List.mem_map] at member
  rcases member with ⟨n,_,rfl⟩
  exact ⟨rfl,rfl,rfl⟩

theorem inputs_map (raw : Nat → BitVec 2) (edges : Nat) :
    (pins raw edges).map (fun pin => ({rawInputs := pin.rawInputs} : Input)) =
      FrameSamples.clocks (incoming raw) 0 edges := by
  simp only [pins,FrameSamples.clocks,List.map_map,Function.comp_def,Nat.zero_add,incoming]

structure Reached (rate : Fin 3) (actual : Session.Actual a)
    (s : Pinwheel.Program.StreamingReady.Session.State a) : Prop where
  package : actual = Pinwheel.Hardware.StreamingReady.SessionCorrespondence.values
    (Pinwheel.Hardware.StreamingReady.Initialization.compiledImage (image (Boot.profile rate))) s
  custody : ∃ trace : BitTrace, s.Custody trace ∧ s.FreeExport

def actualRun (rate : Fin 3) (startup : Session.Actual a) (raw : Nat → BitVec 2) (edges : Nat) : Session.Actual a :=
  (Session.armedActual rate startup).run (Pinwheel.Hardware.StreamingReady.Package.Components.typed a)
    ((pins raw edges).map Pinwheel.Hardware.StreamingReady.SessionCorrespondence.pins)

theorem good (rate : Fin 3) (actual : Session.Actual a) (s : Pinwheel.Program.StreamingReady.Session.State a)
    (armed : Session.Armed rate actual s) (raw : Nat → BitVec 2) (payload : BitVec 8) (ha : a ≤ 3)
    (falling : (raw 0)[(Boot.profile rate).rxInput.val] = false)
    (startLow : (raw (2*(Boot.profile rate).Q))[(Boot.profile rate).rxInput.val] = false)
    (samples : Pinwheel.Program.StreamingUART.Frame.DataSamples (Boot.profile rate) (incoming raw) payload)
    (stopHigh : (raw (38*(Boot.profile rate).Q))[(Boot.profile rate).rxInput.val] = true) :
    ∃ final : Pinwheel.Program.StreamingReady.Session.State a,
      Reached rate (actual.run (Pinwheel.Hardware.StreamingReady.Package.Components.typed a)
        ((pins raw (38*(Boot.profile rate).Q+4)).map Pinwheel.Hardware.StreamingReady.SessionCorrespondence.pins)) final ∧
      final.core.phase = .completed ∧ Pinwheel.Program.StreamingUART.Frame.Received 1 1 payload final.core := by
  have runtime := Session.armed_runtime rate actual s armed (pins raw (38*(Boot.profile rate).Q+4)) ha (pins_idle raw _)
  refine ⟨s.run (image (Boot.profile rate)).program false (pins raw (38*(Boot.profile rate).Q+4)),
    ⟨runtime.1,runtime.2.2⟩,?_⟩
  rw [runtime.2.1,inputs_map]
  exact Pinwheel.Program.StreamingUART.Frame.good_frame_result (Boot.profile rate) 1 1 payload (incoming raw)
    (quiet raw) falling startLow samples stopHigh

theorem bad_stop (rate : Fin 3) (actual : Session.Actual a) (s : Pinwheel.Program.StreamingReady.Session.State a)
    (armed : Session.Armed rate actual s) (raw : Nat → BitVec 2) (payload : BitVec 8) (ha : a ≤ 3)
    (falling : (raw 0)[(Boot.profile rate).rxInput.val] = false)
    (startLow : (raw (2*(Boot.profile rate).Q))[(Boot.profile rate).rxInput.val] = false)
    (samples : Pinwheel.Program.StreamingUART.Frame.DataSamples (Boot.profile rate) (incoming raw) payload)
    (stopLow : (raw (38*(Boot.profile rate).Q))[(Boot.profile rate).rxInput.val] = false) :
    ∃ final : Pinwheel.Program.StreamingReady.Session.State a,
      Reached rate (actual.run (Pinwheel.Hardware.StreamingReady.Package.Components.typed a)
        ((pins raw (38*(Boot.profile rate).Q+3)).map Pinwheel.Hardware.StreamingReady.SessionCorrespondence.pins)) final ∧
      final.core.phase = .fault ∧ Pinwheel.Program.StreamingUART.Frame.Received 1 1 payload final.core := by
  have runtime := Session.armed_runtime rate actual s armed (pins raw (38*(Boot.profile rate).Q+3)) ha (pins_idle raw _)
  refine ⟨s.run (image (Boot.profile rate)).program false (pins raw (38*(Boot.profile rate).Q+3)),
    ⟨runtime.1,runtime.2.2⟩,?_⟩
  rw [runtime.2.1,inputs_map]
  exact Pinwheel.Program.StreamingUART.Frame.bad_stop_result (Boot.profile rate) 1 1 payload (incoming raw)
    (quiet raw) falling startLow samples stopLow

theorem false_start (rate : Fin 3) (actual : Session.Actual a) (s : Pinwheel.Program.StreamingReady.Session.State a)
    (armed : Session.Armed rate actual s) (raw : Nat → BitVec 2) (ha : a ≤ 3)
    (falling : (raw 0)[(Boot.profile rate).rxInput.val] = false)
    (startHigh : (raw (2*(Boot.profile rate).Q))[(Boot.profile rate).rxInput.val] = true) :
    ∃ final : Pinwheel.Program.StreamingReady.Session.State a,
      Reached rate (actual.run (Pinwheel.Hardware.StreamingReady.Package.Components.typed a)
        ((pins raw (2*(Boot.profile rate).Q+3)).map Pinwheel.Hardware.StreamingReady.SessionCorrespondence.pins)) final ∧
      final.core.phase = .fault ∧ final.core.rxProduced = 0 ∧ final.core.rx.count.val = 0 := by
  have runtime := Session.armed_runtime rate actual s armed (pins raw (2*(Boot.profile rate).Q+3)) ha (pins_idle raw _)
  refine ⟨s.run (image (Boot.profile rate)).program false (pins raw (2*(Boot.profile rate).Q+3)),
    ⟨runtime.1,runtime.2.2⟩,?_⟩
  rw [runtime.2.1,inputs_map,FramePrelude.falseStart (Boot.profile rate) 1 1 (incoming raw) (quiet raw) falling startHigh]
  rw [FrameCell.sampleInputs_pair]
  exact ⟨rfl,rfl,rfl⟩

/-- Initialized physical good frame, with no prepared-state or command trace premise. -/
theorem concrete_good (rate : Fin 3) (startup : Session.Actual a) (raw : Nat → BitVec 2) (payload : BitVec 8) (ha : a ≤ 3)
    (falling : (raw 0)[(Boot.profile rate).rxInput.val] = false)
    (startLow : (raw (2*(Boot.profile rate).Q))[(Boot.profile rate).rxInput.val] = false)
    (samples : Pinwheel.Program.StreamingUART.Frame.DataSamples (Boot.profile rate) (incoming raw) payload)
    (stopHigh : (raw (38*(Boot.profile rate).Q))[(Boot.profile rate).rxInput.val] = true) :
    ∃ final : Pinwheel.Program.StreamingReady.Session.State a,
      Reached rate (actualRun rate startup raw (38*(Boot.profile rate).Q+4)) final ∧
      final.core.phase = .completed ∧ Pinwheel.Program.StreamingUART.Frame.Received 1 1 payload final.core := by
  obtain ⟨armed,reached⟩ := Session.initialized_armed rate startup ha
  exact good rate _ armed reached raw payload ha falling startLow samples stopHigh

theorem concrete_bad_stop (rate : Fin 3) (startup : Session.Actual a) (raw : Nat → BitVec 2) (payload : BitVec 8) (ha : a ≤ 3)
    (falling : (raw 0)[(Boot.profile rate).rxInput.val] = false)
    (startLow : (raw (2*(Boot.profile rate).Q))[(Boot.profile rate).rxInput.val] = false)
    (samples : Pinwheel.Program.StreamingUART.Frame.DataSamples (Boot.profile rate) (incoming raw) payload)
    (stopLow : (raw (38*(Boot.profile rate).Q))[(Boot.profile rate).rxInput.val] = false) :
    ∃ final : Pinwheel.Program.StreamingReady.Session.State a,
      Reached rate (actualRun rate startup raw (38*(Boot.profile rate).Q+3)) final ∧
      final.core.phase = .fault ∧ Pinwheel.Program.StreamingUART.Frame.Received 1 1 payload final.core := by
  obtain ⟨armed,reached⟩ := Session.initialized_armed rate startup ha
  exact bad_stop rate _ armed reached raw payload ha falling startLow samples stopLow

theorem concrete_false_start (rate : Fin 3) (startup : Session.Actual a) (raw : Nat → BitVec 2) (ha : a ≤ 3)
    (falling : (raw 0)[(Boot.profile rate).rxInput.val] = false)
    (startHigh : (raw (2*(Boot.profile rate).Q))[(Boot.profile rate).rxInput.val] = true) :
    ∃ final : Pinwheel.Program.StreamingReady.Session.State a,
      Reached rate (actualRun rate startup raw (2*(Boot.profile rate).Q+3)) final ∧
      final.core.phase = .fault ∧ final.core.rxProduced = 0 ∧ final.core.rx.count.val = 0 := by
  obtain ⟨armed,reached⟩ := Session.initialized_armed rate startup ha
  exact false_start rate _ armed reached raw ha falling startHigh

end Pinwheel.Hardware.StreamingUART.Frame
