import Pinwheel.Hardware.StreamingUART.Frame
import Pinwheel.Hardware.StreamingReady.PublicPins
import Pinwheel.Program.StreamingUARTFirstTerminal

/-! Earliest UART terminal edges at the actual public BUSY pad. The concrete
cold/upload/START prefix is derived from arbitrary initial register contents.
The observation pin is active and deselected, so pad masking cannot manufacture
a BUSY drop. Counts are processed raw input prefixes, starting at raw index 0. -/
namespace Pinwheel.Hardware.StreamingMapped.UARTTiming
open Pinwheel.Hardware Pinwheel.Hardware.StreamingReady
open Pinwheel.Program.StreamingReady Pinwheel.Program.StreamingUART

def idlePin (raw : BitVec 2) : Pinwheel.Program.StreamingReady.Session.Pins :=
  {rawInputs := raw}

def padPin (raw : BitVec 2) : TinyWiring.Pins := PublicPins.embed (idlePin raw)

/-- Bit5 of the actual Tiny Tapeout output vector, with active public pins. -/
def busyPad (actual : Package.State a) (raw : BitVec 2) : Bool :=
  (TinyWiring.Description.pads (TinyWiring.canonical a) (padPin raw)
    (actual.observe (Package.Components.typed a)
      (TinyWiring.Description.enginePins (TinyWiring.canonical a) (padPin raw))) .uo).getLsbD 5

theorem pad_busy (a : Nat) (raw : BitVec 2) (engine : Values Package.Output) :
    (TinyWiring.Description.pads (TinyWiring.canonical a) (padPin raw) engine .uo).getLsbD 5 =
      (engine .busy).getLsbD 0 := by
  change (if (padPin raw).ena &&& (padPin raw).rstN = 1#1 then
    (0#2) ++ (engine .busy ++ (engine .ready ++ engine .miso)) else 0#8).getLsbD 5 = _
  rw [if_pos (show (padPin raw).ena &&& (padPin raw).rstN = 1#1 by change (1#1 &&& 1#1) = 1#1; decide)]
  simp only [BitVec.getLsbD_append]
  simp

theorem busyPad_raw_irrelevant (actual : Package.State a) (left right : BitVec 2) :
    busyPad actual left = busyPad actual right := by
  simp only [busyPad,pad_busy]
  rfl

theorem busyPad_source (image : SourceRefinement.Image p)
    (s : Pinwheel.Program.StreamingReady.Session.State a) (raw : BitVec 2) (ha : a ≤ 3)
    (runtime : Pinwheel.Program.StreamingReady.Session.RuntimeInput s (idlePin raw))
    (structural : s.core.Structural) :
    busyPad (SessionCorrespondence.values image s) raw = s.core.phase.busy := by
  rw [busyPad,pad_busy]
  unfold padPin
  rw [PublicPins.engine_embed]
  have output := SessionCorrespondence.outputs_correct image s (idlePin raw) ha runtime structural .busy
  rw [output]
  simp only [SessionCorrespondence.outputs,BitVec.getLsbD_ofBool]
  simp

theorem armed_busyPad (rate : Fin 3) (actual : Package.State a)
    (source : Pinwheel.Program.StreamingReady.Session.State a)
    (armed : Pinwheel.Hardware.StreamingUART.Session.Armed rate actual source)
    (raw : Nat → BitVec 2) (edges : Nat) (ha : a ≤ 3) :
    busyPad (actual.run (Package.Components.typed a)
      ((Pinwheel.Hardware.StreamingUART.Frame.pins raw edges).map SessionCorrespondence.pins)) (raw edges) =
    (run (image (Pinwheel.Hardware.StreamingUART.Boot.profile rate)).program
      (Arm.armed (a := a) (Pinwheel.Hardware.StreamingUART.Boot.profile rate) 1 1)
      (FrameSamples.clocks (Pinwheel.Hardware.StreamingUART.Frame.incoming raw) 0 edges)).phase.busy := by
  have runtime := Pinwheel.Hardware.StreamingUART.Session.armed_runtime rate actual source armed
    (Pinwheel.Hardware.StreamingUART.Frame.pins raw edges) ha
    (Pinwheel.Hardware.StreamingUART.Frame.pins_idle raw edges)
  have idle := HostQuiet.run_idle source
    (image (Pinwheel.Hardware.StreamingUART.Boot.profile rate)).program false
    (Pinwheel.Hardware.StreamingUART.Frame.pins raw edges) armed.idle
    (Pinwheel.Hardware.StreamingUART.Frame.pins_idle raw edges)
  have quiet := HostQuiet.command_quiet
    (source.run (image (Pinwheel.Hardware.StreamingUART.Boot.profile rate)).program false
      (Pinwheel.Hardware.StreamingUART.Frame.pins raw edges)) (idlePin (raw edges)) idle
    ⟨rfl,rfl,rfl⟩
  have currentRuntime : Pinwheel.Program.StreamingReady.Session.RuntimeInput
      (source.run (image (Pinwheel.Hardware.StreamingUART.Boot.profile rate)).program false
        (Pinwheel.Hardware.StreamingUART.Frame.pins raw edges)) (idlePin (raw edges)) :=
    ⟨quiet.cold,by rw [quiet.command]; decide,by rw [quiet.command]; decide,by rw [quiet.command]; decide⟩
  obtain ⟨trace,custody,_⟩ := runtime.2.2
  rw [runtime.1,busyPad_source _ _ _ ha currentRuntime custody.structural,runtime.2.1,
    Pinwheel.Hardware.StreamingUART.Frame.inputs_map]

theorem initialized_busyPad (rate : Fin 3) (startup : Package.State a)
    (raw : Nat → BitVec 2) (edges : Nat) (ha : a ≤ 3) :
    busyPad (Pinwheel.Hardware.StreamingUART.Frame.actualRun rate startup raw edges) (raw edges) =
    (run (image (Pinwheel.Hardware.StreamingUART.Boot.profile rate)).program
      (Arm.armed (a := a) (Pinwheel.Hardware.StreamingUART.Boot.profile rate) 1 1)
      (FrameSamples.clocks (Pinwheel.Hardware.StreamingUART.Frame.incoming raw) 0 edges)).phase.busy := by
  obtain ⟨source,armed⟩ := Pinwheel.Hardware.StreamingUART.Session.initialized_armed rate startup ha
  exact armed_busyPad rate _ source armed raw edges ha

/-- BUSY at the public pad stays high before `edges` and first becomes low
after that many processed frame inputs. Cold/upload/START precede this frame. -/
def FirstBusy (rate : Fin 3) (startup : Package.State a) (raw : Nat → BitVec 2) (edges : Nat) : Prop :=
  (∀ observation, busyPad (Pinwheel.Hardware.StreamingUART.Frame.actualRun rate startup raw edges) observation = false) ∧
    ∀ earlier, earlier < edges →
      ∀ observation, busyPad (Pinwheel.Hardware.StreamingUART.Frame.actualRun rate startup raw earlier) observation = true

private theorem retained_not_busy (phase : Phase) (retained : phase.retained = true) : phase.busy = false := by
  cases phase <;> simp_all [Phase.retained,Phase.busy]

theorem firstBusy_of_source (rate : Fin 3) (startup : Package.State a)
    (raw : Nat → BitVec 2) (edges : Nat) (ha : a ≤ 3)
    (first : FirstTerminal.FirstAt (image (Pinwheel.Hardware.StreamingUART.Boot.profile rate)).program
      (Arm.armed (a := a) (Pinwheel.Hardware.StreamingUART.Boot.profile rate) 1 1)
      (Pinwheel.Hardware.StreamingUART.Frame.incoming raw) edges) :
    FirstBusy rate startup raw edges := by
  constructor
  · intro observation
    rw [busyPad_raw_irrelevant _ observation (raw edges),initialized_busyPad rate startup raw edges ha]
    exact retained_not_busy _ first.1
  · intro earlier before observation
    rw [busyPad_raw_irrelevant _ observation (raw earlier),initialized_busyPad rate startup raw earlier ha]
    exact first.2 earlier before

theorem good_first (rate : Fin 3) (startup : Package.State a)
    (raw : Nat → BitVec 2) (payload : BitVec 8) (ha : a ≤ 3)
    (falling : (raw 0)[(Pinwheel.Hardware.StreamingUART.Boot.profile rate).rxInput.val] = false)
    (startLow : (raw (2*(Pinwheel.Hardware.StreamingUART.Boot.profile rate).Q))[(Pinwheel.Hardware.StreamingUART.Boot.profile rate).rxInput.val] = false)
    (samples : Frame.DataSamples (Pinwheel.Hardware.StreamingUART.Boot.profile rate)
      (Pinwheel.Hardware.StreamingUART.Frame.incoming raw) payload)
    (stopHigh : (raw (38*(Pinwheel.Hardware.StreamingUART.Boot.profile rate).Q))[(Pinwheel.Hardware.StreamingUART.Boot.profile rate).rxInput.val] = true) :
    FirstBusy rate startup raw (38*(Pinwheel.Hardware.StreamingUART.Boot.profile rate).Q+4) := by
  apply firstBusy_of_source rate startup raw _ ha
  exact FirstTerminal.good_frame_first _ 1 1 payload _ (Pinwheel.Hardware.StreamingUART.Frame.quiet raw)
    falling startLow samples stopHigh

theorem bad_stop_first (rate : Fin 3) (startup : Package.State a)
    (raw : Nat → BitVec 2) (payload : BitVec 8) (ha : a ≤ 3)
    (falling : (raw 0)[(Pinwheel.Hardware.StreamingUART.Boot.profile rate).rxInput.val] = false)
    (startLow : (raw (2*(Pinwheel.Hardware.StreamingUART.Boot.profile rate).Q))[(Pinwheel.Hardware.StreamingUART.Boot.profile rate).rxInput.val] = false)
    (samples : Frame.DataSamples (Pinwheel.Hardware.StreamingUART.Boot.profile rate)
      (Pinwheel.Hardware.StreamingUART.Frame.incoming raw) payload)
    (stopLow : (raw (38*(Pinwheel.Hardware.StreamingUART.Boot.profile rate).Q))[(Pinwheel.Hardware.StreamingUART.Boot.profile rate).rxInput.val] = false) :
    FirstBusy rate startup raw (38*(Pinwheel.Hardware.StreamingUART.Boot.profile rate).Q+3) := by
  apply firstBusy_of_source rate startup raw _ ha
  exact FirstTerminal.bad_stop_first _ 1 1 payload _ (Pinwheel.Hardware.StreamingUART.Frame.quiet raw)
    falling startLow samples stopLow

theorem false_start_first (rate : Fin 3) (startup : Package.State a)
    (raw : Nat → BitVec 2) (ha : a ≤ 3)
    (falling : (raw 0)[(Pinwheel.Hardware.StreamingUART.Boot.profile rate).rxInput.val] = false)
    (startHigh : (raw (2*(Pinwheel.Hardware.StreamingUART.Boot.profile rate).Q))[(Pinwheel.Hardware.StreamingUART.Boot.profile rate).rxInput.val] = true) :
    FirstBusy rate startup raw (2*(Pinwheel.Hardware.StreamingUART.Boot.profile rate).Q+3) := by
  apply firstBusy_of_source rate startup raw _ ha
  exact FirstTerminal.false_start_first _ 1 1 _ (Pinwheel.Hardware.StreamingUART.Frame.quiet raw) falling startHigh

end Pinwheel.Hardware.StreamingMapped.UARTTiming
