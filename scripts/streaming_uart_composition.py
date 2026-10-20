"""Join the same reconstructed Ready components to autonomous UART sessions.

Every generated module is compiled by native Lean against fresh component and
wrapper certificates. This factory is an untrusted proof producer.
"""
import streaming_ready_composition


def generate(addr_bits):
    if type(addr_bits) is not int or addr_bits not in (1, 2):
        raise ValueError('Qualified streaming address width must be 1 or 2')
    depth = str(2 ** addr_bits)
    texts = streaming_ready_composition.generate(addr_bits)
    source = r'''def uartBootPins (rate : Fin 3) : List TinyWiring.Pins :=
  (BootPins.coldPin :: Pinwheel.Hardware.StreamingUART.Boot.pins rate).map PublicPins.embed

def uartArmPins (rate : Fin 3) : List TinyWiring.Pins :=
  (BootPins.coldPin :: (Pinwheel.Hardware.StreamingUART.Boot.pins rate ++
    Pinwheel.Program.StreamingUART.StartPins.pins)).map PublicPins.embed

theorem concrete_uart_initialized (rate : Fin 3) (startup : Package.State @A@) :
    ∃ source : Session.State @A@,
      BootCorrespondence.Initialized
        (Pinwheel.Program.StreamingUART.image (Pinwheel.Hardware.StreamingUART.Boot.profile rate))
        (physicalRun startup (uartBootPins rate)) source := by
  rw [physical_run_correct,uartBootPins,embedded_engine_pins,List.map_cons]
  exact Pinwheel.Hardware.StreamingUART.Boot.initialized rate startup

theorem uart_armed_actual (rate : Fin 3) (startup : Package.State @A@) :
    physicalRun startup (uartArmPins rate) =
      Pinwheel.Hardware.StreamingUART.Session.armedActual rate startup := by
  rw [physical_run_correct,uartArmPins,embedded_engine_pins,List.map_cons,List.map_append]
  change startup.run (Package.Components.typed @A@)
      ((SessionCorrespondence.pins BootPins.coldPin ::
        (Pinwheel.Hardware.StreamingUART.Boot.pins rate).map SessionCorrespondence.pins) ++
        Pinwheel.Program.StreamingUART.StartPins.pins.map SessionCorrespondence.pins) = _
  exact List.foldl_append

theorem uart_arming_correct (rate : Fin 3) (startup : Package.State @A@) :
    ∃ source : Session.State @A@,
      Pinwheel.Hardware.StreamingUART.Session.Armed rate
        (physicalRun startup (uartArmPins rate)) source := by
  rw [uart_armed_actual]
  exact Pinwheel.Hardware.StreamingUART.Session.initialized_armed rate startup (by decide)

theorem uart_continuation_actual (rate : Fin 3) (startup : Package.State @A@)
    (samples : List Session.Pins) :
    physicalRun startup (uartArmPins rate ++ samples.map PublicPins.embed) =
      (Pinwheel.Hardware.StreamingUART.Session.armedActual rate startup).run
        (Package.Components.typed @A@) (samples.map SessionCorrespondence.pins) := by
  rw [physical_run_append,uart_armed_actual,physical_run_correct,embedded_engine_pins]

/-- Public idle host pins derive source quiescence and preserve reached custody.
The raw input sequence remains arbitrary on every physical clock. -/
theorem uart_host_quiet_correct (rate : Fin 3) (actual : Package.State @A@)
    (source : Session.State @A@)
    (armed : Pinwheel.Hardware.StreamingUART.Session.Armed rate actual source)
    (inputs : List TinyWiring.Pins)
    (pins : ∀ pin ∈ inputs, Pinwheel.Program.StreamingUART.HostQuiet.Pins
      (SessionCorrespondence.physicalPins pin)) :
    physicalRun actual inputs = SessionCorrespondence.values
      (Initialization.compiledImage (Pinwheel.Program.StreamingUART.image
        (Pinwheel.Hardware.StreamingUART.Boot.profile rate)))
      (source.run (Pinwheel.Program.StreamingUART.image
        (Pinwheel.Hardware.StreamingUART.Boot.profile rate)).program false
        (inputs.map SessionCorrespondence.physicalPins)) ∧
    (source.run (Pinwheel.Program.StreamingUART.image
      (Pinwheel.Hardware.StreamingUART.Boot.profile rate)).program false
      (inputs.map SessionCorrespondence.physicalPins)).core =
      run (Pinwheel.Program.StreamingUART.image
        (Pinwheel.Hardware.StreamingUART.Boot.profile rate)).program
        (Pinwheel.Program.StreamingUART.Arm.armed
          (Pinwheel.Hardware.StreamingUART.Boot.profile rate) 1 1)
        (inputs.map (fun pin => ({rawInputs := (SessionCorrespondence.physicalPins pin).rawInputs} : Input))) ∧
    (∃ trace : BitTrace,
      (source.run (Pinwheel.Program.StreamingUART.image
        (Pinwheel.Hardware.StreamingUART.Boot.profile rate)).program false
        (inputs.map SessionCorrespondence.physicalPins)).Custody trace ∧
      (source.run (Pinwheel.Program.StreamingUART.image
        (Pinwheel.Hardware.StreamingUART.Boot.profile rate)).program false
        (inputs.map SessionCorrespondence.physicalPins)).FreeExport) := by
  rw [physical_run_source_pins]
  have result := Pinwheel.Hardware.StreamingUART.Session.armed_runtime rate actual source armed
    (inputs.map SessionCorrespondence.physicalPins) (by decide)
    (by intro pin member; obtain ⟨physical,physicalMember,rfl⟩ := List.mem_map.mp member; exact pins physical physicalMember)
  simpa only [List.map_map,Function.comp_def] using result

theorem concrete_uart_runtime (rate : Fin 3) (startup : Package.State @A@) :
    ∃ source : Session.State @A@,
      Pinwheel.Hardware.StreamingUART.Session.Armed rate (physicalRun startup (uartArmPins rate)) source ∧
      ∀ inputs : List TinyWiring.Pins,
        (∀ pin ∈ inputs, Pinwheel.Program.StreamingUART.HostQuiet.Pins
          (SessionCorrespondence.physicalPins pin)) →
        physicalRun startup (uartArmPins rate ++ inputs) = SessionCorrespondence.values
          (Initialization.compiledImage (Pinwheel.Program.StreamingUART.image
            (Pinwheel.Hardware.StreamingUART.Boot.profile rate)))
          (source.run (Pinwheel.Program.StreamingUART.image
            (Pinwheel.Hardware.StreamingUART.Boot.profile rate)).program false
            (inputs.map SessionCorrespondence.physicalPins)) := by
  obtain ⟨source,armed⟩ := uart_arming_correct rate startup
  refine ⟨source,armed,?_⟩
  intro inputs pins
  rw [physical_run_append]
  exact (uart_host_quiet_correct rate _ source armed inputs pins).1

theorem concrete_uart_custody (rate : Fin 3) (startup : Package.State @A@) :
    ∃ source : Session.State @A@,
      Pinwheel.Hardware.StreamingUART.Session.Armed rate (physicalRun startup (uartArmPins rate)) source ∧
      (∃ trace : BitTrace, source.Custody trace ∧ source.FreeExport) := by
  obtain ⟨source,armed⟩ := uart_arming_correct rate startup
  exact ⟨source,armed,armed.custody⟩

@FRAME_THEOREMS@

'''
    source = source.replace('@FRAME_THEOREMS@', frame_theorems())
    source = source.replace('@D@', depth).replace('@A@', str(addr_bits))
    # Lean export aliases print their original namespace in #check. Reuse the
    # checked proof bodies to create concrete declarations in the required new
    # root, so the native type inventory cannot silently refer to another root.
    old_root, new_root = 'StreamingReadySessionD' + depth, 'StreamingUARTSessionD' + depth
    ending = 'end Pinwheel.Artifact.' + old_root + '\n'
    inherited = texts[old_root]
    if not inherited.endswith(ending):
        raise RuntimeError('Changed inherited composition module boundary')
    inherited = inherited.removesuffix(ending).replace(
        'namespace Pinwheel.Artifact.' + old_root, 'namespace Pinwheel.Artifact.' + new_root)
    source = ('import Pinwheel.Hardware.StreamingUART.Frame\n' + inherited + '\n' + source +
        'end Pinwheel.Artifact.' + new_root + '\n')
    texts[new_root] = source
    return texts


def frame_theorems():
    return r'''
theorem uart_actual_frame (rate : Fin 3) (startup : Package.State @A@)
    (raw : Nat → BitVec 2) (edges : Nat) :
    physicalRun startup (uartArmPins rate ++
      (Pinwheel.Hardware.StreamingUART.Frame.pins raw edges).map PublicPins.embed) =
      Pinwheel.Hardware.StreamingUART.Frame.actualRun rate startup raw edges :=
  uart_continuation_actual rate startup _

/-- The actual reconstructed components and wrappers receive the initialized
frame under public raw-pin conditions; no prepared receiver is assumed. -/
theorem uart_frame_correct (rate : Fin 3) (startup : Package.State @A@)
    (raw : Nat → BitVec 2) (payload : BitVec 8)
    (falling : (raw 0)[(Pinwheel.Hardware.StreamingUART.Boot.profile rate).rxInput.val] = false)
    (startLow : (raw (2*(Pinwheel.Hardware.StreamingUART.Boot.profile rate).Q))[(Pinwheel.Hardware.StreamingUART.Boot.profile rate).rxInput.val] = false)
    (samples : Pinwheel.Program.StreamingUART.Frame.DataSamples
      (Pinwheel.Hardware.StreamingUART.Boot.profile rate)
      (Pinwheel.Hardware.StreamingUART.Frame.incoming raw) payload)
    (stopHigh : (raw (38*(Pinwheel.Hardware.StreamingUART.Boot.profile rate).Q))[(Pinwheel.Hardware.StreamingUART.Boot.profile rate).rxInput.val] = true) :
    ∃ final : Session.State @A@,
      Pinwheel.Hardware.StreamingUART.Frame.Reached rate
        (physicalRun startup (uartArmPins rate ++
          (Pinwheel.Hardware.StreamingUART.Frame.pins raw
            (38*(Pinwheel.Hardware.StreamingUART.Boot.profile rate).Q+4)).map PublicPins.embed)) final ∧
      final.core.phase = .completed ∧
        Pinwheel.Program.StreamingUART.Frame.Received 1 1 payload final.core := by
  rw [uart_actual_frame]
  exact Pinwheel.Hardware.StreamingUART.Frame.concrete_good rate startup raw payload
    (by decide) falling startLow samples stopHigh

theorem uart_bad_stop_correct (rate : Fin 3) (startup : Package.State @A@)
    (raw : Nat → BitVec 2) (payload : BitVec 8)
    (falling : (raw 0)[(Pinwheel.Hardware.StreamingUART.Boot.profile rate).rxInput.val] = false)
    (startLow : (raw (2*(Pinwheel.Hardware.StreamingUART.Boot.profile rate).Q))[(Pinwheel.Hardware.StreamingUART.Boot.profile rate).rxInput.val] = false)
    (samples : Pinwheel.Program.StreamingUART.Frame.DataSamples
      (Pinwheel.Hardware.StreamingUART.Boot.profile rate)
      (Pinwheel.Hardware.StreamingUART.Frame.incoming raw) payload)
    (stopLow : (raw (38*(Pinwheel.Hardware.StreamingUART.Boot.profile rate).Q))[(Pinwheel.Hardware.StreamingUART.Boot.profile rate).rxInput.val] = false) :
    ∃ final : Session.State @A@,
      Pinwheel.Hardware.StreamingUART.Frame.Reached rate
        (physicalRun startup (uartArmPins rate ++
          (Pinwheel.Hardware.StreamingUART.Frame.pins raw
            (38*(Pinwheel.Hardware.StreamingUART.Boot.profile rate).Q+3)).map PublicPins.embed)) final ∧
      final.core.phase = .fault ∧
        Pinwheel.Program.StreamingUART.Frame.Received 1 1 payload final.core := by
  rw [uart_actual_frame]
  exact Pinwheel.Hardware.StreamingUART.Frame.concrete_bad_stop rate startup raw payload
    (by decide) falling startLow samples stopLow

theorem uart_false_start_correct (rate : Fin 3) (startup : Package.State @A@)
    (raw : Nat → BitVec 2)
    (falling : (raw 0)[(Pinwheel.Hardware.StreamingUART.Boot.profile rate).rxInput.val] = false)
    (startHigh : (raw (2*(Pinwheel.Hardware.StreamingUART.Boot.profile rate).Q))[(Pinwheel.Hardware.StreamingUART.Boot.profile rate).rxInput.val] = true) :
    ∃ final : Session.State @A@,
      Pinwheel.Hardware.StreamingUART.Frame.Reached rate
        (physicalRun startup (uartArmPins rate ++
          (Pinwheel.Hardware.StreamingUART.Frame.pins raw
            (2*(Pinwheel.Hardware.StreamingUART.Boot.profile rate).Q+3)).map PublicPins.embed)) final ∧
      final.core.phase = .fault ∧ final.core.rxProduced = 0 ∧ final.core.rx.count.val = 0 := by
  rw [uart_actual_frame]
  exact Pinwheel.Hardware.StreamingUART.Frame.concrete_false_start rate startup raw
    (by decide) falling startHigh
'''
