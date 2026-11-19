import Pinwheel.Compile.I2CReadFetch
import Pinwheel.Hardware.Reactive.RegisteredFetch
import Pinwheel.I2C.RegisterReadFetch

/-! Tie the combined I²C read to the actual Reactive fetch circuit. The
ordinary core and the registered-fetch core use the same compiled memory. -/
namespace Pinwheel.Hardware.Reactive.I2CReadFetch

open Pinwheel.Hardware Pinwheel.I2C
open Pinwheel.Compile.I2CRead
open RegisterReadFetch

def runtimeInput (bus : Bus) : Core.Inputs :=
  { request := { incoming := Pinwheel.Compile.I2C.encodeInputs bus } }

def baseState (cfg : Config) (request : RegisterRead.Request) (s : RegisterRead.State) :
    Values RegisteredFetch.Base :=
  let p := program cfg request
  Core.values (embed (lift request s)) (Execution.directValues (Execution.imageWords p)) p.idle
    (BitVec.ofFin p.last)

private theorem runtime_step (p : ReadProgram) (s : ReadState) (raw : BitVec 2) :
    Engine.Reactive.step p s false false raw = Engine.Reactive.advance p s raw := by
  cases h : s.control <;> simp [Engine.Reactive.step, Engine.Reactive.busy, Engine.Reactive.advance, h]

/-- From the installed image, the original core takes one step of the
    independent register-read reference on every ordinary edge. -/
theorem baseline_step (cfg : Config) (request : RegisterRead.Request) (s : RegisterRead.State)
    (bus : Bus) :
    ((Core.circuit Core.direct).step (runtimeInput bus).values (baseState cfg request s) :
      Values RegisteredFetch.Base) = @baseState cfg request (RegisterRead.step cfg s bus) := by
  let p := program cfg request
  let mem : Values Execution.DirectReg := Execution.directValues (Execution.imageWords p)
  have next := Core.machine_next p mem Core.direct (Core.direct_represents p) Core.direct_stable
    (runtimeInput bus) (lift request s) (Or.inl rfl)
  dsimp only [runtimeInput] at next
  rw [runtime_step, advance_simulation] at next
  exact next

private def registerOutput (s : Values RegisteredFetch.Register) (r : Reactive.Register w) : BitVec w :=
  (RegisteredFetch.circuit 37).observe (runtimeInput {}).values s (.base (.state r))

private theorem registerOutput_eq (s : Values RegisteredFetch.Register) (r : Reactive.Register w) :
    registerOutput s r = s (.base (.core r)) := rfl

def drive (s : Values RegisteredFetch.Register) : Pins :=
  let enabled := registerOutput s .enabled
  ⟨if enabled[0] then .low else .release, if enabled[1] then .low else .release⟩

private theorem drive_eq (cfg : Config) (request : RegisterRead.Request) (s : RegisterRead.State)
    (hw : Values RegisteredFetch.Register) (represented : @RegisteredFetch.project hw = @baseState cfg request s) :
    drive hw = RegisterRead.pins request s.phase := by
  have enabled := congrArg (fun regs : Values RegisteredFetch.Base => regs (.core .enabled)) represented
  change hw (.base (.core .enabled)) = (embed (lift request s)).pins.enabled at enabled
  have embedded (m : ReadState) : (embed m).pins = m.pins := by
    cases h : m.control <;> simp [embed, h]
  rw [embedded] at enabled
  rw [drive, registerOutput_eq, enabled]
  dsimp only [lift]
  have decode (pins : Pins) :
      (⟨if (Pinwheel.Compile.I2C.encodePins pins).enabled[0] then .low else .release,
        if (Pinwheel.Compile.I2C.encodePins pins).enabled[1] then .low else .release⟩ : Pins) = pins := by
    rcases pins with ⟨scl, sda⟩
    cases scl <;> cases sda <;> rfl
  exact decode _

private theorem checked_control (cfg : Config) (request : RegisterRead.Request) (s : RegisterRead.State)
    (pc : Fin 256) (mode : baseState cfg request s (.core .mode) = 3#3)
    (address : baseState cfg request s (.core .pc) = BitVec.ofFin pc)
    (remaining : baseState cfg request s (.core .remaining) = 0#8) :
    control s = .checked pc 0 := by
  cases h : control s <;> simp [baseState, Core.values, State.values, embed, lift, h, stopMode] at mode address remaining ⊢
  case stopped reason =>
    cases reason <;> simp at mode
  case checked =>
    exact ⟨address, congrArg (@BitVec.toFin 8) remaining⟩

private theorem request_control (cfg : Config) (request : RegisterRead.Request) (s : RegisterRead.State)
    (hw : Values RegisteredFetch.Register) (represented : @RegisteredFetch.project hw = @baseState cfg request s)
    (bus : Bus) (pc : Fin 256)
    (waiting : (RegisteredFetch.fetchWait (BitVec.ofFin pc)).eval (runtimeInput bus).values hw = 1) :
    control s = .checked pc 0 := by
  have enabled := (RegisteredFetch.fetchWait_eq_one (BitVec.ofFin pc) _ hw).mp waiting
  rw [represented] at enabled
  exact checked_control cfg request s pc enabled.2.2.1 enabled.2.2.2.1 enabled.2.2.2.2

/-- The hardware's request edge is in the low phase, after the ACK was
    captured. A fetch response can therefore use the stored branch decision. -/
theorem request_is_low (cfg : Config) (request : RegisterRead.Request) (s : RegisterRead.State)
    (hw : Values RegisteredFetch.Register) (represented : @RegisteredFetch.project hw = @baseState cfg request s)
    (bus : Bus) (waiting : (RegisteredFetch.fetchWait 37).eval (runtimeInput bus).values hw = 1) :
    s.phase = .fall 8 ∧ s.remaining = 0 :=
  (first_ack_dispatch s).mp (request_control cfg request s hw represented bus 37 waiting)

/-- The alternate cut stalls the terminal high phase before capture. -/
theorem late_request_is_capture (cfg : Config) (request : RegisterRead.Request) (s : RegisterRead.State)
    (hw : Values RegisteredFetch.Register) (represented : @RegisteredFetch.project hw = @baseState cfg request s)
    (bus : Bus) (waiting : (RegisteredFetch.fetchWait 36).eval (runtimeInput bus).values hw = 1) :
    s.phase = .high 8 ∧ s.remaining = 0 :=
  (first_ack_capture s).mp (request_control cfg request s hw represented bus 36 waiting)

private theorem saved_request_stable (cfg : Config) (request : RegisterRead.Request) (s : RegisterRead.State)
    (hw : Values RegisteredFetch.Register) (represented : @RegisteredFetch.project hw = @baseState cfg request s)
    (cut : s.phase = .fall 8 ∧ s.remaining = 0) (x y : Bus) :
    RegisteredFetch.requestedWord.eval (runtimeInput x).values hw =
      RegisteredFetch.requestedWord.eval (runtimeInput y).values hw := by
  let checked : Engine.Reactive.Checked 255 15 :=
    ⟨⟨bitPins request 8 true, cfg.phaseMinusOne, none⟩, Pinwheel.Compile.I2C.unguarded, none, fallFinish 8⟩
  have controlEq := (first_ack_dispatch s).mpr cut
  have pc : (embed (lift request s)).pc.toFin = 37 := by
    simp [embed, lift, controlEq]
  apply RegisteredFetch.requestedWord_captureless (program cfg request) _ _ _ _ represented checked
  · rw [pc]
    have address : (37 : Fin 256).val = 37 := by decide
    simp [checked, Engine.Reactive.Program.fetch, program, instruction, bitInstruction, address]
  · rfl

/-- A pending response, if any, holds exactly the successor that the current
    program would fetch. This remains true for any next resolved wire value. -/
structure Related (cfg : Config) (request : RegisterRead.Request) (s : RegisterRead.State)
    (hw : Values RegisteredFetch.Register) : Prop where
  registers : @RegisteredFetch.project hw = @baseState cfg request s
  response : ∀ bus : Bus, hw .response = 1 →
    hw .savedWord = RegisteredFetch.requestedWord.eval (runtimeInput bus).values hw

def wireInput (hw : Values RegisteredFetch.Register) (peer : Pins) : Values Core.Input :=
  (runtimeInput (resolve (drive hw) peer)).values

def clock (hw : Values RegisteredFetch.Register) (peer : Pins) : Values RegisteredFetch.Register :=
  (RegisteredFetch.circuit 37).step (wireInput hw peer) hw

def tick (hw : Values RegisteredFetch.Register) (peer : Pins) : Tick :=
  if (RegisteredFetch.fetchWait 37).eval (wireInput hw peer) hw = 1 then .pending peer else .step peer

/-- The registered-fetch circuit takes the same logical step, or requests
    one successor while holding the controller in the after-ACK SCL-low cut. -/
theorem step (cfg : Config) (request : RegisterRead.Request) (s : RegisterRead.State)
    (hw : Values RegisteredFetch.Register) (peer : Pins) (h : Related cfg request s hw) :
    Related cfg request ((tick hw peer).advance cfg request s) (clock hw peer) ∧
    ((tick hw peer = .pending peer) → s.phase = .fall 8 ∧ s.remaining = 0) := by
  let bus := resolve (drive hw) peer
  change Related cfg request ((tick hw peer).advance cfg request s) (clock hw peer) ∧ _
  have resolved : bus = resolve (RegisterRead.pins request s.phase) peer := by
    rw [show bus = resolve (drive hw) peer from rfl, drive_eq cfg request s hw h.registers]
  by_cases waiting : (RegisteredFetch.fetchWait 37).eval (wireInput hw peer) hw = 1
  · have cut := request_is_low cfg request s hw h.registers bus waiting
    have held := (RegisteredFetch.hold_project 37 (wireInput hw peer) hw waiting).trans h.registers
    have saved := RegisteredFetch.request_saved 37 (wireInput hw peer) hw waiting
    rw [tick, if_pos waiting]
    refine ⟨⟨held, ?_⟩, fun _ => cut⟩
    intro nextBus _
    calc
      (clock hw peer) .savedWord = RegisteredFetch.requestedWord.eval (runtimeInput bus).values hw := saved.2
      _ = RegisteredFetch.requestedWord.eval (runtimeInput nextBus).values hw :=
        saved_request_stable cfg request s hw h.registers cut bus nextBus
      _ = RegisteredFetch.requestedWord.eval (runtimeInput nextBus).values (clock hw peer) := by
        simp only [RegisteredFetch.requestedWord, RegisteredFetch.lift_eval, h.registers, clock, held]
  · have moving : (RegisteredFetch.fetchWait 37).eval (wireInput hw peer) hw = 0 := by bv_omega
    have valid : hw .response = 0 ∨
        hw .savedWord = RegisteredFetch.requestedWord.eval (wireInput hw peer) hw := by
      by_cases response : hw .response = 1
      · exact Or.inr (h.response bus response)
      · exact Or.inl (by bv_omega)
    have next := RegisteredFetch.step_matches 37 (wireInput hw peer) hw moving valid
    rw [h.registers] at next
    have projected := next.trans (baseline_step cfg request s bus)
    rw [resolved] at projected
    rw [tick, if_neg waiting]
    refine ⟨⟨projected, ?_⟩, by simp⟩
    intro _ response
    unfold clock at response
    rw [RegisteredFetch.no_response 37 (wireInput hw peer) hw moving] at response
    contradiction

def runHardware (hw : Values RegisteredFetch.Register) (peers : List Pins) : Values RegisteredFetch.Register :=
  peers.foldl (α := Values RegisteredFetch.Register) clock hw

def schedule (hw : Values RegisteredFetch.Register) : List Pins → List Tick
  | [] => []
  | peer :: rest => tick hw peer :: schedule (clock hw peer) rest

def wireTrace (hw : Values RegisteredFetch.Register) : List Pins → List Wire
  | [] => []
  | peer :: rest => ⟨drive hw, resolve (drive hw) peer⟩ :: wireTrace (clock hw peer) rest

/-- This view reads the same mode and capture registers that feed the core's
    public state outputs. -/
def result (hw : Values RegisteredFetch.Register) : Option RegisterRead.Outcome :=
  Compile.I2CRead.result (view (fromValues (fun r => registerOutput hw r)))

private theorem related_result (cfg : Config) (request : RegisterRead.Request) (s : RegisterRead.State)
    (hw : Values RegisteredFetch.Register) (h : Related cfg request s hw) :
    result hw = RegisterRead.result s := by
  have regs : (fun {w} (r : Reactive.Register w) => hw (.base (.core r))) = @(embed (lift request s)).values := by
    funext w reg
    exact congrArg (fun bank : Values RegisteredFetch.Base => bank (.core reg)) h.registers
  simp only [result, registerOutput_eq]
  rw [regs, from_values, view_embed, result_lift]

/-- The retimed circuit and the independent protocol agree at every finite
    prefix of peer drives. The schedule comes from hardware and wire samples
    are resolved with the hardware's own pin drive on each physical edge. -/
theorem run_refines (cfg : Config) (request : RegisterRead.Request) (s : RegisterRead.State)
    (hw : Values RegisteredFetch.Register) (peers : List Pins) (h : Related cfg request s hw) :
    let ticks := schedule hw peers
    let final := RegisterReadFetch.run cfg request s ticks
    let actual : Values RegisteredFetch.Register := runHardware hw peers
    Related cfg request final actual ∧
    wireTrace hw peers = (trace cfg request s ticks).map Observation.wire ∧
    result actual = RegisterRead.result final := by
  induction peers generalizing s hw with
  | nil => exact ⟨h, rfl, related_result cfg request s hw h⟩
  | cons peer peers ih =>
    have advanced := (step cfg request s hw peer h).1
    obtain ⟨final, wires, outcome⟩ := ih _ _ advanced
    refine ⟨final, ?_, outcome⟩
    have driveEq := drive_eq cfg request s hw h.registers
    have peerEq : (tick hw peer).peer = peer := by unfold tick; split <;> rfl
    simp only [wireTrace, schedule, trace, List.map_cons, wires]
    change (⟨drive hw, resolve (drive hw) peer⟩ : Wire) :: _ =
      ⟨RegisterRead.pins request s.phase, resolve (RegisterRead.pins request s.phase) (tick hw peer).peer⟩ :: _
    rw [driveEq, peerEq]

/-- The response clears the wait gate on the very next edge, regardless of
    the target drive during the fetch. -/
theorem resumes_next_edge (hw : Values RegisteredFetch.Register) (peer next : Pins)
    (waiting : (RegisteredFetch.fetchWait 37).eval (wireInput hw peer) hw = 1) :
    tick (clock hw peer) next = .step next := by
  have available := (RegisteredFetch.request_saved 37 (wireInput hw peer) hw waiting).1
  unfold tick
  rw [RegisteredFetch.no_wait_of_response 37 (wireInput (clock hw peer) next) (clock hw peer) available]
  rfl

/-- With stage-aligned peer drives, one actual low fetch retains the read
    result and the ordered wire/capture events. The physical ACK window
    carries over when the extra clock fits inside the declared low budget. -/
theorem matched_ack_hold (cfg : Config) (request : RegisterRead.Request) (s : RegisterRead.State)
    (hw : Values RegisteredFetch.Register) (peers : List Pins) (h : Related cfg request s hw)
    (before after : List Tick) (peer : Pins)
    (scheduled : schedule hw peers = before ++ [.pending peer] ++ .step peer :: after)
    (timing : AckTiming) (window : AckWindow) (fits : timing.Fits window)
    (observed : timing.Observed (trace cfg request s (before ++ .step peer :: after)) slot value)
    (cut : timing.fall ≤ before.length ∧ before.length < timing.nextRise)
    (slack : timing.nextRise + 1 ≤ timing.fall + window.lowLimit) :
    let original := before ++ .step peer :: after
    let delayed := trace cfg request s (schedule hw peers)
    result (runHardware hw peers) = RegisterRead.result (RegisterReadFetch.run cfg request s original) ∧
    wireTrace hw peers = delayed.map Observation.wire ∧
    wireChanges delayed = wireChanges (trace cfg request s original) ∧
    delayed.filterMap Observation.capture = (trace cfg request s original).filterMap Observation.capture ∧
    (timing.holdLow 1).Observed delayed slot value ∧ (timing.holdLow 1).Fits window := by
  dsimp only
  obtain ⟨_, wires, resultEq⟩ := run_refines cfg request s hw peers h
  have splice := insert_fetch_hold cfg request s before after peer 1
  simp only [List.replicate_one] at splice
  rw [scheduled] at resultEq ⊢
  refine ⟨?_, ?_, splice.2.2.1, splice.2.2.2, ?_⟩
  · rw [resultEq, splice.1]
  · rw [← scheduled]
    exact wires
  · rw [splice.2.1]
    have baseObserved := observed
    rw [trace_append, trace] at baseObserved
    have instant := observe_after_ack_fetch timing window (trace cfg request s before) _
      (observe request (RegisterReadFetch.run cfg request s before) (.step peer))
      (observe request (RegisterReadFetch.run cfg request s before) (.pending peer)) 1
      rfl baseObserved fits
    rw [trace_length] at instant
    simpa only [List.replicate_one, trace] using instant cut slack

end Pinwheel.Hardware.Reactive.I2CReadFetch
