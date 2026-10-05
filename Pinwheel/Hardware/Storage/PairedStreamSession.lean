import Pinwheel.Hardware.Storage.PairedStream
import Pinwheel.Hardware.Storage.PairedHost
import Pinwheel.Hardware.Storage.PairedStreamPackage
import Pinwheel.Hardware.Storage.PairedStreamOwnership
import Pinwheel.Hardware.Storage.PairedStreamBootstrap
import Pinwheel.UART.BufferedSupervisor
import Pinwheel.UART.BufferedSupervisorPhase

/-! Initialized UART sessions of the paired stream package. Program ownership
is ghost state: replacing an image does not relabel an unread packet. The UART
receiver is stepped independently of the represented controller registers. -/
namespace Pinwheel.Hardware.Storage.PairedStreamSession
open Pinwheel.Hardware
open PairedCoverage (Tracked graphInputs advance graph_equations)
open UART.Rx (Config)
set_option backward.isDefEq.respectTransparency false

inductive Origin where
  | unknown
  | uart (epoch : Nat) (cfg : Config)
  deriving DecidableEq, Repr

structure OwnedPacket where
  packet : HostResultBuffer.Packet
  origin : Origin
  deriving DecidableEq, Repr

abbrev Mailbox := HostResultBuffer.Retained.State OwnedPacket
abbrev Receipt := HostResultBuffer.Retained.Receipt OwnedPacket

def erase (s : Mailbox) : HostResultBuffer.Retained.State HostResultBuffer.Packet :=
  ⟨s.pending.map OwnedPacket.packet, s.overrun⟩

def eraseReceipt (r : Receipt) : HostResultBuffer.Retained.Receipt HostResultBuffer.Packet :=
  ⟨r.accepted.map OwnedPacket.packet, r.delivered.map OwnedPacket.packet,
    r.dropped.map OwnedPacket.packet, r.flushed.map OwnedPacket.packet⟩

def eraseCommand : HostResultBuffer.Retained.Command OwnedPacket →
    HostResultBuffer.Retained.Command HostResultBuffer.Packet
  | .reset => .reset
  | .cycle arrival take clear => .cycle (arrival.map OwnedPacket.packet) take clear

theorem erase_step (s : Mailbox) (command : HostResultBuffer.Retained.Command OwnedPacket) :
    (⟨erase (HostResultBuffer.Retained.step s command).state,
      eraseReceipt (HostResultBuffer.Retained.step s command).receipt⟩ :
        HostResultBuffer.Retained.Transition HostResultBuffer.Packet) =
      HostResultBuffer.Retained.step (erase s) (eraseCommand command) := by
  cases command
  all_goals grind [erase, eraseReceipt, eraseCommand, HostResultBuffer.Retained.step]
  done

def uartOutput (cfg : Config) (receiver : UART.Rx.State) : Values Loader.Machine.Output :=
  PairedHost.withExecution (fun {_} _ => 0) (Compile.UARTRx.lift cfg receiver)

def receiverPacket (cfg : Config) (receiver : UART.Rx.State) : HostResultBuffer.Packet :=
  ⟨HostResult.sampleValues (uartOutput cfg receiver),
    (Reactive.embed (Compile.UARTRx.lift cfg receiver)).mode⟩

def receiverArrival (cfg : Config) (receiver : UART.Rx.State) (active : Bool) :
    Option HostResultBuffer.Packet :=
  if active then match receiver.phase with
    | .finished => some (receiverPacket cfg receiver)
    | _ => none
  else none

structure ReferenceState where
  storage : Tracked
  enabled : Bool
  receiver : UART.Rx.State
  adapters : Chip.State
  result : HostResult.State
  mailbox : Mailbox
  active : Bool
  epoch : Nat

/-- The policy's execution status comes from the independent receiver. The
remaining status bits belong to the separately tracked loader. -/
def status (cfg : Config) (s : ReferenceState) : PairedStream.Status :=
  ⟨(Reactive.embed (Compile.UARTRx.lift cfg s.receiver)).mode,
    s.storage.registers .valid == 1, s.storage.registers .pending == 1⟩

def policy (cfg : Config) (s : ReferenceState) : PairedStream.Transition :=
  PairedStream.step ⟨s.enabled⟩ (status cfg s) (PairedPackage.decoded s.adapters)

def effective (cfg : Config) (s : ReferenceState) : Loader.Machine.Inputs :=
  (policy cfg s).effective

def sideband (cfg : Config) (s : ReferenceState) : Values Loader.Machine.Output :=
  fun {_} o => PairedController.body.observe (graphInputs (effective cfg s).values s.storage)
    s.storage.registers (.base o)

def referenceOutput (cfg : Config) (s : ReferenceState) : Values Loader.Machine.Output :=
  PairedHost.withExecution (sideband cfg s) (Compile.UARTRx.lift cfg s.receiver)

def ownedArrival (cfg : Config) (s : ReferenceState) : Option OwnedPacket :=
  (receiverArrival cfg s.receiver s.active).map (fun packet => ⟨packet, .uart s.epoch cfg⟩)

def mailboxCommand (cfg : Config) (pins : Chip.Pins) (s : ReferenceState) :
    HostResultBuffer.Retained.Command OwnedPacket :=
  if HostResult.resetting pins s.result then .reset else
    .cycle (ownedArrival cfg s) (HostResult.consuming s.result) (HostResult.clearing s.result)

def shown (cfg : Config) (s : ReferenceState) : Values Chip.Output
  | _, .uoOut => if s.result.pageSecond == 3 then
      ~~~(~~~(HostResult.shown (referenceOutput cfg s) s.result .uoOut) &&&
        ~~~PairedStream.enabledBits (BitVec.ofBool s.enabled))
      else HostResult.shown (referenceOutput cfg s) s.result .uoOut
  | _, p => HostResult.shown (referenceOutput cfg s) s.result p

def reference (cfg : Config) : Timed.Component Chip.Pins ReferenceState (Values Chip.Output) where
  step := fun pins s =>
    let output : Values Loader.Machine.Output := referenceOutput cfg s
    ⟨advance s.storage (effective cfg s).values, (policy cfg s).state.enabled,
      UART.Rx.step cfg s.receiver (PairedEdges.resetRequested (effective cfg s).values)
        ((effective cfg s).command == 5) ((effective cfg s).incoming[cfg.input.val]),
      PairedPackage.adaptersNext pins s.adapters, HostResult.next pins output s.result,
      (HostResultBuffer.Retained.step s.mailbox (mailboxCommand cfg pins s)).state,
      if HostResult.resetting pins s.result then false else
        Engine.Reactive.busy (Compile.UARTRx.lift cfg s.receiver) || output (.control .start) == 1,
      s.epoch⟩
  observe := fun _ s => shown cfg s

theorem receiver_arrival (cfg : Config) (receiver : UART.Rx.State)
    (o : Values Loader.Machine.Output) (host : HostResult.State) (active : Bool)
    (hactive : host.wasActive = active) :
    HostResultBuffer.arrival (PairedHost.withExecution o (Compile.UARTRx.lift cfg receiver)) host =
      receiverArrival cfg receiver active := by
  simp only [HostResultBuffer.arrival, HostResult.arriving, PairedHost.withExecution,
    Compile.UARTRx.busy_lift]
  rcases receiver with ⟨phase, remaining, samples⟩
  cases phase
  all_goals simp [PairedHost.withExecution,
    Compile.UARTRx.lift, Compile.UARTRx.liftControl, Reactive.embed, Reactive.stopMode,
    receiverArrival, receiverPacket, uartOutput, hactive,
    UART.Rx.busy, Reactive.State.values, HostResult.sampleValues]
  done

theorem core_next (cfg : Config) (image : PairedImage.Image) (s : ReferenceState)
    (h : PairedTimed.Related (Compile.UARTRx.program cfg) image s.storage
      (Compile.UARTRx.lift cfg s.receiver))
    (rule : PairedCertified.Rule (effective cfg s).values)
    (valid : UART.Rx.WellFormed cfg s.receiver) (pins : Chip.Pins) :
    PairedTimed.Related (Compile.UARTRx.program cfg) image
      ((reference cfg).step pins s).storage
      (Compile.UARTRx.lift cfg ((reference cfg).step pins s).receiver) := by
  have next := (PairedTimed.refinement (Compile.UARTRx.program cfg) image).step
    (effective cfg s).values s.storage (Compile.UARTRx.lift cfg s.receiver) rule h
  simpa only [PairedTimed.refinement, PairedTimed.tracked, PairedTimed.reference, reference,
    Compile.UARTRx.step_simulation cfg s.receiver _ _ _ valid,
    Loader.Machine.Inputs.values] using next
  done

theorem mailbox_command (cfg : Config) (s : ReferenceState) (pins : Chip.Pins)
    (active : s.result.wasActive = s.active) :
    eraseCommand (mailboxCommand cfg pins s) =
      HostResultBuffer.command pins (referenceOutput cfg s) s.result := by
  simp only [mailboxCommand, HostResultBuffer.command]
  split <;> simp [eraseCommand, ownedArrival, referenceOutput,
    receiver_arrival cfg s.receiver (sideband cfg s) s.result s.active active, Function.comp_def]
  done

structure Certified (cfg : Config) (image : PairedImage.Image) (s : ReferenceState) : Prop where
  execution : PairedTimed.Related (Compile.UARTRx.program cfg) image s.storage
    (Compile.UARTRx.lift cfg s.receiver)
  wellFormed : UART.Rx.WellFormed cfg s.receiver
  mailbox : erase s.mailbox = HostResultBuffer.project s.result
  active : s.result.wasActive = s.active

theorem mailbox_next (cfg : Config) (s : ReferenceState) (pins : Chip.Pins)
    (mailbox : erase s.mailbox = HostResultBuffer.project s.result)
    (active : s.result.wasActive = s.active) :
    erase ((reference cfg).step pins s).mailbox =
      HostResultBuffer.project ((reference cfg).step pins s).result := by
  have h := congrArg HostResultBuffer.Retained.Transition.state
    (erase_step s.mailbox (mailboxCommand cfg pins s))
  simpa only [reference, mailbox, mailbox_command cfg s pins active,
    ← HostResultBuffer.next_refines] using h
  done

theorem active_next (cfg : Config) (s : ReferenceState) (pins : Chip.Pins) :
    ((reference cfg).step pins s).result.wasActive = ((reference cfg).step pins s).active := by
  simp [reference, HostResult.next, referenceOutput, PairedHost.withExecution]
  cases Engine.Reactive.busy (Compile.UARTRx.lift cfg s.receiver) <;> rfl
  done

theorem wellFormed_next (cfg : Config) (s : ReferenceState) (pins : Chip.Pins)
    (valid : UART.Rx.WellFormed cfg s.receiver) :
    UART.Rx.WellFormed cfg ((reference cfg).step pins s).receiver := by
  exact UART.Rx.BufferedSupervisor.wellFormed_step cfg ⟨s.receiver, {}, s.active⟩
    {line := (effective cfg s).incoming[cfg.input.val],
      start := (effective cfg s).command == 5,
      receiverReset := PairedEdges.resetRequested (effective cfg s).values} valid

theorem certified_next (cfg : Config) (image : PairedImage.Image) (s : ReferenceState)
    (h : Certified cfg image s) (pins : Chip.Pins)
    (rule : PairedCertified.Rule (effective cfg s).values) :
    Certified cfg image ((reference cfg).step pins s) := by
  exact ⟨core_next cfg image s h.execution rule h.wellFormed pins,
    wellFormed_next cfg s pins h.wellFormed, mailbox_next cfg s pins h.mailbox h.active,
    active_next cfg s pins⟩

structure Related (cfg : Config) (image : PairedImage.Image)
    (memory : Memory.SinglePort.Contract S 9 64)
    (actual : PairedStreamPackage.State S) (s : ReferenceState) : Prop where
  storage : PairedCoverage.view memory actual.core = s.storage.physical
  enabled : actual.enabled = s.enabled
  adapters : actual.adapters = s.adapters
  result : actual.result = s.result
  certified : Certified cfg image s

theorem policy_agrees (cfg : Config) (image : PairedImage.Image)
    (memory : Memory.SinglePort.Contract S 9 64) (actual : PairedStreamPackage.State S)
    (s : ReferenceState) (h : Related cfg image memory actual s) :
    PairedStreamPackage.policy actual = policy cfg s := by
  have regs := congrArg Prod.fst h.storage
  change (actual.core.1 : Values PairedController.Register) =
    (s.storage.registers : Values PairedController.Register) at regs
  simpa only [policy, status, PairedStreamPackage.policy, PairedStreamPackage.rawInput,
    PairedStreamOwnership.policy, PairedStreamOwnership.status,
    PairedStreamOwnership.modelPolicy, PairedStreamOwnership.modelStatus,
    regs, h.enabled, h.adapters] using
      PairedStreamOwnership.policy_related (Compile.UARTRx.program cfg) image
        ⟨s.storage, s.enabled⟩ (Compile.UARTRx.lift cfg s.receiver)
        (PairedPackage.decoded s.adapters) h.certified.execution
  done

theorem output_agrees (cfg : Config) (image : PairedImage.Image)
    (memory : Memory.SinglePort.Contract S 9 64) (actual : PairedStreamPackage.State S)
    (s : ReferenceState) (h : Related cfg image memory actual s) :
    (PairedStreamPackage.coreOutput memory actual : Values Loader.Machine.Output) =
      (referenceOutput cfg s : Values Loader.Machine.Output) := by
  have hp := congrArg PairedStream.Transition.effective (policy_agrees cfg image memory actual s h)
  have ho := congrArg (fun a : Values PairedController.Register × Memory.Sram.State 9 64 =>
    ((PairedClosed.model PairedComposition.graph).observe (effective cfg s).values a :
      Values Loader.Machine.Output)) h.storage
  have hc := PairedStreamOwnership.core_output_agrees (Compile.UARTRx.program cfg) image
    ⟨s.storage, s.enabled⟩ (Compile.UARTRx.lift cfg s.receiver)
    (PairedPackage.decoded s.adapters) h.certified.execution
  have he := congrArg PairedStream.Transition.effective
    (PairedStreamOwnership.policy_related (Compile.UARTRx.program cfg) image
      ⟨s.storage, s.enabled⟩ (Compile.UARTRx.lift cfg s.receiver)
      (PairedPackage.decoded s.adapters) h.certified.execution)
  change PairedStreamOwnership.effective ⟨s.storage, s.enabled⟩
    (PairedPackage.decoded s.adapters) = effective cfg s at he
  change ((PairedClosed.implementation PairedComposition.graph memory).observe
    (effective cfg s).values actual.core : Values Loader.Machine.Output) =
      (sideband cfg s : Values Loader.Machine.Output) at ho
  have hc' : (sideband cfg s : Values Loader.Machine.Output) =
      (referenceOutput cfg s : Values Loader.Machine.Output) := by
    unfold PairedStreamOwnership.coreOutput at hc
    rw [he] at hc
    exact hc
    done
  have ho' : (PairedStreamPackage.coreOutput memory actual : Values Loader.Machine.Output) =
      (sideband cfg s : Values Loader.Machine.Output) := by
    simpa only [PairedStreamPackage.coreOutput, PairedStreamPackage.effective,
      effective, hp] using ho
  exact ho'.trans hc'
  done

theorem related_next (cfg : Config) (image : PairedImage.Image)
    (memory : Memory.SinglePort.Contract S 9 64) (actual : PairedStreamPackage.State S)
    (s : ReferenceState) (h : Related cfg image memory actual s) (pins : Chip.Pins)
    (rule : PairedCertified.Rule (effective cfg s).values) :
    Related cfg image memory ((PairedStreamPackage.interpreted memory).step pins actual)
      ((reference cfg).step pins s) := by
  refine ⟨?_, ?_, ?_, ?_, certified_next cfg image s h.certified pins rule⟩
  case refine_1 =>
    simpa only [PairedStreamPackage.interpreted, reference, PairedStreamPackage.effective,
      policy_agrees cfg image memory actual s h, effective,
      PairedTimed.physical_refinement, PairedTimed.tracked, PairedTimed.executable] using
        (PairedTimed.physical_refinement memory).step (effective cfg s).values
          actual.core s.storage h.storage
  case refine_2 =>
    simpa only [PairedStreamPackage.interpreted, reference] using
      congrArg (fun p : PairedStream.Transition => p.state.enabled)
        (policy_agrees cfg image memory actual s h)
  case refine_3 => exact congrArg (PairedPackage.adaptersNext pins) h.adapters
  case refine_4 =>
    simp only [PairedStreamPackage.interpreted, reference,
      output_agrees cfg image memory actual s h, h.result]
  all_goals done

theorem observe_agrees (cfg : Config) (image : PairedImage.Image)
    (memory : Memory.SinglePort.Contract S 9 64) (actual : PairedStreamPackage.State S)
    (s : ReferenceState) (h : Related cfg image memory actual s) (pins : Chip.Pins) :
    ((PairedStreamPackage.interpreted memory).observe pins actual : Values Chip.Output) =
      ((reference cfg).observe pins s : Values Chip.Output) := by
  funext w p
  cases p <;> simp only [PairedStreamPackage.interpreted, reference, shown,
    PairedStream.overlay, PairedStreamPackage.registers, Extended.values,
    HostResult.State.values, PairedStream.enabledRegister, Chip.values,
    PairedStreamPackage.controller, h.enabled, h.result,
    output_agrees cfg image memory actual s h]
  done

theorem tracked_effective (cfg : Config) (image : PairedImage.Image) (s : ReferenceState)
    (h : Certified cfg image s) :
    PairedStreamOwnership.effective ⟨s.storage, s.enabled⟩ (PairedPackage.decoded s.adapters) =
      effective cfg s := by
  exact congrArg PairedStream.Transition.effective
    (PairedStreamOwnership.policy_related (Compile.UARTRx.program cfg) image
      ⟨s.storage, s.enabled⟩ (Compile.UARTRx.lift cfg s.receiver)
      (PairedPackage.decoded s.adapters) h.execution)

theorem effective_rule (cfg : Config) (image : PairedImage.Image) (s : ReferenceState)
    (h : Certified cfg image s)
    (input : PairedStreamOwnership.ReservedInput s.enabled (PairedPackage.decoded s.adapters)) :
    PairedCertified.Rule (effective cfg s).values := by
  rw [← tracked_effective cfg image s h]
  exact PairedStreamOwnership.effective_reserved_rule ⟨s.storage, s.enabled⟩
    (PairedPackage.decoded s.adapters) input

/-- These are host command boundaries, not per-edge core or memory premises.
An offered COMMIT is allowed while enabled and not resetting; the policy
rejects it. A replacement admitted while disabled starts a new epoch. -/
def Admissible (cfg : Config) : ReferenceState → List Chip.Pins → Prop
  | _, [] => True
  | s, pins :: rest =>
    PairedStreamOwnership.ReservedInput s.enabled (PairedPackage.decoded s.adapters) ∧
      Admissible cfg ((reference cfg).step pins s) rest

theorem related_run (cfg : Config) (image : PairedImage.Image)
    (memory : Memory.SinglePort.Contract S 9 64) (actual : PairedStreamPackage.State S)
    (s : ReferenceState) (h : Related cfg image memory actual s) (pins : List Chip.Pins)
    (input : Admissible cfg s pins) :
    Related cfg image memory ((PairedStreamPackage.interpreted memory).run actual pins)
      ((reference cfg).run s pins) := by
  induction pins generalizing actual s
  case nil => exact h
  case cons pin rest ih =>
    exact ih _ _ (related_next cfg image memory actual s h pin
      (effective_rule cfg image s h.certified input.1)) input.2
  done

theorem interpreted_trace (cfg : Config) (image : PairedImage.Image)
    (memory : Memory.SinglePort.Contract S 9 64) (actual : PairedStreamPackage.State S)
    (s : ReferenceState) (h : Related cfg image memory actual s) (pins : List Chip.Pins)
    (input : Admissible cfg s pins) :
    (PairedStreamPackage.interpreted memory).trace actual pins =
      (reference cfg).trace s pins := by
  induction pins generalizing actual s
  case nil => rfl
  case cons pin rest ih =>
    have next := related_next cfg image memory actual s h pin
      (effective_rule cfg image s h.certified input.1)
    simp only [Timed.Component.trace, Timed.Component.edge,
      observe_agrees cfg image memory actual s h pin,
      observe_agrees cfg image memory _ _ next pin, ih _ _ next input.2]
  done

def initialReference (_cfg : Config) (actual : PairedStreamPackage.State S)
    (storage : PairedStreamOwnership.Tracked) (epoch : Nat) : ReferenceState :=
  ⟨storage.inner, storage.enabled, UART.Rx.reset, actual.adapters, actual.result,
    ⟨(HostResultBuffer.project actual.result).pending.map (fun p => ⟨p, .unknown⟩),
      actual.result.overrun⟩, actual.result.wasActive, epoch⟩

theorem initial_related (cfg : Config) (image : PairedImage.Image)
    (memory : Memory.SinglePort.Contract S 9 64) (actual : PairedStreamPackage.State S)
    (storage : PairedStreamOwnership.Tracked)
    (physical : PairedStreamBootstrap.Related memory actual storage)
    (execution : PairedTimed.Related (Compile.UARTRx.program cfg) image storage.inner
      (Engine.Reactive.reset (Compile.UARTRx.program cfg))) (epoch : Nat) :
    Related cfg image memory actual (initialReference cfg actual storage epoch) := by
  refine ⟨physical.1, physical.2, rfl, rfl, ?_⟩
  refine ⟨?_, ?_, ?_, rfl⟩
  case refine_1 => simpa only [initialReference, Compile.UARTRx.reset_simulation] using execution
  case refine_2 => simp [initialReference, UART.Rx.WellFormed, UART.Rx.reset]
  case refine_3 => simp [initialReference, erase, HostResultBuffer.project]
  done

theorem retained_trace (cfg : Config) (image : PairedImage.Image)
    (n : Netlist PairedStream.Register PairedStream.Output PairedStream.Input)
    (hn : PairedStream.core = .ok n)
    (memory : Memory.SinglePort.Contract S 9 64) (actual : PairedStreamPackage.State S)
    (s : ReferenceState) (h : Related cfg image memory actual s) (pins : List Chip.Pins)
    (input : Admissible cfg s pins) :
    (PairedStreamPackage.executable (PairedStream.package n).component memory).trace
      actual.physical pins = (reference cfg).trace s pins := by
  rw [PairedStreamPackage.retained_trace n hn]
  exact interpreted_trace cfg image memory actual s h pins input

/-- Arbitrary power-up, the real sampled reset/release, a qualified UART image
upload, then every admitted finite control history of the emitted package.
The ledger, valid image, receiver relation and activity correspondence are all
established by the prefix rather than supplied on each execution edge. -/
theorem retained_initialized_session (cfg : Config) (image : PairedImage.Image)
    (cert : PairedImage.Corresponds (Compile.UARTRx.program cfg) image)
    (n : Netlist PairedStream.Register PairedStream.Output PairedStream.Input)
    (hn : PairedStream.core = .ok n)
    (memory : Memory.SinglePort.Contract S 9 64) (initial : PairedStreamPackage.State S)
    (resetPin idlePin : Chip.Pins) (hr : resetPin.rstN = false)
    (hi : idlePin.rstN = true) (hc : idlePin.uiIn.getLsbD 2 = true)
    (d₀ d₁ : BitVec 64) (uploadPins : List Chip.Pins) (a b : Chip.Pins)
    (upload : Serial.Session (uploadPins.map Chip.wired)
      (Loader.Machine.uploadCommands (PairedImage.upload image) d₀ d₁)) (epoch : Nat) :
    let prepared := (PairedStreamPackage.interpreted memory).run initial
      [resetPin, resetPin, resetPin, idlePin, idlePin]
    let uploaded := (PairedStreamPackage.interpreted memory).run prepared (uploadPins ++ [a, b])
    ∃ storage : PairedStreamOwnership.Tracked,
      Related cfg image memory uploaded (initialReference cfg uploaded storage epoch) ∧
      storage.enabled = false ∧
      ∀ pins : List Chip.Pins, Admissible cfg (initialReference cfg uploaded storage epoch) pins →
        (PairedStreamPackage.executable (PairedStream.package n).component memory).trace
          ((PairedStreamPackage.executable (PairedStream.package n).component memory).run
            ((PairedStreamPackage.executable (PairedStream.package n).component memory).run
              initial.physical [resetPin, resetPin, resetPin, idlePin, idlePin])
            (uploadPins ++ [a, b])) pins =
          (reference cfg).trace (initialReference cfg uploaded storage epoch) pins := by
  dsimp only
  obtain ⟨storage, physical, execution, disabled⟩ :=
    PairedStreamBootstrap.initialized_upload (Compile.UARTRx.program cfg) image cert memory initial
      resetPin idlePin hr hi hc d₀ d₁ uploadPins a b upload
  refine ⟨storage, initial_related cfg image memory _ storage physical execution epoch, disabled, ?_⟩
  intro pins admissible
  simpa only [PairedStreamPackage.retained_run n hn] using
    retained_trace cfg image n hn memory _ (initialReference cfg _ storage epoch)
      (initial_related cfg image memory _ storage physical execution epoch) pins admissible
  done

theorem packet_samples (cfg : Config) (receiver : UART.Rx.State) :
    HostResultBuffer.sampleVector (receiverPacket cfg receiver).samples = receiver.samples := by
  exact UART.Rx.BufferedSupervisor.execution_samples (fun {_} _ => 0)
    (Compile.UARTRx.lift cfg receiver)

theorem packet_outcome (cfg : Config) (receiver : UART.Rx.State) :
    HostResultBuffer.uartOutcome (receiverPacket cfg receiver) = UART.Rx.outcome receiver.samples := by
  exact congrArg UART.Rx.outcome (packet_samples cfg receiver)

/-- Only arrivals constructed in this certified epoch receive its UART origin.
An older raw mailbox packet is never interpreted by changing the active image. -/
theorem owned_arrival_origin (cfg : Config) (s : ReferenceState) (packet : OwnedPacket)
    (h : ownedArrival cfg s = some packet) :
    packet.origin = .uart s.epoch cfg ∧ packet.packet.outcome = 5 ∧
      HostResultBuffer.uartOutcome packet.packet = UART.Rx.outcome s.receiver.samples ∧
      s.receiver.phase = .finished := by
  cases active : s.active
  case false => simp [ownedArrival, receiverArrival, active] at h
  case true =>
    cases phase : s.receiver.phase <;> simp [ownedArrival, receiverArrival, active, phase] at h
    rw [← h]
    refine ⟨rfl, ?_, packet_outcome cfg s.receiver, rfl⟩
    simp [receiverPacket, Compile.UARTRx.lift, Compile.UARTRx.liftControl,
      Reactive.embed, Reactive.stopMode, phase]
    done
  all_goals done

def ownedReceipt (cfg : Config) (pins : Chip.Pins) (s : ReferenceState) : Receipt :=
  (HostResultBuffer.Retained.step s.mailbox (mailboxCommand cfg pins s)).receipt

def ownedReceipts (cfg : Config) : ReferenceState → List Chip.Pins → List Receipt
  | _, [] => []
  | s, pins :: rest => ownedReceipt cfg pins s ::
    ownedReceipts cfg ((reference cfg).step pins s) rest

def mailboxCommands (cfg : Config) : ReferenceState → List Chip.Pins →
    List (HostResultBuffer.Retained.Command OwnedPacket)
  | _, [] => []
  | s, pins :: rest => mailboxCommand cfg pins s ::
    mailboxCommands cfg ((reference cfg).step pins s) rest

def actualReceipts (memory : Memory.SinglePort.Contract S 9 64) :
    PairedStreamPackage.State S → List Chip.Pins →
      List (HostResultBuffer.Retained.Receipt HostResultBuffer.Packet)
  | _, [] => []
  | s, pins :: rest => HostResultBuffer.receipt pins (PairedStreamPackage.coreOutput memory s) s.result ::
    actualReceipts memory ((PairedStreamPackage.interpreted memory).step pins s) rest

theorem receipt_agrees (cfg : Config) (image : PairedImage.Image)
    (memory : Memory.SinglePort.Contract S 9 64) (actual : PairedStreamPackage.State S)
    (s : ReferenceState) (h : Related cfg image memory actual s) (pins : Chip.Pins) :
    HostResultBuffer.receipt pins (PairedStreamPackage.coreOutput memory actual) actual.result =
      eraseReceipt (ownedReceipt cfg pins s) := by
  have edge := congrArg HostResultBuffer.Retained.Transition.receipt
    (erase_step s.mailbox (mailboxCommand cfg pins s))
  simpa only [ownedReceipt, h.certified.mailbox, mailbox_command cfg s pins h.certified.active,
    HostResultBuffer.receipt, output_agrees cfg image memory actual s h, h.result] using edge.symm
  done

theorem receipts_agree (cfg : Config) (image : PairedImage.Image)
    (memory : Memory.SinglePort.Contract S 9 64) (actual : PairedStreamPackage.State S)
    (s : ReferenceState) (h : Related cfg image memory actual s) (pins : List Chip.Pins)
    (input : Admissible cfg s pins) :
    actualReceipts memory actual pins = (ownedReceipts cfg s pins).map eraseReceipt := by
  induction pins generalizing actual s
  case nil => rfl
  case cons pin rest ih =>
    simp only [actualReceipts, ownedReceipts, List.map_cons, receipt_agrees cfg image memory actual s h pin]
    congr 1
    exact ih _ _ (related_next cfg image memory actual s h pin
      (effective_rule cfg image s h.certified input.1)) input.2
  done

theorem mailbox_run (cfg : Config) (s : ReferenceState) (pins : List Chip.Pins) :
    (⟨((reference cfg).run s pins).mailbox, ownedReceipts cfg s pins⟩ :
      HostResultBuffer.Retained.Trace OwnedPacket) =
      HostResultBuffer.Retained.run s.mailbox (mailboxCommands cfg s pins) := by
  induction pins generalizing s
  case nil => rfl
  case cons pin rest ih =>
    have tail := congrArg (fun t : HostResultBuffer.Retained.Trace OwnedPacket =>
      (⟨t.state, ownedReceipt cfg pin s :: t.receipts⟩ : HostResultBuffer.Retained.Trace OwnedPacket))
        (ih ((reference cfg).step pin s))
    simpa only [Timed.Component.run, ownedReceipts, mailboxCommands,
      HostResultBuffer.Retained.run, ownedReceipt, reference] using tail
  done

theorem ownership_order (cfg : Config) (s : ReferenceState) (pins : List Chip.Pins) :
    s.mailbox.pending.toList ++ HostResultBuffer.Retained.accepted (ownedReceipts cfg s pins) =
      HostResultBuffer.Retained.retired (ownedReceipts cfg s pins) ++
        ((reference cfg).run s pins).mailbox.pending.toList := by
  simpa only [← mailbox_run] using
    HostResultBuffer.Retained.run_order s.mailbox (mailboxCommands cfg s pins)

theorem ownership_accounting (cfg : Config) (s : ReferenceState) (pins : List Chip.Pins) :
    s.mailbox.pending.toList.length +
        (HostResultBuffer.Retained.arrivals (mailboxCommands cfg s pins)).length =
      (HostResultBuffer.Retained.delivered (ownedReceipts cfg s pins)).length +
      (HostResultBuffer.Retained.dropped (ownedReceipts cfg s pins)).length +
      (HostResultBuffer.Retained.flushed (ownedReceipts cfg s pins)).length +
      ((reference cfg).run s pins).mailbox.pending.toList.length := by
  simpa only [← mailbox_run] using
    HostResultBuffer.Retained.run_accounting s.mailbox (mailboxCommands cfg s pins)

def tracked (s : ReferenceState) : PairedStreamOwnership.Tracked := ⟨s.storage, s.enabled⟩

theorem tracked_next (cfg : Config) (image : PairedImage.Image) (s : ReferenceState)
    (h : Certified cfg image s) (pins : Chip.Pins) :
    tracked ((reference cfg).step pins s) =
      PairedStreamOwnership.advance (tracked s) (PairedPackage.decoded s.adapters) := by
  exact (congrArg (fun p : PairedStream.Transition =>
    (⟨advance s.storage p.effective.values, p.state.enabled⟩ : PairedStreamOwnership.Tracked))
      (PairedStreamOwnership.policy_related (Compile.UARTRx.program cfg) image
        (tracked s) (Compile.UARTRx.lift cfg s.receiver)
        (PairedPackage.decoded s.adapters) h.execution)).symm

structure Operational (s : ReferenceState) : Prop where
  reserved : PairedStreamOwnership.Reserved (tracked s)
  receiver : s.enabled = true → s.receiver.phase ≠ .ready

theorem initial_operational (cfg : Config) (actual : PairedStreamPackage.State S)
    (storage : PairedStreamOwnership.Tracked) (epoch : Nat) (disabled : storage.enabled = false) :
    Operational (initialReference cfg actual storage epoch) := by
  constructor
  all_goals simp [PairedStreamOwnership.Reserved, tracked, initialReference, disabled]
  done

theorem operational_next (cfg : Config) (image : PairedImage.Image) (s : ReferenceState)
    (h : Certified cfg image s) (operational : Operational s) (pins : Chip.Pins) :
    Operational ((reference cfg).step pins s) := by
  constructor
  case reserved =>
    rw [tracked_next cfg image s h pins]
    exact PairedStreamOwnership.reserved_next (tracked s)
      (PairedPackage.decoded s.adapters) operational.reserved
  case receiver =>
    intro hn
    have hn' : (PairedStreamOwnership.advance (tracked s) (PairedPackage.decoded s.adapters)).enabled = true := by
      exact (congrArg PairedStreamOwnership.Tracked.enabled (tracked_next cfg image s h pins)).symm.trans hn
    have reset := PairedStreamOwnership.enabled_next_no_reset (tracked s)
      (PairedPackage.decoded s.adapters) hn'
    unfold tracked at reset
    rw [tracked_effective cfg image s h] at reset
    have live : s.receiver.phase ≠ .ready ∨ ((effective cfg s).command == 5) = true := by
      cases enabled : s.enabled
      case false =>
        have start := PairedStreamOwnership.enabling_starts (tracked s)
          (PairedPackage.decoded s.adapters) enabled hn'
        unfold tracked at start
        rw [tracked_effective cfg image s h] at start
        exact Or.inr (by simp [start])
      case true => exact Or.inl (operational.receiver enabled)
      done
    change (UART.Rx.step cfg s.receiver _ _ _).phase ≠ .ready
    rw [reset]
    exact UART.Rx.BufferedSupervisor.step_not_ready cfg s.receiver _ _ live
  done

theorem physical_mode (cfg : Config) (image : PairedImage.Image)
    (memory : Memory.SinglePort.Contract S 9 64) (actual : PairedStreamPackage.State S)
    (s : ReferenceState) (h : Related cfg image memory actual s) :
    actual.core.1 .mode = (Reactive.embed (Compile.UARTRx.lift cfg s.receiver)).mode := by
  exact (congrArg (fun a : Values PairedController.Register × Memory.Sram.State 9 64 =>
    a.1 .mode) h.storage).trans (congrArg Reactive.State.mode h.certified.execution.2.2)

/-- STOP aborts/disarms the receiver. The mailbox still consumes the ordinary
old-state arrival on this edge, including a completion coincident with STOP. -/
theorem stop_transition (cfg : Config) (s : ReferenceState) (pins : Chip.Pins)
    (command : (PairedPackage.decoded s.adapters).command = 6)
    (data : (PairedPackage.decoded s.adapters).data = 0) :
    ((reference cfg).step pins s).receiver = UART.Rx.reset ∧
      ((reference cfg).step pins s).enabled = false ∧
      ((reference cfg).step pins s).mailbox =
        (HostResultBuffer.Retained.step s.mailbox (mailboxCommand cfg pins s)).state := by
  simp [reference, effective, policy, PairedStream.step, PairedStream.stopping,
    command, data, PairedEdges.resetRequested, Loader.Machine.Inputs.values, UART.Rx.step]
  done

def Quiet (s : ReferenceState) : Prop :=
  (PairedPackage.decoded s.adapters).init = false ∧
    (PairedPackage.decoded s.adapters).reset = false ∧
    (PairedPackage.decoded s.adapters).command = 0

theorem quiet_enabled (cfg : Config) (s : ReferenceState) (enabled : s.enabled = true)
    (quiet : Quiet s) (pins : Chip.Pins) :
    ((reference cfg).step pins s).enabled = true := by
  have modes := UART.Rx.BufferedSupervisor.mode_not_failure cfg s.receiver
  simp [reference, policy, PairedStream.step, PairedStream.resetting, PairedStream.stopping,
    PairedStream.arming, PairedStream.failed, status, enabled, quiet.1, quiet.2.1, quiet.2.2]
  exact modes
  done

theorem quiet_reset (cfg : Config) (s : ReferenceState) (quiet : Quiet s) :
    PairedEdges.resetRequested (effective cfg s).values = false := by
  simp [PairedEdges.resetRequested, effective, policy, PairedStream.step,
    PairedStream.stopping, PairedStream.resetting, PairedStream.arming,
    Loader.Machine.Inputs.values, quiet.1, quiet.2.1, quiet.2.2]
  split <;> decide +kernel
  done

theorem quiet_activation (cfg : Config) (s : ReferenceState) (operational : Operational s)
    (enabled : s.enabled = true) (quiet : Quiet s) :
    (UART.Rx.busy s.receiver || ((effective cfg s).command == 5)) = true := by
  cases busy : UART.Rx.busy s.receiver
  case true => rfl
  case false =>
    have finished := UART.Rx.BufferedSupervisor.stopped_finished s.receiver busy
      (operational.receiver enabled)
    have mode := (UART.Rx.BufferedSupervisor.mode_finished cfg s.receiver).mpr finished
    have fields := operational.reserved enabled
    change s.storage.registers .valid = 1 ∧ s.storage.registers .pending = 0 at fields
    simp only [BitVec.ofNat_eq_ofNat] at fields
    simp [effective, policy, PairedStream.step, PairedStream.stopping, PairedStream.resetting,
      PairedStream.arming, PairedStream.rearming, status, enabled, quiet.1, quiet.2.1, quiet.2.2,
      mode, fields.1, fields.2]
  done

def logical (s : ReferenceState) : UART.Rx.BufferedSupervisor.State :=
  ⟨s.receiver, HostResultBuffer.uartProject s.result, s.active⟩

def logicalInput (cfg : Config) (pins : Chip.Pins) (s : ReferenceState) :
    UART.Rx.BufferedSupervisor.Input :=
  {line := (effective cfg s).incoming[cfg.input.val],
    start := !PairedEdges.resetRequested (effective cfg s).values && ((effective cfg s).command == 5),
    receiverReset := PairedEdges.resetRequested (effective cfg s).values,
    flush := HostResult.resetting pins s.result,
    take := HostResult.consuming s.result, clearOverrun := HostResult.clearing s.result}

theorem start_value (cfg : Config) (image : PairedImage.Image) (s : ReferenceState)
    (h : Certified cfg image s) (rule : PairedCertified.Rule (effective cfg s).values) :
    referenceOutput cfg s (.control .start) = BitVec.ofBool
      (!PairedEdges.resetRequested (effective cfg s).values &&
        !UART.Rx.busy s.receiver && ((effective cfg s).command == 5)) := by
  have r : PairedCertified.Rule
      (PairedStreamOwnership.effective (tracked s) (PairedPackage.decoded s.adapters)).values := by
    simpa only [tracked, tracked_effective cfg image s h] using rule
  have start := PairedStreamOwnership.start_value (Compile.UARTRx.program cfg) image
    (tracked s) (Compile.UARTRx.lift cfg s.receiver) (PairedPackage.decoded s.adapters) h.execution r
  unfold PairedStreamOwnership.coreOutput tracked at start
  rw [tracked_effective cfg image s h] at start
  simpa only [referenceOutput, sideband, PairedHost.withExecution, Compile.UARTRx.busy_lift] using start
  done

theorem receiver_gated_start (cfg : Config) (receiver : UART.Rx.State)
    (reset start line : Bool) :
    UART.Rx.step cfg receiver reset start line =
      UART.Rx.step cfg receiver reset (!reset && start) line := by
  cases reset <;> simp [UART.Rx.step]
  done

theorem logical_next (cfg : Config) (image : PairedImage.Image) (s : ReferenceState)
    (h : Certified cfg image s) (pins : Chip.Pins)
    (rule : PairedCertified.Rule (effective cfg s).values) :
    logical ((reference cfg).step pins s) =
      (UART.Rx.BufferedSupervisor.step cfg (logical s) (logicalInput cfg pins s)).state := by
  have buffer := UART.Rx.BufferedSupervisor.observer_step cfg (logical s) (logicalInput cfg pins s)
    pins (referenceOutput cfg s) s.result rfl h.active
    (UART.Rx.BufferedSupervisor.execution_coreCorresponds cfg s.receiver (sideband cfg s)) rfl rfl rfl
  simp only [logical, reference, UART.Rx.BufferedSupervisor.step, logicalInput,
    UART.Rx.BufferedSupervisor.State.mk.injEq]
  refine ⟨receiver_gated_start cfg s.receiver _ _ _,
    congrArg UART.Rx.Buffer.Transition.state buffer, ?_⟩
  simp only [start_value cfg image s h rule, Compile.UARTRx.busy_lift]
  cases UART.Rx.busy s.receiver <;>
    cases PairedEdges.resetRequested (effective cfg s).values <;>
    cases (effective cfg s).command == 5 <;> rfl
  done

def runN (cfg : Config) (s : ReferenceState) (incoming : Nat → Chip.Pins) : Nat → ReferenceState
  | 0 => s
  | n + 1 => (reference cfg).step (incoming (n + 1)) (runN cfg s incoming n)

def actualRunN (memory : Memory.SinglePort.Contract S 9 64) (s : PairedStreamPackage.State S)
    (incoming : Nat → Chip.Pins) : Nat → PairedStreamPackage.State S
  | 0 => s
  | n + 1 => (PairedStreamPackage.interpreted memory).step (incoming (n + 1))
      (actualRunN memory s incoming n)

def QuietHistory (cfg : Config) (s : ReferenceState) (incoming : Nat → Chip.Pins) : Prop :=
  ∀ n, Quiet (runN cfg s incoming n)

theorem quiet_rule (_cfg : Config) (s : ReferenceState) (quiet : Quiet s) :
    PairedStreamOwnership.ReservedInput s.enabled (PairedPackage.decoded s.adapters) := by
  exact ⟨quiet.1, Or.inl (by rw [quiet.2.2]; decide +kernel)⟩

theorem certified_runN (cfg : Config) (image : PairedImage.Image) (s : ReferenceState)
    (h : Certified cfg image s) (incoming : Nat → Chip.Pins)
    (quiet : QuietHistory cfg s incoming) (n : Nat) : Certified cfg image (runN cfg s incoming n) := by
  induction n
  case zero => exact h
  case succ n ih =>
    exact certified_next cfg image _ ih (incoming (n + 1))
      (effective_rule cfg image _ ih (quiet_rule cfg _ (quiet n)))

theorem operational_runN (cfg : Config) (image : PairedImage.Image) (s : ReferenceState)
    (h : Certified cfg image s) (operational : Operational s) (incoming : Nat → Chip.Pins)
    (quiet : QuietHistory cfg s incoming) (n : Nat) : Operational (runN cfg s incoming n) := by
  induction n
  case zero => exact operational
  case succ n ih =>
    exact operational_next cfg image _ (certified_runN cfg image s h incoming quiet n)
      ih (incoming (n + 1))

theorem enabled_runN (cfg : Config) (s : ReferenceState) (enabled : s.enabled = true)
    (incoming : Nat → Chip.Pins) (quiet : QuietHistory cfg s incoming) (n : Nat) :
    (runN cfg s incoming n).enabled = true := by
  induction n
  case zero => exact enabled
  case succ n ih => exact quiet_enabled cfg _ ih (quiet n) (incoming (n + 1))

theorem related_runN (cfg : Config) (image : PairedImage.Image)
    (memory : Memory.SinglePort.Contract S 9 64) (actual : PairedStreamPackage.State S)
    (s : ReferenceState) (h : Related cfg image memory actual s) (incoming : Nat → Chip.Pins)
    (quiet : QuietHistory cfg s incoming) (n : Nat) :
    Related cfg image memory (actualRunN memory actual incoming n) (runN cfg s incoming n) := by
  induction n
  case zero => exact h
  case succ n ih =>
    exact related_next cfg image memory _ _ ih (incoming (n + 1))
      (effective_rule cfg image _ ih.certified (quiet_rule cfg _ (quiet n)))

def inputHistory (cfg : Config) (s : ReferenceState) (incoming : Nat → Chip.Pins) (n : Nat) :
    UART.Rx.BufferedSupervisor.Input :=
  logicalInput cfg (incoming n) (runN cfg s incoming (n - 1))

theorem logical_runN (cfg : Config) (image : PairedImage.Image) (s : ReferenceState)
    (h : Certified cfg image s) (incoming : Nat → Chip.Pins)
    (quiet : QuietHistory cfg s incoming) (n : Nat) :
    logical (runN cfg s incoming n) =
      UART.Rx.BufferedSupervisor.run cfg (logical s) (inputHistory cfg s incoming) n := by
  induction n
  case zero => rfl
  case succ n ih =>
    rw [runN, UART.Rx.BufferedSupervisor.run, ← ih]
    simpa only [inputHistory, Nat.add_sub_cancel] using
      logical_next cfg image _ (certified_runN cfg image s h incoming quiet n) (incoming (n + 1))
        (effective_rule cfg image _ (certified_runN cfg image s h incoming quiet n)
          (quiet_rule cfg _ (quiet n)))
  done

theorem released_runN (cfg : Config) (s : ReferenceState)
    (released : s.result.resetFirst = true ∧ s.result.resetSecond = true)
    (incoming : Nat → Chip.Pins) (pinsReleased : ∀ n, (incoming n).rstN = true) (n : Nat) :
    (runN cfg s incoming n).result.resetFirst = true ∧
      (runN cfg s incoming n).result.resetSecond = true := by
  induction n
  case zero => exact released
  case succ n ih => exact ⟨pinsReleased (n + 1), ih.1⟩
  done

theorem inputHistory_quiet (cfg : Config) (s : ReferenceState)
    (released : s.result.resetFirst = true ∧ s.result.resetSecond = true)
    (incoming : Nat → Chip.Pins) (pinsReleased : ∀ n, (incoming n).rstN = true)
    (quiet : QuietHistory cfg s incoming) (n : Nat) :
    (inputHistory cfg s incoming n).receiverReset = false ∧
      (inputHistory cfg s incoming n).flush = false := by
  exact ⟨quiet_reset cfg _ (quiet (n - 1)), by
    simp only [inputHistory, logicalInput, HostResult.resetting, pinsReleased n,
      (released_runN cfg s released incoming pinsReleased (n - 1)).1,
      (released_runN cfg s released incoming pinsReleased (n - 1)).2]
    rfl⟩
  done

theorem inputHistory_active (cfg : Config) (image : PairedImage.Image) (s : ReferenceState)
    (certified : Certified cfg image s) (operational : Operational s)
    (enabled : s.enabled = true) (incoming : Nat → Chip.Pins)
    (quiet : QuietHistory cfg s incoming) (n : Nat) :
    (UART.Rx.busy (UART.Rx.BufferedSupervisor.run cfg (logical s)
      (inputHistory cfg s incoming) n).receiver ||
        (inputHistory cfg s incoming (n + 1)).start) = true := by
  rw [← logical_runN cfg image s certified incoming quiet n]
  simpa only [logical, inputHistory, Nat.add_sub_cancel, logicalInput,
    quiet_reset cfg _ (quiet n), Bool.not_false, Bool.true_and] using
      quiet_activation cfg _ (operational_runN cfg image s certified operational incoming quiet n)
        (enabled_runN cfg s enabled incoming quiet n) (quiet n)
  done

/-- UART decoding is attached only to the normal-completion packet generated
by the certified current receiver, never to an unrelated retained packet. -/
theorem arrival_agrees (cfg : Config) (image : PairedImage.Image)
    (memory : Memory.SinglePort.Contract S 9 64) (actual : PairedStreamPackage.State S)
    (s : ReferenceState) (related : Related cfg image memory actual s) :
    (HostResultBuffer.arrival (PairedStreamPackage.coreOutput memory actual) actual.result).map
      HostResultBuffer.uartOutcome = UART.Rx.BufferedSupervisor.arrival (logical s) := by
  rw [output_agrees cfg image memory actual s related, related.result]
  exact UART.Rx.BufferedSupervisor.arrival_refines cfg s.receiver (referenceOutput cfg s)
    s.result s.active related.certified.active
      (UART.Rx.BufferedSupervisor.execution_coreCorresponds cfg s.receiver (sideband cfg s))
  done

/-- Strong timing at a certified ARM boundary. Quiet consumed commands derive
all continuing activation obligations; receiver timing and sampled-line age
remain explicit wire-environment premises. Consumer stalls are unrestricted. -/
theorem quiet_receive_series (t : UART.Link.Timing) (image : PairedImage.Image)
    (memory : Memory.SinglePort.Contract S 9 64) (actual : PairedStreamPackage.State S)
    (s : ReferenceState) (related : Related t.rx image memory actual s)
    (operational : Operational s) (enabled : s.enabled = true)
    (receiver : s.receiver = UART.Rx.initial) (active : s.active = true)
    (released : s.result.resetFirst = true ∧ s.result.resetSecond = true)
    (incoming : Nat → Chip.Pins) (pinsReleased : ∀ n, (incoming n).rstN = true)
    (quiet : QuietHistory t.rx s incoming) (latency : UART.Link.Latency)
    (bytes : List (BitVec 8)) (age : Nat → Nat) (safe : UART.StreamLink.Safe t latency)
    (within : latency.Contains age)
    (line : ∀ n, (inputHistory t.rx s incoming n).line = UART.StreamLink.sampled t bytes age n) :
    ∃ frames, frames.map UART.Rx.Stream.FrameSpec.byte = bytes ∧
      UART.StreamLink.Windows t latency frames ∧
      ∀ n, n ≤ UART.Rx.Stream.horizon t.rx frames →
        (HostResultBuffer.arrival
          (PairedStreamPackage.coreOutput memory (actualRunN memory actual incoming n))
          (actualRunN memory actual incoming n).result).map HostResultBuffer.uartOutcome =
            UART.Rx.Stream.expected t.rx frames n := by
  have start : logical s = ⟨UART.Rx.initial, HostResultBuffer.uartProject s.result, true⟩ := by
    simp only [logical, receiver, active]
  obtain ⟨frames, payloads, windows, pulses⟩ := UART.Rx.BufferedSupervisor.phase_receive_series
    t latency bytes age (HostResultBuffer.uartProject s.result) (inputHistory t.rx s incoming)
    (inputHistory_quiet t.rx s released incoming pinsReleased quiet)
    (by rw [← start]; exact inputHistory_active t.rx image s related.certified operational enabled incoming quiet)
    safe within line
  refine ⟨frames, payloads, windows, fun n hn => ?_⟩
  rw [arrival_agrees t.rx image memory _ _ (related_runN t.rx image memory actual s related incoming quiet n),
    logical_runN t.rx image s related.certified incoming quiet n, start]
  exact pulses n hn
  done

theorem effective_incoming (cfg : Config) (s : ReferenceState) :
    (effective cfg s).incoming = s.adapters.second.incoming := by rfl

/-- The first two consumed edges use the initial two sampler stages. -/
theorem line_initial (cfg : Config) (s : ReferenceState) (incoming : Nat → Chip.Pins) :
    (inputHistory cfg s incoming 1).line = s.adapters.second.incoming.getLsbD cfg.input.val ∧
    (inputHistory cfg s incoming 2).line = s.adapters.first.incoming.getLsbD cfg.input.val := by
  exact ⟨rfl, rfl⟩
  done

/-- Physical input edge n+1 is consumed two package edges later. This theorem
states the exact digital sampler delay, separately from UART clock safety. -/
theorem line_delayed (cfg : Config) (s : ReferenceState) (incoming : Nat → Chip.Pins) (n : Nat) :
    (inputHistory cfg s incoming (n + 3)).line =
      (incoming (n + 1)).uioIn.getLsbD cfg.input.val := by
  simp only [inputHistory, logicalInput, effective_incoming]
  have index : n + 3 - 1 = n + 2 := by omega
  rw [index, runN, runN]
  simp only [reference, PairedPackage.adaptersNext, Chip.wired, ← BitVec.getLsbD_eq_getElem,
    BitVec.getLsbD_extractLsb', cfg.input.isLt, decide_true, Bool.true_and, Nat.zero_add]
  done

/-- A physical wire history including the two initial sampler stages. The
age/clock safety condition is supplied separately by the UART timing theorem. -/
def Samples (cfg : Config) (s : ReferenceState) (incoming : Nat → Chip.Pins)
    (wire : Nat → Bool) : Prop :=
  s.adapters.second.incoming.getLsbD cfg.input.val = wire 0 ∧
  s.adapters.second.incoming.getLsbD cfg.input.val = wire 1 ∧
  s.adapters.first.incoming.getLsbD cfg.input.val = wire 2 ∧
  ∀ n, (incoming (n + 1)).uioIn.getLsbD cfg.input.val = wire (n + 3)

theorem sampled_line (cfg : Config) (s : ReferenceState) (incoming : Nat → Chip.Pins)
    (wire : Nat → Bool) (samples : Samples cfg s incoming wire) (n : Nat) :
    (inputHistory cfg s incoming n).line = wire n := by
  cases n
  case zero => exact samples.1
  case succ n =>
    cases n
    case zero => exact samples.2.1
    case succ n =>
      cases n
      case zero => exact (line_initial cfg s incoming).2.trans samples.2.2.1
      case succ n => exact (line_delayed cfg s incoming n).trans (samples.2.2.2 n)
  done

/-- The package timing corollary consumes actual bidirectional input-pad
values with the exact two-stage prefix, and arbitrary consumer/clear controls. -/
theorem quiet_wire_receive_series (t : UART.Link.Timing) (image : PairedImage.Image)
    (memory : Memory.SinglePort.Contract S 9 64) (actual : PairedStreamPackage.State S)
    (s : ReferenceState) (related : Related t.rx image memory actual s)
    (operational : Operational s) (enabled : s.enabled = true)
    (receiver : s.receiver = UART.Rx.initial) (active : s.active = true)
    (released : s.result.resetFirst = true ∧ s.result.resetSecond = true)
    (incoming : Nat → Chip.Pins) (pinsReleased : ∀ n, (incoming n).rstN = true)
    (quiet : QuietHistory t.rx s incoming) (latency : UART.Link.Latency)
    (bytes : List (BitVec 8)) (age : Nat → Nat) (safe : UART.StreamLink.Safe t latency)
    (within : latency.Contains age)
    (samples : Samples t.rx s incoming (UART.StreamLink.sampled t bytes age)) :
    ∃ frames, frames.map UART.Rx.Stream.FrameSpec.byte = bytes ∧
      UART.StreamLink.Windows t latency frames ∧
      ∀ n, n ≤ UART.Rx.Stream.horizon t.rx frames →
        (HostResultBuffer.arrival
          (PairedStreamPackage.coreOutput memory (actualRunN memory actual incoming n))
          (actualRunN memory actual incoming n).result).map HostResultBuffer.uartOutcome =
            UART.Rx.Stream.expected t.rx frames n := by
  exact quiet_receive_series t image memory actual s related operational enabled receiver active
    released incoming pinsReleased quiet latency bytes age safe within
      (sampled_line t.rx s incoming _ samples)
  done

def IdleAdapters (s : ReferenceState) : Prop :=
  s.adapters.receiver.fire = false ∧ Serial.Idle s.adapters.first ∧ Serial.Idle s.adapters.second

theorem idle_quiet (s : ReferenceState) (idle : IdleAdapters s) : Quiet s := by
  exact Serial.feed_quiet s.adapters.second s.adapters.receiver idle.2.2.1 idle.1
  done

theorem idle_adapters_next (cfg : Config) (s : ReferenceState) (idle : IdleAdapters s)
    (pins : Chip.Pins) (pinIdle : Serial.Idle (Chip.wired pins)) :
    IdleAdapters ((reference cfg).step pins s) := by
  refine ⟨?_, pinIdle, idle.2.1⟩
  simp only [reference, PairedPackage.adaptersNext, Serial.next, Serial.taking,
    idle.2.2.1, idle.2.2.2, Bool.not_true, Bool.and_false, Bool.false_and]
  done

theorem idle_adapters_runN (cfg : Config) (s : ReferenceState) (idle : IdleAdapters s)
    (incoming : Nat → Chip.Pins) (pinIdle : ∀ n, Serial.Idle (Chip.wired (incoming n))) (n : Nat) :
    IdleAdapters (runN cfg s incoming n) := by
  induction n
  case zero => exact idle
  case succ n ih => exact idle_adapters_next cfg _ ih (incoming (n + 1)) (pinIdle (n + 1))
  done

theorem idle_quiet_history (cfg : Config) (s : ReferenceState) (idle : IdleAdapters s)
    (incoming : Nat → Chip.Pins) (pinIdle : ∀ n, Serial.Idle (Chip.wired (incoming n))) :
    QuietHistory cfg s incoming := by
  exact fun n => idle_quiet _ (idle_adapters_runN cfg s idle incoming pinIdle n)
  done

theorem idle_released (pins : Chip.Pins) (idle : Serial.Idle (Chip.wired pins)) :
    pins.rstN = true := by
  have h : (!pins.rstN) = false := idle.1
  cases b : pins.rstN <;> simp_all
  done

/-- A settled idle serial interface supplies quiet consumed controls directly
from physical pins; no per-edge execution or SRAM observation is assumed. -/
theorem idle_wire_receive_series (t : UART.Link.Timing) (image : PairedImage.Image)
    (memory : Memory.SinglePort.Contract S 9 64) (actual : PairedStreamPackage.State S)
    (s : ReferenceState) (related : Related t.rx image memory actual s)
    (operational : Operational s) (enabled : s.enabled = true)
    (receiver : s.receiver = UART.Rx.initial) (active : s.active = true)
    (released : s.result.resetFirst = true ∧ s.result.resetSecond = true)
    (idle : IdleAdapters s) (incoming : Nat → Chip.Pins)
    (pinIdle : ∀ n, Serial.Idle (Chip.wired (incoming n)))
    (latency : UART.Link.Latency) (bytes : List (BitVec 8)) (age : Nat → Nat)
    (safe : UART.StreamLink.Safe t latency) (within : latency.Contains age)
    (samples : Samples t.rx s incoming (UART.StreamLink.sampled t bytes age)) :
    ∃ frames, frames.map UART.Rx.Stream.FrameSpec.byte = bytes ∧
      UART.StreamLink.Windows t latency frames ∧
      ∀ n, n ≤ UART.Rx.Stream.horizon t.rx frames →
        (HostResultBuffer.arrival
          (PairedStreamPackage.coreOutput memory (actualRunN memory actual incoming n))
          (actualRunN memory actual incoming n).result).map HostResultBuffer.uartOutcome =
            UART.Rx.Stream.expected t.rx frames n := by
  exact quiet_wire_receive_series t image memory actual s related operational enabled receiver active
    released incoming (fun n => idle_released _ (pinIdle n))
    (idle_quiet_history t.rx s idle incoming pinIdle) latency bytes age safe within samples
  done

/-- The digital sampler's two package edges correspond to two RX clock ticks
in the common-time UART link model. -/
theorem sampled_two_ticks (t : UART.Link.Timing) (bytes : List (BitVec 8)) (n : Nat) :
    UART.StreamLink.sampled t bytes (fun _ => 2 * t.rxTick) (n + 3) =
      UART.StreamLink.sampled t bytes (fun _ => 0) (n + 1) := by
  have edge : t.edge (n + 3) = t.edge (n + 1) + 2 * t.rxTick := by
    simp only [UART.Link.Timing.edge, Nat.add_mul]
    omega
  simp only [UART.StreamLink.sampled, UART.Link.observe, edge, Nat.add_lt_add_iff_right,
    Nat.add_sub_add_right, Nat.add_zero]
  done

end Pinwheel.Hardware.Storage.PairedStreamSession
