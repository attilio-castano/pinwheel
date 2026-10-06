import Pinwheel.Hardware.Storage.PairedStreamSession

/-! ARM admission at the single delivered command edge. The quiet suffix is
kept explicit: draining the serial pipeline also advances the UART receiver. -/
namespace Pinwheel.Hardware.Storage.PairedStreamArm
open Pinwheel.Hardware Loader
open PairedStreamSession
open UART.Rx (Config)
set_option backward.isDefEq.respectTransparency false

structure Ready (s : ReferenceState) : Prop where
  disabled : s.enabled = false
  receiver : s.receiver = UART.Rx.reset
  pending : s.storage.registers .pending = 0
  released : s.result.resetFirst = true ∧ s.result.resetSecond = true

theorem quiet_effective (cfg : Config) (s : ReferenceState)
    (disabled : s.enabled = false) (quiet : Quiet s) (pins : Chip.Pins) :
    effective cfg s = PairedPackage.decoded s.adapters ∧
      ((reference cfg).step pins s).enabled = false := by
  simp [effective, policy, reference, PairedStream.step, PairedStream.resetting,
    PairedStream.stopping, PairedStream.arming, PairedStream.rearming,
    disabled, quiet.1, quiet.2.1, quiet.2.2]
  cases decoded : PairedPackage.decoded s.adapters
  simp only [Quiet, decoded] at quiet
  simp [quiet.1, quiet.2.1, quiet.2.2]
  done

theorem quiet_ready_next (cfg : Config) (s : ReferenceState) (ready : Ready s)
    (quiet : Quiet s) (pins : Chip.Pins) (released : pins.rstN = true) :
    Ready ((reference cfg).step pins s) := by
  refine ⟨(quiet_effective cfg s ready.disabled quiet pins).2, ?_, ?_, ?_⟩
  case refine_1 =>
    change UART.Rx.step cfg s.receiver _ _ _ = UART.Rx.reset
    rw [quiet_reset cfg s quiet, (quiet_effective cfg s ready.disabled quiet pins).1, ready.receiver]
    simp [UART.Rx.step, UART.Rx.busy, UART.Rx.reset, quiet.2.2]
    done
  case refine_2 =>
    change (PairedCoverage.advance s.storage (effective cfg s).values).registers .pending = 0
    rw [(quiet_effective cfg s ready.disabled quiet pins).1]
    exact (PairedStreamOwnership.quiet_pending s.storage _ quiet).trans ready.pending
    done
  case refine_3 => exact ⟨released, ready.released.1⟩
  done

theorem arm_effective (cfg : Config) (image : PairedImage.Image) (s : ReferenceState)
    (certified : Certified cfg image s) (ready : Ready s)
    (command : Machine.Carries (PairedPackage.decoded s.adapters) 6 1) (pins : Chip.Pins) :
    (effective cfg s).command = 5 ∧ ((reference cfg).step pins s).enabled = true := by
  have raw := Machine.carries_plain command (by decide +kernel)
  have admitted := PairedStreamOwnership.arm_admitted (tracked s)
    (PairedPackage.decoded s.adapters) ready.disabled certified.execution.1.valid ready.pending
      (by
        rw [PairedStreamOwnership.status_related (Compile.UARTRx.program cfg) image
          (tracked s) (Compile.UARTRx.lift cfg s.receiver) certified.execution]
        simp [PairedStreamOwnership.modelStatus, PairedStream.busy, ready.receiver,
          UART.Rx.reset, Compile.UARTRx.lift, Compile.UARTRx.liftControl,
          Reactive.embed, Reactive.stopMode]
        done) raw.1 raw.2.1 raw.2.2.1 raw.2.2.2
  exact ⟨(congrArg Machine.Inputs.command
      (tracked_effective cfg image s certified)).symm.trans admitted.1,
    (congrArg PairedStreamOwnership.Tracked.enabled
      (tracked_next cfg image s certified pins)).trans admitted.2⟩
  done

theorem arm_rule (_cfg : Config) (s : ReferenceState)
    (command : Machine.Carries (PairedPackage.decoded s.adapters) 6 1) :
    PairedStreamOwnership.ReservedInput s.enabled (PairedPackage.decoded s.adapters) := by
  simp [PairedStreamOwnership.ReservedInput, (Machine.carries_plain command (by decide +kernel)).1,
    (Machine.carries_plain command (by decide +kernel)).2.2.1]

theorem arm_next (cfg : Config) (image : PairedImage.Image) (s : ReferenceState)
    (certified : Certified cfg image s) (ready : Ready s)
    (command : Machine.Carries (PairedPackage.decoded s.adapters) 6 1)
    (pins : Chip.Pins) (released : pins.rstN = true) :
    ((reference cfg).step pins s).receiver = UART.Rx.initial ∧
      ((reference cfg).step pins s).enabled = true ∧
      ((reference cfg).step pins s).active = true ∧
      Operational ((reference cfg).step pins s) ∧
      ((reference cfg).step pins s).mailbox =
        (HostResultBuffer.Retained.step s.mailbox (.cycle none
          (HostResult.consuming s.result) (HostResult.clearing s.result))).state := by
  have admitted := arm_effective cfg image s certified ready command pins
  have noreset : PairedEdges.resetRequested (effective cfg s).values = false := by
    rw [← tracked_effective cfg image s certified]
    exact PairedStreamOwnership.enabled_next_no_reset (tracked s) _
      ((congrArg PairedStreamOwnership.Tracked.enabled
        (tracked_next cfg image s certified pins)).symm.trans admitted.2)
    done
  have noflush : HostResult.resetting pins s.result = false := by
    simp [HostResult.resetting, released, ready.released.1, ready.released.2]
  refine ⟨?_, admitted.2, ?_, operational_next cfg image s certified
    ⟨PairedStreamOwnership.reserved_disabled (tracked s) ready.disabled,
      by simp [ready.disabled]⟩ pins, ?_⟩
  case refine_1 =>
    simp [reference, noreset, admitted.1, ready.receiver, UART.Rx.step, UART.Rx.busy, UART.Rx.reset]
  case refine_2 =>
    simp [reference, noflush,
      start_value cfg image s certified (effective_rule cfg image s certified (arm_rule cfg s command)),
      noreset, admitted.1, ready.receiver, Compile.UARTRx.busy_lift, UART.Rx.busy, UART.Rx.reset]
  case refine_3 =>
    simp [reference, mailboxCommand, noflush, ownedArrival, receiverArrival, ready.receiver, UART.Rx.reset]
  done

theorem initial_ready (cfg : Config) (actual : PairedStreamPackage.State S)
    (storage : PairedStreamOwnership.Tracked) (epoch : Nat)
    (disabled : storage.enabled = false) (pending : storage.inner.registers .pending = 0)
    (released : actual.result.resetFirst = true ∧ actual.result.resetSecond = true) :
    Ready (initialReference cfg actual storage epoch) :=
  ⟨disabled, rfl, pending, released⟩

theorem arm_receipt (cfg : Config) (s : ReferenceState) (ready : Ready s)
    (pins : Chip.Pins) (released : pins.rstN = true) :
    ownedReceipt cfg pins s = (HostResultBuffer.Retained.step s.mailbox
      (.cycle none (HostResult.consuming s.result) (HostResult.clearing s.result))).receipt := by
  simp [ownedReceipt, mailboxCommand, HostResult.resetting, released,
    ready.released.1, ready.released.2, ownedArrival, receiverArrival, ready.receiver, UART.Rx.reset]

/-- The admitted edge, before the trailing quiet drain samples. -/
structure Admission (cfg : Config) (image : PairedImage.Image)
    (memory : Memory.SinglePort.Contract S 9 64) (actual : PairedStreamPackage.State S)
    (s : ReferenceState) (beforePins : List Chip.Pins) (armPin : Chip.Pins)
    (suffix : List Chip.Pins) : Prop where
  quietPrefix : Machine.Delivers (Chip.consumed s.adapters beforePins) []
  ready : Ready ((reference cfg).run s beforePins)
  before : Related cfg image memory ((PairedStreamPackage.interpreted memory).run actual beforePins)
    ((reference cfg).run s beforePins)
  command : Machine.Carries (PairedPackage.decoded ((reference cfg).run s beforePins).adapters) 6 1
  after : Related cfg image memory
    ((PairedStreamPackage.interpreted memory).step armPin
      ((PairedStreamPackage.interpreted memory).run actual beforePins))
    ((reference cfg).step armPin ((reference cfg).run s beforePins))
  receiver : ((reference cfg).step armPin ((reference cfg).run s beforePins)).receiver = UART.Rx.initial
  enabled : ((reference cfg).step armPin ((reference cfg).run s beforePins)).enabled = true
  active : ((reference cfg).step armPin ((reference cfg).run s beforePins)).active = true
  operational : Operational ((reference cfg).step armPin ((reference cfg).run s beforePins))
  released :
    ((reference cfg).step armPin ((reference cfg).run s beforePins)).result.resetFirst = true ∧
      ((reference cfg).step armPin ((reference cfg).run s beforePins)).result.resetSecond = true
  mailbox : ((reference cfg).step armPin ((reference cfg).run s beforePins)).mailbox =
    (HostResultBuffer.Retained.step ((reference cfg).run s beforePins).mailbox
      (.cycle none (HostResult.consuming ((reference cfg).run s beforePins).result)
        (HostResult.clearing ((reference cfg).run s beforePins).result))).state
  quietSuffix : Machine.Delivers
    (Chip.consumed ((reference cfg).step armPin ((reference cfg).run s beforePins)).adapters suffix) []

theorem Admission.receipt (admitted : Admission cfg image memory actual s beforePins armPin suffix) :
    ownedReceipt cfg armPin ((reference cfg).run s beforePins) =
      (HostResultBuffer.Retained.step ((reference cfg).run s beforePins).mailbox
        (.cycle none (HostResult.consuming ((reference cfg).run s beforePins).result)
          (HostResult.clearing ((reference cfg).run s beforePins).result))).receipt :=
  arm_receipt cfg _ admitted.ready armPin admitted.released.1

theorem delivered_arm (cfg : Config) (image : PairedImage.Image)
    (memory : Memory.SinglePort.Contract S 9 64) (actual : PairedStreamPackage.State S)
    (s : ReferenceState) (related : Related cfg image memory actual s) (ready : Ready s)
    (pins : List Chip.Pins) (released : ∀ pin ∈ pins, pin.rstN = true)
    (delivered : Machine.Delivers (Chip.consumed s.adapters pins) [(6, 1)]) :
    ∃ beforePins armPin suffix, pins = beforePins ++ armPin :: suffix ∧
      Admission cfg image memory actual s beforePins armPin suffix := by
  induction pins generalizing actual s
  case nil => cases delivered
  case cons pin rest ih =>
    rw [PairedHost.consumed_cons] at delivered
    cases delivered
    case quiet quiet tail =>
      obtain ⟨beforePins, armPin, suffix, split, admitted⟩ := ih
        ((PairedStreamPackage.interpreted memory).step pin actual) ((reference cfg).step pin s)
        (related_next cfg image memory actual s related pin
          (effective_rule cfg image s related.certified (quiet_rule cfg s quiet)))
        (quiet_ready_next cfg s ready quiet pin (released pin (List.mem_cons_self)))
        (fun i hi => released i (List.mem_cons_of_mem _ hi)) tail
      refine ⟨pin :: beforePins, armPin, suffix, by simp [split], ?_⟩
      refine ⟨?_, admitted.ready, admitted.before, admitted.command, admitted.after,
        admitted.receiver, admitted.enabled, admitted.active, admitted.operational,
        admitted.released, admitted.mailbox, admitted.quietSuffix⟩
      simpa only [PairedHost.consumed_cons, reference] using Machine.Delivers.quiet quiet admitted.quietPrefix
      done
    case command command tail =>
      have admitted := arm_next cfg image s related.certified ready command pin
        (released pin (List.mem_cons_self))
      exact ⟨[], pin, rest, rfl, ⟨.nil, ready, related, command,
        related_next cfg image memory actual s related pin
          (effective_rule cfg image s related.certified (arm_rule cfg s command)),
        admitted.1, admitted.2.1, admitted.2.2.1, admitted.2.2.2.1,
        ⟨released pin (List.mem_cons_self), ready.released.1⟩, admitted.2.2.2.2, tail⟩⟩
      done
    done
  done

private theorem bit_no_init (b : Bool) (samples : List Serial.Inputs)
    (bit : Serial.IsBit b samples) : ∀ i ∈ samples, i.init = false := by
  obtain ⟨lows, first, highs, rfl, _, _, low, high, _, highsHigh⟩ := bit.split
  grind [Serial.Low, Serial.High]

private theorem bits_no_init (segments : Nat → List Serial.Inputs) (n k : Nat)
    (qualified : ∀ j, k ≤ j → j < k + n → ∀ i ∈ segments j, i.init = false) :
    ∀ i ∈ Serial.bitsFrom segments k n, i.init = false := by
  induction n generalizing k
  case zero => simp [Serial.bitsFrom]
  case succ n ih =>
    simp only [Serial.bitsFrom, List.forall_mem_append]
    exact ⟨qualified k (Nat.le_refl _) (by omega),
      ih (k + 1) (fun j lo hi => qualified j (by omega) (by omega))⟩
    done
  done

private theorem frame_no_init (c : BitVec 8) (d : BitVec 64) (samples : List Serial.Inputs)
    (frame : Serial.IsFrame c d samples) : ∀ i ∈ samples, i.init = false := by
  obtain ⟨segments, rfl, bits⟩ := frame.split
  exact bits_no_init segments 72 0 (fun k _ hi => bit_no_init _ _ (bits k hi))
  done

private theorem session_no_init (samples : List Serial.Inputs)
    (commands : List (BitVec 3 × BitVec 64)) (session : Serial.Session samples commands) :
    ∀ i ∈ samples, i.init = false := by
  induction session
  case nil => simp
  case idle idle _ ih => simpa only [List.forall_mem_cons] using And.intro idle.1 ih
  case frame frame _ ih =>
    simpa only [List.forall_mem_append] using And.intro (frame_no_init _ _ _ frame) ih
  done

theorem session_released (pins : List Chip.Pins) (commands : List (BitVec 3 × BitVec 64))
    (session : Serial.Session (pins.map Chip.wired) commands) :
    ∀ pin ∈ pins, pin.rstN = true := by
  have all := session_no_init _ _ session
  exact fun pin hi => by
    simpa only [Chip.wired, Bool.not_eq_false'] using
      all (Chip.wired pin) (List.mem_map.mpr ⟨pin, hi, rfl⟩)
  done

theorem qualified_arm (cfg : Config) (image : PairedImage.Image)
    (memory : Memory.SinglePort.Contract S 9 64) (actual : PairedStreamPackage.State S)
    (s : ReferenceState) (related : Related cfg image memory actual s) (ready : Ready s)
    (count : s.adapters.receiver.count = 0) (fire : s.adapters.receiver.fire = false)
    (first : Serial.Idle s.adapters.first) (second : Serial.Idle s.adapters.second)
    (pins : List Chip.Pins) (a b : Chip.Pins) (ha : a.rstN = true) (hb : b.rstN = true)
    (session : Serial.Session (pins.map Chip.wired) [(6, 1)]) :
    ∃ beforePins armPin suffix, pins ++ [a, b] = beforePins ++ armPin :: suffix ∧
      Admission cfg image memory actual s beforePins armPin suffix := by
  apply delivered_arm cfg image memory actual s related ready (pins ++ [a, b])
  case released =>
    simpa only [List.forall_mem_append] using And.intro (session_released pins _ session)
      (show ∀ pin ∈ [a, b], pin.rstN = true by simp [ha, hb])
  case delivered => exact Chip.session_delivers s.adapters count fire first second pins a b _ session
  done

end Pinwheel.Hardware.Storage.PairedStreamArm
