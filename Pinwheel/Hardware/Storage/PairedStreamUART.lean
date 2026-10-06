import Pinwheel.Hardware.Storage.PairedStreamLifecycle
import Pinwheel.Hardware.Storage.PairedStreamArm

/-! Public initialized UART endpoints. The resident image is installed by the
real serial loader, and the receiver starts only at its delivered ARM edge. -/
namespace Pinwheel.Hardware.Storage.PairedStreamUART
open Pinwheel.Hardware
open PairedStreamSession
open UART.Rx (Config)
set_option backward.isDefEq.respectTransparency false

theorem result_drained (memory : Memory.SinglePort.Contract S 9 64)
    (actual : PairedStreamPackage.State S) (pins : List Chip.Pins) (a b : Chip.Pins) :
    let after := (PairedStreamPackage.interpreted memory).run actual (pins ++ [a, b])
    after.result.resetFirst = b.rstN ∧ after.result.resetSecond = a.rstN := by
  induction pins generalizing actual
  case nil => exact ⟨rfl, rfl⟩
  case cons pin rest ih => exact ih ((PairedStreamPackage.interpreted memory).step pin actual)
  done

theorem restart_released (r : PairedStreamLifecycle.Restart cfg image)
    (memory : Memory.SinglePort.Contract S 9 64) (initial : PairedStreamPackage.State S)
    (epoch : Nat) (first : r.drainFirst.rstN = true) (second : r.drainSecond.rstN = true) :
    (r.reference memory initial epoch).result.resetFirst = true ∧
      (r.reference memory initial epoch).result.resetSecond = true := by
  have h := result_drained memory (r.prepared memory initial) r.upload r.drainFirst r.drainSecond
  simpa only [PairedStreamLifecycle.Restart.reference, PairedStreamLifecycle.rebase,
    PairedStreamLifecycle.Restart.after, initialReference, first, second] using h
  done

theorem restart_ready (r : PairedStreamLifecycle.Restart cfg image)
    (memory : Memory.SinglePort.Contract S 9 64) (initial : PairedStreamPackage.State S)
    (epoch : Nat) (first : r.drainFirst.rstN = true) (second : r.drainSecond.rstN = true) :
    PairedStreamArm.Ready (r.reference memory initial epoch) := by
  have initialized := r.initialized memory initial epoch
  exact ⟨initialized.1, initialized.2.1, initialized.2.2.1,
    restart_released r memory initial epoch first second⟩
  done

/-- A real upload followed by a real delivered ARM locates the admitted
receiver edge. Trailing drain samples remain in the suffix and advance it. -/
theorem initialized_delivered_arm (r : PairedStreamLifecycle.Restart cfg image)
    (memory : Memory.SinglePort.Contract S 9 64) (initial : PairedStreamPackage.State S)
    (epoch : Nat) (first : r.drainFirst.rstN = true) (second : r.drainSecond.rstN = true)
    (pins : List Chip.Pins) (released : ∀ pin ∈ pins, pin.rstN = true)
    (delivered : Loader.Machine.Delivers (Chip.consumed (r.reference memory initial epoch).adapters pins)
      [(6, 1)]) :
    ∃ beforePins armPin suffix, pins = beforePins ++ armPin :: suffix ∧
      PairedStreamArm.Admission cfg image memory (r.after memory initial)
        (r.reference memory initial epoch) beforePins armPin suffix := by
  exact PairedStreamArm.delivered_arm cfg image memory _ _ (r.correct memory initial epoch)
    (restart_ready r memory initial epoch first second) pins released delivered
  done

def cutActual (memory : Memory.SinglePort.Contract S 9 64) (actual : PairedStreamPackage.State S)
    (beforePins : List Chip.Pins) (armPin : Chip.Pins) : PairedStreamPackage.State S :=
  (PairedStreamPackage.interpreted memory).step armPin
    ((PairedStreamPackage.interpreted memory).run actual beforePins)

def cutReference (cfg : Config) (s : ReferenceState) (beforePins : List Chip.Pins)
    (armPin : Chip.Pins) : ReferenceState :=
  (reference cfg).step armPin ((reference cfg).run s beforePins)

/-- The first post-ARM edge retains its actual consumer/clear receipt. It does
not invent a UART arrival or discard an unread packet from an earlier epoch. -/
theorem admitted_first_receipt (cfg : Config) (image : PairedImage.Image)
    (memory : Memory.SinglePort.Contract S 9 64) (actual : PairedStreamPackage.State S)
    (s : ReferenceState) (beforePins : List Chip.Pins) (armPin : Chip.Pins) (suffix : List Chip.Pins)
    (admitted : PairedStreamArm.Admission cfg image memory actual s beforePins armPin suffix)
    (pins : Chip.Pins) (released : pins.rstN = true) :
    let current := cutReference cfg s beforePins armPin
    HostResultBuffer.receipt pins
      (PairedStreamPackage.coreOutput memory (cutActual memory actual beforePins armPin))
      (cutActual memory actual beforePins armPin).result =
        eraseReceipt (HostResultBuffer.Retained.step current.mailbox
          (.cycle none (HostResult.consuming current.result)
            (HostResult.clearing current.result))).receipt := by
  dsimp only
  unfold cutActual cutReference
  rw [receipt_agrees cfg image memory _ _ admitted.after]
  simp only [ownedReceipt, mailboxCommand, HostResult.resetting,
    released, admitted.released.1, admitted.released.2, Bool.true_and,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, ownedArrival, receiverArrival,
    admitted.receiver, UART.Rx.initial, ite_self, Option.map_none]
  done

/-- Receiver start, reset phase and continuing activation all follow from the
delivered ARM cut and the certified policy. The remaining premises describe
allowed host controls and the sampled external UART waveform. -/
theorem admitted_wire_receive_series (t : UART.Link.Timing) (image : PairedImage.Image)
    (memory : Memory.SinglePort.Contract S 9 64) (actual : PairedStreamPackage.State S)
    (s : ReferenceState) (beforePins : List Chip.Pins) (armPin : Chip.Pins) (suffix : List Chip.Pins)
    (admitted : PairedStreamArm.Admission t.rx image memory actual s beforePins armPin suffix)
    (incoming : Nat → Chip.Pins) (released : ∀ n, (incoming n).rstN = true)
    (quiet : QuietHistory t.rx (cutReference t.rx s beforePins armPin) incoming)
    (latency : UART.Link.Latency) (bytes : List (BitVec 8)) (age : Nat → Nat)
    (safe : UART.StreamLink.Safe t latency) (within : latency.Contains age)
    (samples : Samples t.rx (cutReference t.rx s beforePins armPin) incoming
      (UART.StreamLink.sampled t bytes age)) :
    ∃ frames, frames.map UART.Rx.Stream.FrameSpec.byte = bytes ∧
      UART.StreamLink.Windows t latency frames ∧
      ∀ n, n ≤ UART.Rx.Stream.horizon t.rx frames →
        (HostResultBuffer.arrival
          (PairedStreamPackage.coreOutput memory
            (actualRunN memory (cutActual memory actual beforePins armPin) incoming n))
          (actualRunN memory (cutActual memory actual beforePins armPin) incoming n).result).map
          HostResultBuffer.uartOutcome = UART.Rx.Stream.expected t.rx frames n := by
  exact quiet_wire_receive_series t image memory _ _ admitted.after admitted.operational
    admitted.enabled admitted.receiver admitted.active admitted.released incoming released quiet
      latency bytes age safe within samples
  done

theorem restart_settled (r : PairedStreamLifecycle.Restart cfg image)
    (memory : Memory.SinglePort.Contract S 9 64) (initial : PairedStreamPackage.State S)
    (epoch : Nat) (firstIdle : Serial.Idle (Chip.wired r.drainFirst))
    (secondIdle : Serial.Idle (Chip.wired r.drainSecond)) :
    let s := r.reference memory initial epoch
    s.adapters.receiver.count = 0 ∧ s.adapters.receiver.fire = false ∧
      Serial.Idle s.adapters.first ∧ Serial.Idle s.adapters.second := by
  obtain ⟨storage, physical, stopped, disabled, count, fire, first, second⟩ :=
    PairedStreamBootstrap.reset_prepares memory initial r.reset r.idle
      r.resetLow r.idleReleased r.idleSerial
  have settled := PairedStreamBootstrap.settled_session memory (r.prepared memory initial)
    count fire first second r.upload r.drainFirst r.drainSecond firstIdle secondIdle
      (Loader.Machine.uploadCommands (PairedImage.upload image) r.beginData r.commitData) r.delivery
  simpa only [PairedStreamLifecycle.Restart.reference, PairedStreamLifecycle.rebase,
    initialReference, PairedStreamLifecycle.Restart.after] using settled
  done

/-- Both upload and ARM are qualified physical serial transcripts. Admission
is derived at the actual delivered edge, including observer reset phase. -/
theorem initialized_qualified_arm (r : PairedStreamLifecycle.Restart cfg image)
    (memory : Memory.SinglePort.Contract S 9 64) (initial : PairedStreamPackage.State S)
    (epoch : Nat) (firstIdle : Serial.Idle (Chip.wired r.drainFirst))
    (secondIdle : Serial.Idle (Chip.wired r.drainSecond))
    (pins : List Chip.Pins) (a b : Chip.Pins) (ha : a.rstN = true) (hb : b.rstN = true)
    (session : Serial.Session (pins.map Chip.wired) [(6, 1)]) :
    ∃ beforePins armPin suffix, pins ++ [a, b] = beforePins ++ armPin :: suffix ∧
      PairedStreamArm.Admission cfg image memory (r.after memory initial)
        (r.reference memory initial epoch) beforePins armPin suffix := by
  have settled := restart_settled r memory initial epoch firstIdle secondIdle
  exact PairedStreamArm.qualified_arm cfg image memory _ _ (r.correct memory initial epoch)
    (restart_ready r memory initial epoch (idle_released _ firstIdle) (idle_released _ secondIdle))
    settled.1 settled.2.1 settled.2.2.1 settled.2.2.2 pins a b ha hb session
  done

def Reception (t : UART.Link.Timing) (memory : Memory.SinglePort.Contract S 9 64)
    (actual : PairedStreamPackage.State S) (incoming : Nat → Chip.Pins)
    (latency : UART.Link.Latency) (bytes : List (BitVec 8)) : Prop :=
  ∃ frames, frames.map UART.Rx.Stream.FrameSpec.byte = bytes ∧
    UART.StreamLink.Windows t latency frames ∧
    ∀ n, n ≤ UART.Rx.Stream.horizon t.rx frames →
      (HostResultBuffer.arrival
        (PairedStreamPackage.coreOutput memory (actualRunN memory actual incoming n))
        (actualRunN memory actual incoming n).result).map HostResultBuffer.uartOutcome =
          UART.Rx.Stream.expected t.rx frames n

/-- Arbitrary power-up, actual reset/release, qualified canonical-image upload,
and qualified delivered ARM establish the certified timing cut.
There are no recurring core-correspondence, memory-Q or activation premises.
The timing conclusion applies to any allowed consumer/clear history. -/
theorem initialized_wire_session (t : UART.Link.Timing) (image : PairedImage.Image)
    (r : PairedStreamLifecycle.Restart t.rx image)
    (memory : Memory.SinglePort.Contract S 9 64) (initial : PairedStreamPackage.State S)
    (epoch : Nat) (firstIdle : Serial.Idle (Chip.wired r.drainFirst))
    (secondIdle : Serial.Idle (Chip.wired r.drainSecond))
    (pins : List Chip.Pins) (a b : Chip.Pins) (ha : a.rstN = true) (hb : b.rstN = true)
    (session : Serial.Session (pins.map Chip.wired) [(6, 1)]) :
    ∃ beforePins armPin suffix, pins ++ [a, b] = beforePins ++ armPin :: suffix ∧
      PairedStreamArm.Admission t.rx image memory (r.after memory initial)
        (r.reference memory initial epoch) beforePins armPin suffix ∧
      ∀ incoming : Nat → Chip.Pins, (∀ n, (incoming n).rstN = true) →
        QuietHistory t.rx (cutReference t.rx (r.reference memory initial epoch) beforePins armPin) incoming →
        ∀ (latency : UART.Link.Latency) (bytes : List (BitVec 8)) (age : Nat → Nat),
          UART.StreamLink.Safe t latency → latency.Contains age →
          Samples t.rx (cutReference t.rx (r.reference memory initial epoch) beforePins armPin)
            incoming (UART.StreamLink.sampled t bytes age) →
          Reception t memory (cutActual memory (r.after memory initial) beforePins armPin)
            incoming latency bytes := by
  obtain ⟨beforePins, armPin, suffix, split, admitted⟩ :=
    initialized_qualified_arm r memory initial epoch firstIdle secondIdle pins a b ha hb session
  refine ⟨beforePins, armPin, suffix, split, admitted, ?_⟩
  intro incoming released quiet latency bytes age safe within samples
  exact admitted_wire_receive_series t image memory _ _ beforePins armPin suffix admitted
    incoming released quiet latency bytes age safe within samples
  done

/-- Destination-edge history containing every known trailing ARM sample,
followed by future pin edges. Edge zero is not consumed by runN. -/
def extend (suffix : List Chip.Pins) (future : Nat → Chip.Pins) (n : Nat) : Chip.Pins :=
  if h : 0 < n ∧ n ≤ suffix.length then suffix[n - 1] else future (n - suffix.length)

theorem extend_suffix (suffix : List Chip.Pins) (future : Nat → Chip.Pins) (k : Fin suffix.length) :
    extend suffix future (k.val + 1) = suffix[k.val] := by
  simp [extend, show 0 < k.val + 1 ∧ k.val + 1 ≤ suffix.length by omega]
  done

/-- One initialized continuous session includes the original trailing ARM
samples literally, followed by future physical pin edges. Continuing rearm,
the certified resident fetch, and the observer phase are derived invariants;
only host-control and digital wire timing conditions remain as premises. -/
theorem initialized_continuous_uart (t : UART.Link.Timing) (image : PairedImage.Image)
    (r : PairedStreamLifecycle.Restart t.rx image)
    (memory : Memory.SinglePort.Contract S 9 64) (initial : PairedStreamPackage.State S)
    (epoch : Nat) (firstIdle : Serial.Idle (Chip.wired r.drainFirst))
    (secondIdle : Serial.Idle (Chip.wired r.drainSecond))
    (pins : List Chip.Pins) (a b : Chip.Pins) (ha : a.rstN = true) (hb : b.rstN = true)
    (session : Serial.Session (pins.map Chip.wired) [(6, 1)]) :
    ∃ beforePins armPin suffix, pins ++ [a, b] = beforePins ++ armPin :: suffix ∧
      PairedStreamArm.Admission t.rx image memory (r.after memory initial)
        (r.reference memory initial epoch) beforePins armPin suffix ∧
      ∀ future : Nat → Chip.Pins, (∀ n, (extend suffix future n).rstN = true) →
        QuietHistory t.rx (cutReference t.rx (r.reference memory initial epoch) beforePins armPin)
          (extend suffix future) →
        ∀ (latency : UART.Link.Latency) (bytes : List (BitVec 8)) (age : Nat → Nat),
          UART.StreamLink.Safe t latency → latency.Contains age →
          Samples t.rx (cutReference t.rx (r.reference memory initial epoch) beforePins armPin)
            (extend suffix future) (UART.StreamLink.sampled t bytes age) →
          Reception t memory (cutActual memory (r.after memory initial) beforePins armPin)
            (extend suffix future) latency bytes := by
  obtain ⟨beforePins, armPin, suffix, split, admitted, timing⟩ :=
    initialized_wire_session t image r memory initial epoch firstIdle secondIdle pins a b ha hb session
  exact ⟨beforePins, armPin, suffix, split, admitted,
    fun future => timing (extend suffix future)⟩
  done

end Pinwheel.Hardware.Storage.PairedStreamUART
