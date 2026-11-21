import Pinwheel.Hardware.StreamingReady.SegmentTrace
import Pinwheel.Hardware.StreamingReady.SegmentTransactionTimeout

/-! A checked flat trace through the first dynamically expired poll. The
    contract checks the reached pre-edge sampler and deadline. Protocol-specific
    claims about which path should be taken use a separate source contract. -/
namespace Pinwheel.Hardware.StreamingReady.SegmentTraceTimeout

open Pinwheel.Hardware SegmentCore SegmentPathControl SegmentTransaction
open SegmentTiming (run)

/-- The final poll uses the pre-edge sampler, so ready at this aperture
    succeeds even when the countdown has reached zero. -/
def deadline (i : Values Core.Input) (s : Values (Register a)) : Bool :=
  i .initialize == 0#1 && i .command == 0#4 && i .txPush == 0#1 &&
    s (.base .phase) == 7#3 && Core.waitReady.eval i (project s) == 0#1 &&
    Core.guardBudget.eval i (project s) != 0#8 && s (.base .countdown) == 0#8

def accepts (registered : Bool) (started : Values (Register a)) (clocks : List (Values Core.Input))
    (last : Values Core.Input) : Bool :=
  SegmentTrace.active registered started clocks && deadline last (run registered started clocks)

private theorem accepts_parts {started : Values (Register a)} {last : Values Core.Input}
    (accepted : accepts registered started clocks last = true) :
    SegmentTrace.active registered started clocks = true ∧ deadline last (run registered started clocks) = true := by
  simpa only [accepts, Bool.and_eq_true] using accepted

theorem accepts_sound {started : Values (Register a)} {last : Values Core.Input}
    (accepted : accepts registered started clocks last = true) :
    ActiveClocks registered started clocks ∧ ProtocolOwnership.AtDeadline last (run registered started clocks) := by
  obtain ⟨active, expiry⟩ := accepts_parts accepted
  simp only [deadline, Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at expiry
  obtain ⟨⟨⟨⟨⟨⟨init, command⟩, noPush⟩, phase⟩, miss⟩, bounded⟩, elapsed⟩ := expiry
  exact ⟨SegmentTrace.active_clocks active, ⟨⟨init, command, noPush⟩, phase, miss, bounded, elapsed⟩⟩

/-- An installed image and an admitted START run through every checked clock.
    The failed last poll restores the installed idle pose, matches the observed
    prefix lengths in the 16-bit counters, and retains the owner created at START. -/
theorem from_start (registered : Bool) (s : Values (Register a)) (start last : Values Core.Input)
    (installed : Installed rows s) (admitted : Core.starting.eval start (project s) = 1#1)
    (accepted : accepts registered ((circuit a registered).step start s) clocks last = true) :
    let started : Values (Register a) := (circuit a registered).step start s
    let aperture : Values (Register a) := run registered started clocks
    let fault : Values (Register a) := (circuit a registered).step last aperture
    let bits := SegmentTrace.observe registered started clocks
    SegmentTiming.TimeoutCut aperture fault ∧ fault (.base .phase) = 6#3 ∧
      fault (.base .levels) = s (.base .idleLevels) ∧ fault (.base .enabled) = s (.base .idleEnabled) ∧
      fault (.base .txConsumed) = BitVec.ofNat 16 bits.tx.length ∧
      fault (.base .rxProduced) = BitVec.ofNat 16 bits.rx.length ∧
      fault (.base .generation) = s (.base .generation) ∧
      fault (.base .transfer) = s (.base .transfer) + 1 ∧ fault (.base .total) = start .startCount := by
  obtain ⟨active, finalPoll⟩ := accepts_sound accepted
  have reached := SegmentTiming.timeout_edge registered last _ finalPoll
  have idle := SegmentTransactionTimeout.idle_from_start registered s start admitted active
  obtain ⟨tx, rx, generation, transfer, total⟩ :=
    SegmentTrace.from_start registered s start installed admitted (accepts_parts accepted).1
  have lastOwner := active_owner_frame registered last (run registered ((circuit a registered).step start s) clocks)
    ⟨finalPoll.ordinary.1, by simp [finalPoll.ordinary.2.1]⟩
    (by simp [finalPoll.waiting]) (by simp [finalPoll.waiting]) (by simp [finalPoll.waiting])
  exact ⟨reached, congrArg ProtocolOwnership.TerminalCut.phase reached.retained,
    reached.levels.trans idle.1, reached.enabled.trans idle.2,
    (congrArg ProtocolOwnership.TerminalCut.reserved reached.retained).trans tx,
    (congrArg ProtocolOwnership.TerminalCut.captured reached.retained).trans rx,
    lastOwner.generation.trans generation, lastOwner.transfer.trans transfer, lastOwner.total.trans total⟩

/-- At the acknowledged receive cut, expiry still owns accepted but unsent TX.
    The acknowledged end is the length of the entire observed receive prefix,
    provided that count fits the hardware's 16-bit register. -/
theorem after_drain (registered : Bool) (s : Values (Register a)) (start last : Values Core.Input)
    (installed : Installed rows s) (admitted : Core.starting.eval start (project s) = 1#1)
    (accepted : accepts registered ((circuit a registered).step start s) clocks last = true)
    (drain : List (Values Core.Input)) (ordinary : ∀ i ∈ drain, ProtocolOwnership.DrainInput i)
    (front : Values Streaming.Frontend.Register) :
    let started : Values (Register a) := (circuit a registered).step start s
    let aperture : Values (Register a) := run registered started clocks
    let prefixBits := SegmentTrace.observe registered started clocks
    let fault : Values (Register a) := (circuit a registered).step last aperture
    let drained : Values (Register a) := run registered fault drain
    let owned := (aperture (.base .txAccepted)).toNat - (aperture (.base .txConsumed)).toNat
    (aperture (.base .txConsumed)).toNat ≤ (aperture (.base .txAccepted)).toNat →
    prefixBits.rx.length < 65536 → ProtocolOwnership.AcknowledgedReceive drained front →
      (ProtocolOwnership.segmentedReport .timeout .retained 0 owned drained drained front).Valid ∧
      drained (.base .phase) = 6#3 ∧ (front .ackOffset).toNat = prefixBits.rx.length ∧
      ∀ cancel : Values Core.Input, cancel .initialize = 0#1 → cancel .command = 15#4 →
        let after : Values (Register a) := (circuit a registered).step cancel drained
        (ProtocolOwnership.segmentedReport .timeout .cancelled 0 owned drained after front).Valid ∧
          after (.base .phase) = 0#3 ∧ after (.base .valid) = 0#1 := by
  intro started aperture prefixBits fault drained owned ordered fits acknowledged
  have sampled := (SegmentTrace.from_start registered s start installed admitted (accepts_parts accepted).1).2.1
  obtain ⟨retained, phase, preserved, _, _, cancelled⟩ := ProtocolOwnership.timeout_after_drain
    registered last aperture (accepts_sound accepted).2 ordered drain ordinary front acknowledged
  have exported : (front .ackOffset).toNat = prefixBits.rx.length := by
    have captured : aperture (.base .rxProduced) = BitVec.ofNat 16 prefixBits.rx.length := sampled
    have kept : drained (.base .rxProduced) = aperture (.base .rxProduced) := preserved
    rw [← acknowledged.exact, kept, captured]
    exact Nat.mod_eq_of_lt fits
  exact ⟨retained, phase, exported, cancelled⟩

end Pinwheel.Hardware.StreamingReady.SegmentTraceTimeout
