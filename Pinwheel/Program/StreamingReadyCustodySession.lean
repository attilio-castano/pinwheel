import Pinwheel.Program.StreamingReadyCustodyBytes
import Pinwheel.Program.StreamingReadyReservation

namespace Pinwheel.Program.StreamingReady
open Pinwheel.Program.Streaming
set_option linter.unusedSimpArgs false

def Session.State.ReservationSafe (s : Session.State a) : Prop := s.host.phase = 2#3 → s.StageGrant

theorem Session.State.reservation_step (s : Session.State a) (p : Program) (pending : Bool)
    (i : Session.Pins) (ha : a ≤ 3) (runtime : Session.RuntimeInput s i)
    (frames : s.host.FrameSafe) (structural : s.core.Structural) (reservation : s.ReservationSafe) :
    (s.step p pending i).ReservationSafe := by
  intro phase
  rcases s.host.phase2_origin (s.hostInput pending i) phase with ⟨_, admitted⟩ | before
  · exact Session.State.StageGrant.admit s p pending i ha runtime.1 frames structural admitted
  · exact Session.State.StageGrant.stage s p pending i runtime.1 frames before (reservation before)

/-- A reached host/core session carries real custody and exact proof-only bit traces. -/
structure Session.State.Custody (s : Session.State a) (trace : BitTrace) : Prop where
  control : s.host.ControlSafe
  reservation : s.ReservationSafe
  interval : s.ExportInterval
  bytes : s.ExportBytes trace
  related : trace.Related s.core
  counts : trace.NaturalCounts s.core
  structural : s.core.Structural
  progress : s.core.Progress

theorem Session.State.Custody.step (s : Session.State a) (p : Program) (pending : Bool)
    (i : Session.Pins) (trace : BitTrace) (ha : a ≤ 3) (runtime : Session.RuntimeInput s i)
    (custody : s.Custody trace) :
    (s.step p pending i).Custody (trace.step s.core (s.command i).runtime) := by
  constructor
  · exact s.host.controlSafe_step (s.hostInput pending i) custody.control
  · exact s.reservation_step p pending i ha runtime custody.control.frames custody.structural custody.reservation
  · exact custody.interval.step s p pending i runtime custody.control.empty custody.reservation
      trace custody.counts custody.related custody.structural custody.progress
  · exact custody.bytes.step s p pending i trace runtime custody.interval custody.counts
      custody.control.empty custody.reservation
  · exact custody.related.step p s.core (s.command i).runtime trace custody.structural
  · exact custody.counts.step p s.core (s.command i).runtime trace custody.related custody.structural custody.progress
  · exact StreamingReady.step_structural p s.core (s.command i).runtime custody.structural
  · exact StreamingReady.step_progress p s.core (s.command i).runtime custody.progress

def Session.State.traceRun (s : Session.State a) (p : Program) (pending : Bool) (trace : BitTrace) :
    List Session.Pins → BitTrace
  | [] => trace
  | i :: inputs => (s.step p pending i).traceRun p pending (trace.step s.core (s.command i).runtime) inputs

theorem Session.State.traceRun_runtimeInputs (s : Session.State a) (p : Program) (pending : Bool)
    (trace : BitTrace) (pins : List Session.Pins) :
    s.traceRun p pending trace pins =
      StreamingReady.traceRun p s.core trace (s.runtimeInputs p pending pins) := by
  induction pins generalizing s trace with
  | nil => rfl
  | cons i rest ih => exact ih (s.step p pending i) (trace.step s.core (s.command i).runtime)

theorem Session.State.Custody.run (s : Session.State a) (p : Program) (pending : Bool)
    (samples : List Session.Pins) (trace : BitTrace) (ha : a ≤ 3)
    (runtime : Session.RuntimeTrace p pending s samples) (custody : s.Custody trace) :
    (s.run p pending samples).Custody (s.traceRun p pending trace samples) := by
  induction samples generalizing s trace with
  | nil => exact custody
  | cons i inputs induction =>
    exact induction (s.step p pending i) (trace.step s.core (s.command i).runtime)
      runtime.2 (custody.step s p pending i trace ha runtime.1)

theorem Session.State.Custody.started (s : Session.State a) (p : Program) (pending : Bool)
    (i : Session.Pins) (runtime : Session.RuntimeInput s i) (control : s.host.ControlSafe)
    (start : ((s.command i).runtime.command == 3 && s.core.canStart (s.command i).runtime) = true) :
    (s.step p pending i).Custody {} := by
  have clear := s.accepted_clears pending i (Or.inl start)
  have core := s.core_admitted_start p pending i runtime start
  have command := start
  simp only [Bool.and_eq_true, beq_iff_eq] at command
  obtain ⟨delivering, operation⟩ := s.host.command_operation (i.host {}) 3 (by decide) (by decide) command.1
  have phase : s.host.phase = 1#3 := by
    have facts := delivering
    simp only [Host.State.delivering, Bool.and_eq_true, beq_iff_eq] at facts
    exact facts.1.1
  have afterPhase : (s.step p pending i).host.phase = 3#3 := by
    have cold : (s.hostInput pending i).initialize = false := runtime.1
    have flags := s.host.work_no_frame (s.hostInput pending i) control.frames (by rw [phase]; decide)
    simp [Session.State.step, Host.step, cold, Host.State.closingRequest, flags.2.1, phase,
      Host.State.bulk, operation]
  constructor
  · exact s.host.controlSafe_step (s.hostInput pending i) control
  · intro phase2
    rw [afterPhase] at phase2
    contradiction
  · exact Session.State.ExportInterval.clear s p pending i runtime clear
  · have bytes := Session.State.ExportBytes.clear s p pending i {} runtime clear
    rw [s.trace_clear pending i {} runtime clear] at bytes
    exact bytes
  · rw [core]
    exact BitTrace.Related.start p s.core (s.command i).runtime
  · rw [core]
    exact BitTrace.NaturalCounts.start p s.core (s.command i).runtime
  · rw [core]
    exact s.core.start_structural p (s.command i).runtime
  · rw [core]
    exact s.core.start_progress p (s.command i).runtime

theorem Session.State.Custody.receipt_valid (s : Session.State a) (trace : BitTrace)
    (custody : s.Custody trace) :
    s.host.receipt.Valid s.core.rxProduced.toNat s.core.rxPopped.toNat :=
  custody.interval.receipt_valid s (custody.counts.order s.core trace custody.related).2

/-- A drained and acknowledged RX prefix is exact even if TX remains owned. -/
theorem Session.State.Custody.acknowledged_capture (s : Session.State a) (trace : BitTrace)
    (custody : s.Custody trace) (emptyQueue : s.core.rx.count.val = 0)
    (emptyPartial : s.core.rxUsed = 0#6) (acknowledged : s.host.exportBits.toNat = 0) :
    trace.captured = trace.exported ∧ s.host.ackOffset.toNat = trace.captured.length := by
  have chunks : trace.rxQueued = [] := by
    apply List.length_eq_zero_iff.mp
    simpa [emptyQueue] using custody.related.rxQueue.length
  have exported : trace.captured = trace.exported := by
    simpa [chunks,State.pendingRx,emptyPartial] using custody.related.rxOrder
  obtain ⟨acked,length,order⟩ := custody.bytes
  have empty : s.host.exportedBits = [] := by simp [Host.State.exportedBits,acknowledged]
  rw [empty,List.append_nil] at order
  exact ⟨exported,by rw [exported,order,length]⟩

/-- Retained transfers can drain RX without taking new samples. -/
theorem retained_trace (p : Program) (s : State a) (trace : BitTrace) (inputs : List Input)
    (retained : s.phase.retained = true)
    (ordinary : ∀ i ∈ inputs, i.Runtime ∧ i.command ≠ 4#4) :
    let final := run p s inputs
    final.phase = s.phase ∧ final.rxUsed = s.rxUsed ∧
      (traceRun p s trace inputs).captured = trace.captured := by
  induction inputs generalizing s trace with
  | nil => exact ⟨rfl,rfl,rfl⟩
  | cons i rest ih =>
    obtain ⟨⟨cold,warm⟩,release⟩ := ordinary i List.mem_cons_self
    have terminal : s.phase = .completed ∨ s.phase = .fault := by
      cases phase : s.phase <;> simp [Phase.retained,phase] at retained ⊢
    have notFree : s.phase ≠ .free := by
      rcases terminal with phase | phase <;> simp [phase]
    have next : step p i s = clock p i s := by
      simp [step,cold,(show i.command ≠ 15#4 from warm),release,State.canStart,notFree]
    have stable : engine p s = s := by
      rcases terminal with phase | phase <;> simp [engine,phase]
    have phaseStable : (step p i s).phase = s.phase := by simp [next,clock,stable]
    have usedStable : (step p i s).rxUsed = s.rxUsed := by simp [next,clock,stable]
    have noCapture : s.captures = false := by
      rcases terminal with phase | phase <;> simp [State.captures,phase]
    have captures : (trace.step s i).captured = trace.captured := by
      simp [BitTrace.step,cold,(show i.command ≠ 15#4 from warm),release,State.canStart,notFree,
        BitTrace.clock,State.rxEvent,noCapture]
    obtain ⟨last,used,bits⟩ := ih _ _ (by rw [phaseStable]; exact retained)
      (fun j member => ordinary j (List.mem_cons_of_mem _ member))
    exact ⟨last.trans phaseStable,used.trans usedStable,bits.trans captures⟩

theorem Session.State.Custody.release_all_bits (s : Session.State a) (i : Session.Pins)
    (trace : BitTrace) (custody : s.Custody trace)
    (command : (s.command i).runtime.command = 4#4) (accepted : s.core.canRelease (s.command i).runtime = true) :
    trace.accepted = trace.consumed ∧ trace.captured = trace.exported ∧
      trace.exported.length = s.host.ackOffset.toNat ∧ s.host.exportBits.toNat = 0 := by
  have drained : s.core.drained = true := by
    simp only [State.canRelease, Bool.and_eq_true] at accepted
    exact accepted.2
  have exactBits := custody.related.drained s.core trace drained
  have noReceipt := s.release_requires_ack i custody.control.release custody.interval command
  obtain ⟨acknowledged, length, order⟩ := custody.bytes
  have empty : s.host.exportedBits = [] := by simp [Host.State.exportedBits, noReceipt]
  rw [empty, List.append_nil] at order
  exact ⟨exactBits.1, exactBits.2, by rw [order]; exact length, noReceipt⟩

theorem Session.State.Custody.unacknowledged_blocks_release (s : Session.State a) (i : Session.Pins)
    (trace : BitTrace) (custody : s.Custody trace) (unacknowledged : 0 < s.host.exportBits.toNat) :
    (s.command i).runtime.command ≠ 4#4 := by
  intro command
  have empty := s.release_requires_ack i custody.control.release custody.interval command
  omega

end Pinwheel.Program.StreamingReady
