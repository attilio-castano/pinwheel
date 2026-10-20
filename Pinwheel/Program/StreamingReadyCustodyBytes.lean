import Pinwheel.Program.StreamingReadyCustodyInvariant
import Pinwheel.Program.StreamingCustodyBytes

namespace Pinwheel.Program.StreamingReady
open Pinwheel.Program.Streaming
set_option linter.unusedSimpArgs false

/-- Exact bytes in frontend custody are the unacknowledged suffix of actual popped bits. -/
def Session.State.ExportBytes (s : Session.State a) (trace : BitTrace) : Prop :=
  ∃ acknowledged : List Bool, acknowledged.length = s.host.ackOffset.toNat ∧
    trace.exported = acknowledged ++ s.host.exportedBits

theorem Session.State.trace_no_clear (s : Session.State a) (pending : Bool) (i : Session.Pins)
    (trace : BitTrace) (runtime : Session.RuntimeInput s i)
    (clearing : s.host.clearingExport (s.hostInput pending i).status = false) :
    trace.step s.core (s.command i).runtime = trace.clock s.core (s.command i).runtime := by
  have noStart : ((s.command i).runtime.command == 3 && s.core.canStart (s.command i).runtime) = false := by
    apply Bool.eq_false_iff.mpr
    intro admitted
    have clear := s.accepted_clears pending i (Or.inl admitted)
    simp [clearing] at clear
  have noRelease : ((s.command i).runtime.command == 4 && s.core.canRelease (s.command i).runtime) = false := by
    apply Bool.eq_false_iff.mpr
    intro admitted
    have clear := s.accepted_clears pending i (Or.inr admitted)
    simp [clearing] at clear
  have warm : (s.command i).runtime.command ≠ 15#4 := runtime.2.1
  simp only [BitTrace.step, noStart, noRelease]
  simp [runtime.1, warm]

theorem Session.State.trace_clear (s : Session.State a) (pending : Bool) (i : Session.Pins)
    (trace : BitTrace) (runtime : Session.RuntimeInput s i)
    (clearing : s.host.clearingExport (s.hostInput pending i).status = true) :
    trace.step s.core (s.command i).runtime = {} := by
  rcases s.clearing_accepted pending i runtime clearing with start | release
  · simp only [BitTrace.step, runtime.1, start, Bool.false_eq_true, ↓reduceIte]
    split <;> rfl
  · simp only [Bool.and_eq_true, beq_iff_eq] at release
    simp [BitTrace.step, runtime.1, release.1, release.2]

theorem Session.State.ExportBytes.clear (s : Session.State a) (p : Program) (pending : Bool)
    (i : Session.Pins) (trace : BitTrace) (runtime : Session.RuntimeInput s i)
    (clearing : s.host.clearingExport (s.hostInput pending i).status = true) :
    (s.step p pending i).ExportBytes (trace.step s.core (s.command i).runtime) := by
  rw [s.trace_clear pending i trace runtime clearing]
  have cold : (s.hostInput pending i).initialize = false := runtime.1
  refine ⟨[], ?_, ?_⟩
  all_goals simp [Session.State.step, Host.step, cold, clearing, Host.State.exportedBits]

theorem Session.State.ExportBytes.hold (s : Session.State a) (p : Program) (pending : Bool)
    (i : Session.Pins) (trace : BitTrace) (runtime : Session.RuntimeInput s i)
    (bytes : s.ExportBytes trace)
    (clearing : s.host.clearingExport (s.hostInput pending i).status = false)
    (admitting : s.host.admittingBulk (s.hostInput pending i).status = false)
    (capturing : s.host.stagedRX = false) :
    (s.step p pending i).ExportBytes (trace.step s.core (s.command i).runtime) := by
  rw [s.trace_no_clear pending i trace runtime clearing]
  obtain ⟨acknowledged, length, order⟩ := bytes
  have cold : (s.hostInput pending i).initialize = false := runtime.1
  have pop : (s.command i).runtime.rxPop = false := capturing
  refine ⟨acknowledged, ?_, ?_⟩
  · simpa [Session.State.step, Host.step, cold, clearing, admitting] using length
  · simpa [Session.State.step, Host.step, cold, clearing, admitting, capturing,
      BitTrace.clock, State.exportedBits, State.hostPop, pop, Queue.willPop, Host.State.exportedBits] using order

theorem Session.State.ExportBytes.admit (s : Session.State a) (p : Program) (pending : Bool)
    (i : Session.Pins) (trace : BitTrace) (runtime : Session.RuntimeInput s i)
    (interval : s.ExportInterval) (counts : trace.NaturalCounts s.core)
    (admitted : s.host.admittingBulk (s.hostInput pending i).status = true) :
    (s.step p pending i).ExportBytes (trace.step s.core (s.command i).runtime) := by
  have bulk : s.host.bulk = true := by
    have facts := admitted
    simp only [Host.State.admittingBulk, Bool.and_eq_true] at facts
    exact facts.1.2
  have noClear : s.host.clearingExport (s.hostInput pending i).status = false := by
    simp [Host.State.clearingExport, Host.State.delivering, bulk]
  rw [s.trace_no_clear pending i trace runtime noClear]
  have fields := s.host.admit_export_fields (s.hostInput pending i) runtime.1 admitted
  have nextInterval := interval.admit s p pending i runtime.1 admitted
  have ack : (s.step p pending i).host.ackOffset = s.core.rxPopped :=
    nextInterval.ack.trans fields.2.1
  have pop : (s.command i).runtime.rxPop = false := (s.admission_command pending i admitted).2
  refine ⟨trace.exported, ?_, ?_⟩
  · rw [ack]
    exact counts.exported
  · change (trace.clock s.core (s.command i).runtime).exported =
      trace.exported ++ Packing.rxBits ((Host.step (s.hostInput pending i) s.host).exportData.setWidth 32)
        (Host.step (s.hostInput pending i) s.host).exportBits.toNat
    rw [fields.2.2.1]
    simp [BitTrace.clock, State.exportedBits, State.hostPop, pop, Queue.willPop]

theorem Session.State.ExportBytes.capture (s : Session.State a) (p : Program) (pending : Bool)
    (i : Session.Pins) (trace : BitTrace) (runtime : Session.RuntimeInput s i)
    (bytes : s.ExportBytes trace) (empty : s.host.StageEmpty) (phase : s.host.phase = 2#3)
    (receiving : s.host.rxPending = true) (grant : s.StageGrant) :
    (s.step p pending i).ExportBytes (trace.step s.core (s.command i).runtime) := by
  have noClear : s.host.clearingExport (s.hostInput pending i).status = false := by
    simp [Host.State.clearingExport, Host.State.delivering, phase]
  rw [s.trace_no_clear pending i trace runtime noClear]
  obtain ⟨acknowledged, length, order⟩ := bytes
  have oldBits : s.host.exportedBits = [] := by
    simp [Host.State.exportedBits, empty phase receiving]
  rw [oldBits, List.append_nil] at order
  have fields := s.host.capture_export_fields (s.hostInput pending i) runtime.1 phase receiving
  have newBits : (s.step p pending i).host.exportedBits = s.core.rx.peek.rxBits := by
    change Packing.rxBits ((Host.step (s.hostInput pending i) s.host).exportData.setWidth 32)
      (Host.step (s.hostInput pending i) s.host).exportBits.toNat = _
    rw [fields.1, fields.2.2.1]
    have bound := s.core.rx.peek.validBits_le
    simp [Session.State.hostInput, Session.Pins.host,Streaming.Session.Pins.host, State.status, grant.receive receiving,
      Chunk.rxBits, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show s.core.rx.peek.validBits < 64 by omega),
      Nat.mod_eq_of_lt (show s.core.rx.peek.validBits < 128 by omega)]
  refine ⟨acknowledged, ?_, ?_⟩
  · change acknowledged.length = (Host.step (s.hostInput pending i) s.host).ackOffset.toNat
    rw [fields.2.2.2]
    exact length
  · rw [newBits]
    simp [BitTrace.clock, State.exportedBits, s.stage_pop i phase grant receiving, order]

theorem Session.State.ExportBytes.step (s : Session.State a) (p : Program) (pending : Bool)
    (i : Session.Pins) (trace : BitTrace) (runtime : Session.RuntimeInput s i)
    (bytes : s.ExportBytes trace) (interval : s.ExportInterval) (counts : trace.NaturalCounts s.core)
    (empty : s.host.StageEmpty) (reservation : s.host.phase = 2#3 → s.StageGrant) :
    (s.step p pending i).ExportBytes (trace.step s.core (s.command i).runtime) := by
  by_cases clearing : s.host.clearingExport (s.hostInput pending i).status = true
  · exact Session.State.ExportBytes.clear s p pending i trace runtime clearing
  · have noClear := Bool.eq_false_iff.mpr clearing
    by_cases admitting : s.host.admittingBulk (s.hostInput pending i).status = true
    · exact Session.State.ExportBytes.admit s p pending i trace runtime interval counts admitting
    · have noAdmit := Bool.eq_false_iff.mpr admitting
      by_cases capturing : s.host.stagedRX = true
      · have capture := capturing
        simp only [Host.State.stagedRX, Bool.and_eq_true, beq_iff_eq] at capture
        exact bytes.capture s p pending i trace runtime empty capture.1 capture.2 (reservation capture.1)
      · exact bytes.hold s p pending i trace runtime noClear noAdmit (Bool.eq_false_iff.mpr capturing)

end Pinwheel.Program.StreamingReady
