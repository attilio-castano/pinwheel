import Pinwheel.Program.StreamingCustody
import Pinwheel.Program.StreamingTiming

namespace Pinwheel.Program.Streaming

theorem Host.State.phase2_origin (s : Host.State) (i : Host.Input)
    (phase : (Host.step i s).phase = 2#3) :
    (s.phase = 1#3 ∧ s.admittingBulk i.status = true) ∨ s.phase = 2#3 := by
  by_cases cold : i.initialize = true
  · simp [Host.step, cold] at phase
  · simp only [Host.step, cold, Bool.false_eq_true, ↓reduceIte] at phase
    split at phase
    · split at phase <;> (try split at phase) <;> simp_all
    · split at phase
      · left
        have before : s.phase = 1#3 := by simpa using (show (s.phase == 1) = true by assumption)
        by_cases bulk : s.bulk = true <;> by_cases admit : s.bulkAdmitted i.status = true <;>
          simp_all [Host.State.admittingBulk]
      · split at phase
        · right; simpa using (show (s.phase == 2) = true by assumption)
        · split at phase
          · contradiction
          · split at phase
            · contradiction
            · right; exact phase

def Host.State.StageEmpty (s : Host.State) : Prop :=
  s.phase = 2#3 → s.rxPending = true → s.exportBits = 0#7

theorem Host.State.stageEmpty_step (s : Host.State) (i : Host.Input) : (Host.step i s).StageEmpty := by
  intro phase pending
  rcases s.phase2_origin i phase with ⟨before, admitted⟩ | before
  · by_cases cold : i.initialize = true
    · simp [Host.step, cold]
    · simp only [Host.step, cold, Bool.false_eq_true, ↓reduceIte, admitted]
      split <;> rfl
  · by_cases cold : i.initialize = true
    · simp [Host.step, cold] at pending
    · cases rx : s.rxPending <;>
        simp [Host.step, cold, Host.State.admittingBulk, Host.State.stagedRX, before, rx] at pending

theorem Host.State.phase1_origin (s : Host.State) (i : Host.Input)
    (phase : (Host.step i s).phase = 1#3) :
    i.initialize = false ∧ s.closingRequest i = true ∧ s.closingCode = 0#4 := by
  by_cases cold : i.initialize = true
  · simp [Host.step, cold] at phase
  · have ordinary : i.initialize = false := Bool.eq_false_iff.mpr cold
    simp only [Host.step, ordinary, Bool.false_eq_true, ↓reduceIte] at phase
    split at phase
    · split at phase
      · contradiction
      · split at phase
        · exact ⟨ordinary, by assumption, by simpa using (show (s.closingCode == 0) = true by assumption)⟩
        · contradiction
    · split at phase
      · split at phase <;> (try split at phase) <;> contradiction
      · split at phase
        · split at phase <;> contradiction
        · split at phase
          · contradiction
          · split at phase
            · contradiction
            · have previous : s.phase ≠ 1#3 := by simpa using (show ¬(s.phase == 1) = true by assumption)
              exact False.elim (previous phase)

theorem Host.State.closing_custody_fields (s : Host.State) (i : Host.Input) (safe : s.FrameSafe)
    (closing : s.closingRequest i = true) (cold : i.initialize = false) :
    (Host.step i s).request = s.request ∧
    (Host.step i s).exportData = s.exportData ∧
    (Host.step i s).exportStart = s.exportStart ∧
    (Host.step i s).exportBits = s.exportBits ∧
    (Host.step i s).ackOffset = s.ackOffset := by
  have facts := closing
  simp only [Host.State.closingRequest, Host.State.closing, Bool.and_eq_true,
    Bool.not_eq_true'] at facts
  have idle := safe facts.1.1.1
  simp [Host.step, cold, Host.State.startingFrame, Host.State.receiving,
    Host.State.taking, Host.State.clearingExport, Host.State.delivering,
    Host.State.admittingBulk, Host.State.stagedRX, idle, facts.1.1.1, facts.1.2]

theorem Host.State.release_code (s : Host.State) (code : s.closingCode = 0#4)
    (operation : s.opcode = 4#4) : s.unacknowledged = false := by
  by_cases unack : s.unacknowledged = true
  · simp [Host.State.closingCode, operation, unack] at code
    repeat' (first | contradiction | split at code)
  · exact Bool.eq_false_iff.mpr unack

def Host.State.ReleaseSafe (s : Host.State) : Prop :=
  s.phase = 1#3 → s.opcode = 4#4 → s.unacknowledged = false

theorem Host.State.releaseSafe_step (s : Host.State) (i : Host.Input) (safe : s.FrameSafe) :
    (Host.step i s).ReleaseSafe := by
  intro phase operation
  rcases s.phase1_origin i phase with ⟨cold, closing, code⟩
  rcases s.closing_custody_fields i safe closing cold with ⟨request, data, start, bits, ack⟩
  have op : s.opcode = 4#4 := by simpa only [Host.State.opcode, request] using operation
  simpa only [Host.State.unacknowledged, Host.State.exportEnd, start, bits, ack] using s.release_code code op

/-- The actual frontend interval ends exactly at the cumulative core pop count. -/
structure Session.State.ExportInterval (s : Session.State a) : Prop where
  bits : s.host.exportBits.toNat ≤ 32
  ack : s.host.ackOffset = s.host.exportStart
  ending : s.host.exportStart.toNat + s.host.exportBits.toNat = s.core.rxPopped.toNat

def Host.State.receipt (s : Host.State) : Receipt :=
  ⟨s.exportData, s.exportStart, ⟨s.exportBits.toNat % 65, Nat.mod_lt _ (by decide)⟩, s.ackOffset⟩

theorem Session.State.ExportInterval.receipt_valid (s : Session.State a) (interval : s.ExportInterval)
    (order : s.core.rxPopped.toNat ≤ s.core.rxProduced.toNat) :
    s.host.receipt.Valid s.core.rxProduced.toNat s.core.rxPopped.toNat := by
  constructor
  · simp [Host.State.receipt, interval.ack]
  · simpa [Host.State.receipt, Nat.mod_eq_of_lt (show s.host.exportBits.toNat < 65 by have := interval.bits; omega)] using interval.ending
  · exact order
  · exact s.core.rxProduced.isLt

theorem Session.State.ExportInterval.end_word (s : Session.State a) (interval : s.ExportInterval) :
    s.host.exportEnd = s.core.rxPopped := by
  apply BitVec.eq_of_toNat_eq
  have bound := s.core.rxPopped.isLt
  have bits := interval.bits
  have ending := interval.ending
  simp only [Host.State.exportEnd, BitVec.toNat_add, BitVec.toNat_setWidth]
  omega

theorem Session.State.ExportInterval.unacknowledged (s : Session.State a) (interval : s.ExportInterval) :
    s.host.unacknowledged = true ↔ 0 < s.host.exportBits.toNat := by
  rw [Host.State.unacknowledged, interval.end_word s, bne_iff_ne, interval.ack]
  rw [← BitVec.toNat_ne_iff_ne]
  have ending := interval.ending
  omega

theorem Host.State.admit_export_fields (s : Host.State) (i : Host.Input) (cold : i.initialize = false)
    (admitted : s.admittingBulk i.status = true) :
    (Host.step i s).exportData = 0#64 ∧
    (Host.step i s).exportStart = i.status.rxPopped ∧
    (Host.step i s).exportBits = 0#7 ∧
    (Host.step i s).ackOffset = s.payload 64 16 := by
  have bulk : s.bulk = true := by
    simp only [Host.State.admittingBulk, Bool.and_eq_true] at admitted
    exact admitted.1.2
  simp [Host.step, cold, admitted, Host.State.clearingExport, Host.State.delivering, bulk]

theorem Host.State.capture_export_fields (s : Host.State) (i : Host.Input) (cold : i.initialize = false)
    (phase : s.phase = 2#3) (receiving : s.rxPending = true) :
    (Host.step i s).exportData = i.status.rxData.setWidth 64 ∧
    (Host.step i s).exportStart = s.exportStart ∧
    (Host.step i s).exportBits = i.status.rxBits.setWidth 7 ∧
    (Host.step i s).ackOffset = s.ackOffset := by
  simp [Host.step, cold, Host.State.clearingExport, Host.State.delivering,
    Host.State.admittingBulk, Host.State.stagedRX, phase, receiving]

theorem Session.State.core_clock_zero (s : Session.State a) (p : Program) (pending : Bool)
    (i : Session.Pins) (cold : i.initialize = false) (command : (s.command i).runtime.command = 0#4) :
    (s.step p pending i).core = clock p (s.command i).runtime s.core := by
  change Streaming.step p (s.command i).runtime s.core = _
  have coldInput : (s.command i).runtime.initialize = false := cold
  simp [Streaming.step, coldInput, command]

theorem Session.State.admission_command (s : Session.State a) (pending : Bool) (i : Session.Pins)
    (admitted : s.host.admittingBulk (s.hostInput pending i).status = true) :
    (s.command i).runtime.command = 0#4 ∧ (s.command i).runtime.rxPop = false := by
  have facts := admitted
  simp only [Host.State.admittingBulk, Bool.and_eq_true, beq_iff_eq] at facts
  rcases facts with ⟨⟨phase, bulk⟩, _⟩
  simp [Session.State.command, Host.State.command, Host.State.delivering, Host.State.stagedRX, phase, bulk]

theorem Session.State.ExportInterval.admit (s : Session.State a) (p : Program) (pending : Bool)
    (i : Session.Pins) (cold : i.initialize = false) (interval : s.ExportInterval)
    (admitted : s.host.admittingBulk (s.hostInput pending i).status = true) :
    (s.step p pending i).ExportInterval := by
  have fields := s.host.admit_export_fields (s.hostInput pending i) cold admitted
  have ack : s.host.payload 64 16 = s.core.rxPopped := by
    have facts := admitted
    simp only [Host.State.admittingBulk, Host.State.bulkAdmitted, Host.State.bulkOffsets,
      Bool.and_eq_true, beq_iff_eq] at facts
    exact facts.2.1.1.1.2.2.trans (interval.end_word s)
  have popped : (s.step p pending i).core.rxPopped = s.core.rxPopped := by
    rw [s.core_clock_zero p pending i cold (s.admission_command pending i admitted).1]
    simp [clock, State.hostPop, (s.admission_command pending i admitted).2, Queue.willPop]
  constructor
  · change (Host.step (s.hostInput pending i) s.host).exportBits.toNat ≤ 32
    rw [fields.2.2.1]
    decide
  · change (Host.step (s.hostInput pending i) s.host).ackOffset =
        (Host.step (s.hostInput pending i) s.host).exportStart
    rw [fields.2.2.2, fields.2.1, ack]
    rfl
  · change (Host.step (s.hostInput pending i) s.host).exportStart.toNat +
        (Host.step (s.hostInput pending i) s.host).exportBits.toNat = _
    rw [fields.2.1, fields.2.2.1, popped]
    rfl

theorem Session.State.ExportInterval.capture (s : Session.State a) (p : Program) (pending : Bool)
    (i : Session.Pins) (cold : i.initialize = false) (interval : s.ExportInterval)
    (empty : s.host.StageEmpty) (phase : s.host.phase = 2#3) (receiving : s.host.rxPending = true)
    (grant : s.StageGrant) (trace : BitTrace) (counts : trace.NaturalCounts s.core)
    (related : trace.Related s.core) (structural : s.core.Structural) (progress : s.core.Progress) :
    (s.step p pending i).ExportInterval := by
  have fields := s.host.capture_export_fields (s.hostInput pending i) cold phase receiving
  have ready := grant.receive receiving
  have bits : ((s.hostInput pending i).status.rxBits.setWidth 7).toNat = s.core.rx.peek.validBits := by
    have bound := s.core.rx.peek.validBits_le
    simp [Session.State.hostInput, Session.Pins.host, State.status, ready,
      BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show s.core.rx.peek.validBits < 64 by omega),
      Nat.mod_eq_of_lt (show s.core.rx.peek.validBits < 128 by omega)]
  have nextCounts := counts.clock p s.core (s.command i).runtime trace related structural progress
  have popped : (s.step p pending i).core.rxPopped.toNat =
      s.core.rxPopped.toNat + s.core.rx.peek.validBits := by
    rw [s.core_clock_zero p pending i cold (s.stage_command i phase).1, ← nextCounts.exported]
    simp [BitTrace.clock, State.exportedBits, s.stage_pop i phase grant receiving,
      counts.exported, Chunk.rxBits]
  have before : s.host.exportStart.toNat = s.core.rxPopped.toNat := by
    have ending := interval.ending
    rw [empty phase receiving] at ending
    simpa using ending
  constructor
  · change (Host.step (s.hostInput pending i) s.host).exportBits.toNat ≤ 32
    rw [fields.2.2.1, bits]
    exact s.core.rx.peek.validBits_le
  · change (Host.step (s.hostInput pending i) s.host).ackOffset =
        (Host.step (s.hostInput pending i) s.host).exportStart
    rw [fields.2.2.2, fields.2.1]
    exact interval.ack
  · change (Host.step (s.hostInput pending i) s.host).exportStart.toNat +
        (Host.step (s.hostInput pending i) s.host).exportBits.toNat = _
    rw [fields.2.1, fields.2.2.1, bits, before, popped]

theorem Host.State.command_operation (s : Host.State) (i : Host.Input) (operation : BitVec 4)
    (nonzero : operation ≠ 0#4) (notReset : operation ≠ 15#4)
    (command : (s.command i).runtime.command = operation) :
    s.delivering = true ∧ s.opcode = operation := by
  change (if s.delivering then (if s.opcode == 7 then 15 else s.opcode) else 0) = operation at command
  split at command
  · split at command
    · exact False.elim (notReset command.symm)
    · exact ⟨by assumption, command⟩
  · exact False.elim (nonzero command.symm)

theorem Session.State.accepted_clears (s : Session.State a) (pending : Bool) (i : Session.Pins)
    (accepted : ((s.command i).runtime.command == 3 && s.core.canStart (s.command i).runtime) = true ∨
      ((s.command i).runtime.command == 4 && s.core.canRelease (s.command i).runtime) = true) :
    s.host.clearingExport (s.hostInput pending i).status = true := by
  rcases accepted with start | release
  all_goals simp only [Bool.and_eq_true, beq_iff_eq] at *
  · obtain ⟨delivering, operation⟩ := s.host.command_operation (i.host {}) 3 (by decide) (by decide) start.1
    have phase : s.host.phase = 1#3 := by
      have facts := delivering
      simp only [Host.State.delivering, Bool.and_eq_true, beq_iff_eq] at facts
      exact facts.1.1
    have inactive : (s.command i).runtime.txPush = false ∧ (s.command i).runtime.rxPop = false := by
      simp [Session.State.command, Host.State.command, Host.State.stagedTX, Host.State.stagedRX, phase]
    have rejected : (s.hostInput pending i).status.rejected = false := by
      change (s.core.status pending (s.command i).runtime).rejected = false
      simp [State.status, start.1, start.2, inactive.1, inactive.2]
    simp [Host.State.clearingExport, delivering, operation, rejected]
  · obtain ⟨delivering, operation⟩ := s.host.command_operation (i.host {}) 4 (by decide) (by decide) release.1
    have phase : s.host.phase = 1#3 := by
      have facts := delivering
      simp only [Host.State.delivering, Bool.and_eq_true, beq_iff_eq] at facts
      exact facts.1.1
    have inactive : (s.command i).runtime.txPush = false ∧ (s.command i).runtime.rxPop = false := by
      simp [Session.State.command, Host.State.command, Host.State.stagedTX, Host.State.stagedRX, phase]
    have rejected : (s.hostInput pending i).status.rejected = false := by
      change (s.core.status pending (s.command i).runtime).rejected = false
      simp [State.status, release.1, release.2, inactive.1, inactive.2]
    simp [Host.State.clearingExport, delivering, operation, rejected]

theorem Session.State.core_clock_no_clear (s : Session.State a) (p : Program) (pending : Bool)
    (i : Session.Pins) (runtime : Session.RuntimeInput s i)
    (clearing : s.host.clearingExport (s.hostInput pending i).status = false) :
    (s.step p pending i).core = clock p (s.command i).runtime s.core := by
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
  change Streaming.step p (s.command i).runtime s.core = _
  have warm : (s.command i).runtime.command ≠ 15#4 := runtime.2.1
  simp only [Streaming.step, noStart, noRelease]
  simp [runtime.1, warm]

theorem Session.State.ExportInterval.hold (s : Session.State a) (p : Program) (pending : Bool)
    (i : Session.Pins) (runtime : Session.RuntimeInput s i) (interval : s.ExportInterval)
    (clearing : s.host.clearingExport (s.hostInput pending i).status = false)
    (admitting : s.host.admittingBulk (s.hostInput pending i).status = false)
    (capturing : s.host.stagedRX = false) : (s.step p pending i).ExportInterval := by
  have cold : (s.hostInput pending i).initialize = false := runtime.1
  have popped : (s.step p pending i).core.rxPopped = s.core.rxPopped := by
    rw [s.core_clock_no_clear p pending i runtime clearing]
    have pop : (s.command i).runtime.rxPop = false := capturing
    simp [clock, State.hostPop, pop, Queue.willPop]
  constructor
  · simpa only [Session.State.step, Host.step, cold, Bool.false_eq_true, ↓reduceIte,
      clearing, admitting, capturing] using interval.bits
  · simpa only [Session.State.step, Host.step, cold, Bool.false_eq_true, ↓reduceIte,
      clearing, admitting, capturing] using interval.ack
  · change (Host.step (s.hostInput pending i) s.host).exportStart.toNat +
        (Host.step (s.hostInput pending i) s.host).exportBits.toNat = _
    simpa only [Host.step, cold, Bool.false_eq_true, ↓reduceIte, clearing, admitting, capturing, popped] using interval.ending

theorem Session.State.clearing_accepted (s : Session.State a) (pending : Bool) (i : Session.Pins)
    (runtime : Session.RuntimeInput s i)
    (clearing : s.host.clearingExport (s.hostInput pending i).status = true) :
    ((s.command i).runtime.command == 3 && s.core.canStart (s.command i).runtime) = true ∨
      ((s.command i).runtime.command == 4 && s.core.canRelease (s.command i).runtime) = true := by
  have facts := clearing
  simp only [Host.State.clearingExport, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true,
    beq_iff_eq] at facts
  rcases facts with ⟨⟨delivering, rejected⟩, operation⟩
  have phase : s.host.phase = 1#3 := by
    have before := delivering
    simp only [Host.State.delivering, Bool.and_eq_true, beq_iff_eq] at before
    exact before.1.1
  have inactive : (s.command i).runtime.txPush = false ∧ (s.command i).runtime.rxPop = false := by
    simp [Session.State.command, Host.State.command, Host.State.stagedTX, Host.State.stagedRX, phase]
  change (s.core.status pending (s.command i).runtime).rejected = false at rejected
  rcases operation with (start | release) | reset
  · have command : (s.command i).runtime.command = 3#4 := by
      simp [Session.State.command, Host.State.command, delivering, start]
    left
    simpa [State.status, command, inactive.1, inactive.2] using rejected
  · have command : (s.command i).runtime.command = 4#4 := by
      simp [Session.State.command, Host.State.command, delivering, release]
    right
    simpa [State.status, command, inactive.1, inactive.2] using rejected
  · have command : (s.command i).runtime.command = 15#4 := by
      simp [Session.State.command, Host.State.command, delivering, reset]
    exact False.elim (runtime.2.1 command)

theorem Session.State.ExportInterval.clear (s : Session.State a) (p : Program) (pending : Bool)
    (i : Session.Pins) (runtime : Session.RuntimeInput s i)
    (clearing : s.host.clearingExport (s.hostInput pending i).status = true) :
    (s.step p pending i).ExportInterval := by
  have cold : (s.hostInput pending i).initialize = false := runtime.1
  have popped : (s.step p pending i).core.rxPopped = 0#16 := by
    rcases s.clearing_accepted pending i runtime clearing with start | release
    · simp only [Bool.and_eq_true, beq_iff_eq] at start
      simp [Session.State.step, Streaming.step, runtime.1, start.1, start.2, State.start]
    · simp only [Bool.and_eq_true, beq_iff_eq] at release
      simp [Session.State.step, Streaming.step, runtime.1, release.1, release.2, State.release]
  constructor
  · simp [Session.State.step, Host.step, cold, clearing]
  · simp [Session.State.step, Host.step, cold, clearing]
  · change (Host.step (s.hostInput pending i) s.host).exportStart.toNat +
        (Host.step (s.hostInput pending i) s.host).exportBits.toNat = _
    simp [Host.step, cold, clearing, popped]

theorem Session.State.ExportInterval.step (s : Session.State a) (p : Program) (pending : Bool)
    (i : Session.Pins) (runtime : Session.RuntimeInput s i) (interval : s.ExportInterval)
    (empty : s.host.StageEmpty) (reservation : s.host.phase = 2#3 → s.StageGrant)
    (trace : BitTrace) (counts : trace.NaturalCounts s.core) (related : trace.Related s.core)
    (structural : s.core.Structural) (progress : s.core.Progress) :
    (s.step p pending i).ExportInterval := by
  by_cases clearing : s.host.clearingExport (s.hostInput pending i).status = true
  · exact Session.State.ExportInterval.clear s p pending i runtime clearing
  · have noClear := Bool.eq_false_iff.mpr clearing
    by_cases admitting : s.host.admittingBulk (s.hostInput pending i).status = true
    · exact interval.admit s p pending i runtime.1 admitting
    · have noAdmit := Bool.eq_false_iff.mpr admitting
      by_cases capturing : s.host.stagedRX = true
      · have capture := capturing
        simp only [Host.State.stagedRX, Bool.and_eq_true, beq_iff_eq] at capture
        exact interval.capture s p pending i runtime.1 empty capture.1 capture.2
          (reservation capture.1) trace counts related structural progress
      · exact interval.hold s p pending i runtime noClear noAdmit (Bool.eq_false_iff.mpr capturing)

structure Host.State.ControlSafe (s : Host.State) : Prop where
  frames : s.FrameSafe
  empty : s.StageEmpty
  release : s.ReleaseSafe

theorem Host.State.controlSafe_step (s : Host.State) (i : Host.Input) (safe : s.ControlSafe) :
    (Host.step i s).ControlSafe :=
  ⟨s.frameSafe_step i safe.frames, s.stageEmpty_step i, s.releaseSafe_step i safe.frames⟩

theorem Host.State.controlSafe_cold (s : Host.State) (i : Host.Input) (cold : i.initialize = true) :
    (Host.step i s).ControlSafe := by
  constructor <;> simp [Host.step, cold, Host.State.FrameSafe, Host.State.StageEmpty, Host.State.ReleaseSafe]

theorem Host.State.controlSafe_run (s : Host.State) (inputs : List Host.Input) (safe : s.ControlSafe) :
    (Host.run s inputs).ControlSafe := by
  induction inputs generalizing s with
  | nil => exact safe
  | cons i inputs induction => exact induction (Host.step i s) (s.controlSafe_step i safe)

theorem Session.State.release_requires_ack (s : Session.State a) (i : Session.Pins)
    (safe : s.host.ReleaseSafe) (interval : s.ExportInterval)
    (command : (s.command i).runtime.command = 4#4) : s.host.exportBits.toNat = 0 := by
  obtain ⟨delivering, operation⟩ := s.host.command_operation (i.host {}) 4 (by decide) (by decide) command
  have phase : s.host.phase = 1#3 := by
    have facts := delivering
    simp only [Host.State.delivering, Bool.and_eq_true, beq_iff_eq] at facts
    exact facts.1.1
  have acknowledged := safe phase operation
  have equivalence := interval.unacknowledged s
  have notPositive : ¬0 < s.host.exportBits.toNat := by
    intro positive
    have unack := equivalence.mpr positive
    simp [acknowledged] at unack
  omega

end Pinwheel.Program.Streaming
