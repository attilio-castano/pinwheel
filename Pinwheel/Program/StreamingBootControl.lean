import Pinwheel.Program.StreamingHostExecution

/-! The source host control used by concrete physical loader certificates.
Response payload storage is omitted. During non-bulk boot clocks, status
affects this control only through command rejection. -/
namespace Pinwheel.Program.Streaming.Host.BootControl

structure State where
  sckPrev : Bool := false
  csnPrev : Bool := false
  active : Bool := false
  reading : Bool := false
  count : BitVec 7 := 0
  request : BitVec 176 := 0
  requestCRC : BitVec 16 := 0
  phase : BitVec 3 := 0
  code : BitVec 4 := 0
  sequence : BitVec 16 := 0
  cacheReply : Bool := false
  ready : Bool := false
  lastValid : Bool := false
  lastRequest : BitVec 176 := 0
  txLeft : BitVec 7 := 0
  txStaging : BitVec 64 := 0
  rxPending : Bool := false
  workBulk : Bool := false
  exportStart : BitVec 16 := 0
  exportBits : BitVec 7 := 0
  ackOffset : BitVec 16 := 0
  crcCount : BitVec 6 := 0
  deriving DecidableEq, Repr

def project (s : Host.State) : State :=
  { sckPrev := s.sckPrev, csnPrev := s.csnPrev, active := s.active, reading := s.reading
    count := s.count, request := s.request, requestCRC := s.requestCRC, phase := s.phase
    code := s.code, sequence := s.sequence, cacheReply := s.cacheReply, ready := s.ready
    lastValid := s.lastValid, lastRequest := s.lastRequest, txLeft := s.txLeft
    txStaging := s.txStaging, rxPending := s.rxPending, workBulk := s.workBulk
    exportStart := s.exportStart, exportBits := s.exportBits, ackOffset := s.ackOffset
    crcCount := s.crcCount }

def restore (s : State) : Host.State :=
  { sckPrev := s.sckPrev, csnPrev := s.csnPrev, active := s.active, reading := s.reading
    count := s.count, request := s.request, requestCRC := s.requestCRC, phase := s.phase
    code := s.code, sequence := s.sequence, cacheReply := s.cacheReply, ready := s.ready
    lastValid := s.lastValid, lastRequest := s.lastRequest, txLeft := s.txLeft
    txStaging := s.txStaging, rxPending := s.rxPending, workBulk := s.workBulk
    exportStart := s.exportStart, exportBits := s.exportBits, ackOffset := s.ackOffset
    crcCount := s.crcCount }

def rawStep (i : Host.Input) (s : State) : State := project (Host.step i (restore s))

def input (rejected : Bool) (i : Host.Input) : Host.Input :=
  { i with status := { rejected := rejected } }

def step (rejected : Bool) (i : Host.Input) (s : State) : State := rawStep (input rejected i) s

def command (i : Host.Input) (s : State) : Host.Command := (restore s).command i

def Safe (s : State) : Prop :=
  s.phase ≠ 2#3 ∧ (s.phase = 1#3 → (restore s).bulk = false)

theorem raw_step_correct (i : Host.Input) (s : Host.State) :
    project (Host.step i s) = rawStep i (project s) := by
  by_cases cold : i.initialize
  all_goals simp only [rawStep,Host.step,cold,Bool.false_eq_true,ite_true,ite_false,
    Host.State.startingFrame,Host.State.closing,Host.State.taking,Host.State.receiving,
    Host.State.closingRequest,Host.State.closingReadExact,Host.State.bulk,
    Host.State.supported,Host.State.opcode,Host.State.payload,Host.State.headerValid,
    Host.State.wireValid,Host.State.duplicate,Host.State.sequenceNew,Host.State.requestSequence,
    Host.State.exportEnd,Host.State.unacknowledged,Host.State.payloadCanonical,Host.State.closingCode,
    Host.State.wanted,Host.State.requestedBits,Host.State.beatsNeeded,Host.State.tailCanonical,
    Host.State.bulkOwner,Host.State.bulkOffsets,Host.State.bulkAdmitted,Host.State.admittingBulk,
    Host.State.delivering,Host.State.clearingExport,Host.State.stagedTX,Host.State.stagedRX,
    Host.State.stagedBits,Host.State.stageRejected,Host.State.stageDone,Host.State.finishingCRC,
    project,restore]
  all_goals rfl
  done

theorem project_restore (s : State) : project (restore s) = s := by
  rfl

theorem command_correct (i : Host.Input) (s : Host.State) :
    s.command i = command i (project s) := by
  rfl

theorem command_status (i : Host.Input) (s : State) (status : Host.Status) :
    command {i with status := status} s = command i s := by
  rfl

theorem safe_not_admitting (s : State) (safe : Safe s) (status : Host.Status) :
    (restore s).admittingBulk status = false := by
  by_cases one : s.phase = 1#3
  · have bulk := safe.2 one
    simp [Host.State.admittingBulk,bulk]
  · simp [Host.State.admittingBulk,restore,one]
  done

theorem raw_step_rejected (i : Host.Input) (s : State) (safe : Safe s) :
    rawStep i s = step i.status.rejected i s := by
  have two : (restore s).phase ≠ 2#3 := safe.1
  by_cases cold : i.initialize
  · simp [rawStep,step,input,Host.step,cold,project]
  · by_cases one : s.phase = 1#3
    · have bulk := safe.2 one
      simp [step,rawStep,input,Host.step,cold,safe_not_admitting s safe,
        Host.State.stageRejected,Host.State.stagedRX,two,bulk,project,
        Host.State.startingFrame,Host.State.closing,Host.State.taking,Host.State.receiving,
        Host.State.closingRequest,Host.State.closingReadExact,Host.State.clearingExport]
      done
    · have notOne : (restore s).phase ≠ 1#3 := one
      simp [step,rawStep,input,Host.step,cold,safe_not_admitting s safe,
        Host.State.stageRejected,Host.State.stagedRX,two,notOne,project,
        Host.State.startingFrame,Host.State.closing,Host.State.taking,Host.State.receiving,
        Host.State.closingRequest,Host.State.closingReadExact,Host.State.clearingExport]
  done

/-- Loader-safe control depends on feedback only through the actual rejection
bit. Receipt payloads and CRC work never enter the command-control relation. -/
theorem step_correct (i : Host.Input) (s : Host.State) (safe : Safe (project s)) :
    project (Host.step i s) = step i.status.rejected i (project s) := by
  exact (raw_step_correct i s).trans (raw_step_rejected i (project s) safe)

end Pinwheel.Program.Streaming.Host.BootControl
