import Pinwheel.Program.StreamingReadyRegisterReadVariants
import Pinwheel.Program.StreamingReadySegmentReadback
import Pinwheel.Program.StreamingReadySegmentExecution

/-! External sampler windows and the combined register-read wire contract. -/
namespace Pinwheel.Program.StreamingReadySegments.Wire

open StreamingReady (Guard I2cProfile Pins)
open Execution

/-- A bounded guard's preceding unqualified samples, shared by the ready
    and expired outcomes. Guard qualification uses the final eligible sample. -/
structure PollWindow (guard : Guard) where
  limit : Fin 255
  bounded : guard.limit = .misses limit
  misses : List (BitVec 2)
  unqualified : misses.any guard.matches = false
  within : misses.length ≤ limit.val

def PollWindow.samples {guard : Guard} (window : PollWindow guard) (last : BitVec 2) : List (BitVec 2) :=
  window.misses ++ [last]

theorem PollWindow.accept {guard : Guard} (window : PollWindow guard) (last : BitVec 2)
    (ready : guard.matches last = true) : pollWindow guard (window.samples last) = some (some last) := by
  simp [PollWindow.samples, pollWindow_after_misses _ _ window.bounded _ _ window.unqualified window.within, ready]
  done

theorem PollWindow.expire {guard : Guard} (window : PollWindow guard) (last : BitVec 2)
    (notReady : guard.matches last = false) (exhausted : window.misses.length = window.limit.val) :
    pollWindow guard (window.samples last) = some none := by
  simp [PollWindow.samples, pollWindow_after_misses _ _ window.bounded _ _ window.unqualified window.within,
    notReady, exhausted]
  done

/-- SCL is released by both parties. SDA is the independently resolved wire bit. -/
def highSample (data : Bool) : BitVec 2 := StreamingI2CRead.busRaw ⟨true, data⟩

private def bitObservation (data : Bool) : Observation := .cell 0 [highSample data]

def resolvedData (request : I2C.RegisterRead.Request) (target : I2C.RegisterReadPeer.Target) : List Bool :=
  ((List.finRange 36).take target.stopAfter).map fun slot =>
    I2C.resolveLine (I2C.RegisterRead.dataDrive request slot) (I2C.RegisterReadPeer.bitDrive target slot.val)

/-- Place the START and STOP aperture samples around the peer's wire data.
    The first two bytes precede the repeated START. -/
def timelyObservations (request : I2C.RegisterRead.Request) (target : I2C.RegisterReadPeer.Target) :
    List Observation :=
  let bits := (resolvedData request target).map bitObservation
  if bits.length ≤ 18 then [.wait [3]] ++ bits ++ [.wait [1]]
  else [.wait [3]] ++ bits.take 18 ++ [.wait [3]] ++ bits.drop 18 ++ [.wait [1]]

/-- Stop releasing SCL through the complete poll budget of the specified
    open-drain slot. The aperture history preceding it agrees with the peer. -/
def deadlineObservations (request : I2C.RegisterRead.Request) (target : I2C.RegisterReadPeer.Target)
    (slot : Fin 36) : List Observation :=
  let bits := ((resolvedData request target).take slot.val).map bitObservation
  let blocked := Observation.cell 0 (List.replicate (I2cProfile.standard.budgetMinusOne.val + 1) 0)
  if slot.val < 18 then [.wait [3]] ++ bits ++ [blocked]
  else [.wait [3]] ++ bits.take 18 ++ [.wait [3]] ++ bits.drop 18 ++ [blocked]

structure Summary where
  terminal : Terminal
  captured : List Bool
  reserved : List Bool
  remainingTX : List Bool
  pending : List Observation
  last : Option Event
  deriving DecidableEq

def summarize (result : Result) : Summary :=
  ⟨result.terminal, result.rxBits, result.txBits, result.remainingTX,
    result.remainingObservations, result.events.getLast?⟩

def timelyExpected (request : I2C.RegisterRead.Request) (target : I2C.RegisterReadPeer.Target) :
    Summary :=
  let clocks := match target.nack with
    | none => 1598
    | some stage => if stage.val == 0 then 458 else if stage.val == 1 then 821 else 1236
  let extent := target.stopAfter
  let terminal := Terminal.planned ⟨if target.nack.isSome then .discard else .complete, extent, extent, clocks⟩
  ⟨terminal, expectedRegisterRead request target, (registerReadTX request).take extent,
    (registerReadTX request).drop extent, [], some (.drive {})⟩

def deadlineTerminal (slot : Fin 36) : Terminal :=
  let pc := if slot.val < 9 then 3 else if slot.val < 18 then 6 else if slot.val < 27 then 12 else 15
  .timeout pc (slot.val % 9)

def deadlineExpected (request : I2C.RegisterRead.Request) (target : I2C.RegisterReadPeer.Target)
    (slot : Fin 36) : Summary :=
  ⟨deadlineTerminal slot, (expectedRegisterRead request target).take slot.val,
    (registerReadTX request).take (slot.val + 1), (registerReadTX request).drop (slot.val + 1),
    [], some (.drive {})⟩

abbrev fixtureRequest : I2C.RegisterRead.Request := ⟨0x53, 0xA6⟩

private def runTimely (target : I2C.RegisterReadPeer.Target) : Option Summary :=
  (run (registerReadRows .standard) 36 (registerReadTX fixtureRequest)
    (timelyObservations fixtureRequest target)).map summarize

private def runDeadline (target : I2C.RegisterReadPeer.Target) (slot : Fin 36) : Option Summary :=
  (run (registerReadRows .standard) 36 (registerReadTX fixtureRequest)
    (deadlineObservations fixtureRequest target slot)).map summarize

private def checksPayloads (bytes : List (Fin 256)) : Bool :=
  bytes.all fun byte =>
    let target : I2C.RegisterReadPeer.Target := ⟨BitVec.ofFin byte, none, 0⟩
    decide (runTimely target = some (timelyExpected fixtureRequest target))

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem payloads_checked : checksPayloads (List.finRange 256) = true := by
  decide +kernel
  done

/-- Every reply byte traverses the all-ACK path of the checked image, with
    exactly the chronological wire samples and all 36 TX reservations. -/
theorem timely_read (payload : BitVec 8) :
    let target : I2C.RegisterReadPeer.Target := ⟨payload, none, 0⟩
    (run (registerReadRows .standard) 36 (registerReadTX fixtureRequest)
      (timelyObservations fixtureRequest target)).map summarize = some (timelyExpected fixtureRequest target) := by
  have verified := List.all_eq_true.mp payloads_checked payload.toFin (List.mem_finRange _)
  simpa only [BitVec.ofFin_toFin, runTimely] using of_decide_eq_true verified
  done

set_option maxRecDepth 8192 in
/-- The first NACK fences off all later wire data and reserves exactly the
    prefix ending on that NACK. The remaining TX list is the unsent suffix. -/
theorem early_nack (stage : Fin 3) :
    let target : I2C.RegisterReadPeer.Target := ⟨0, some stage, 0⟩
    (run (registerReadRows .standard) 36 (registerReadTX fixtureRequest)
      (timelyObservations fixtureRequest target)).map summarize = some (timelyExpected fixtureRequest target) := by
  have cases : stage = 0 ∨ stage = 1 ∨ stage = 2 := by omega
  rcases cases with rfl | rfl | rfl <;> decide +kernel
  done

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem deadlines_checked : (List.finRange 36).all (fun slot =>
    decide (runDeadline ⟨0x96, none, 0⟩ slot = some (deadlineExpected fixtureRequest ⟨0x96, none, 0⟩ slot))) = true := by
  decide +kernel
  done

/-- At any of the 36 streaming slots on the fixture's all-ACK path, the
    blocked aperture contributes one reservation and no capture. -/
theorem stream_deadline (slot : Fin 36) :
    let target : I2C.RegisterReadPeer.Target := ⟨0x96, none, 0⟩
    (run (registerReadRows .standard) 36 (registerReadTX fixtureRequest)
      (deadlineObservations fixtureRequest target slot)).map summarize =
        some (deadlineExpected fixtureRequest target slot) := by
  exact of_decide_eq_true (List.all_eq_true.mp deadlines_checked slot (List.mem_finRange _))
  done

end Pinwheel.Program.StreamingReadySegments.Wire
