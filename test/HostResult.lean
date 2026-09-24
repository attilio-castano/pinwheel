import Pinwheel.Hardware.HostResult
import Pinwheel.Hardware.Storage.OnePortAdmission

open Pinwheel.Hardware

private def outputs (mode : BitVec 3) (samples : BitVec 16) (started rejected : Bool := false) :
    Values Loader.Machine.Output
  | _, .core .busy => BitVec.ofBool (1 ≤ mode.toNat && mode.toNat ≤ 4)
  | _, .core (.state .mode) => mode
  | _, .core (.state (.sample k)) => samples.extractLsb' k.val 1
  | _, .control .start => BitVec.ofBool started
  | _, .control .rejected => BitVec.ofBool rejected
  | _, _ => 0

def main : IO Unit := do
  let pins : Chip.Pins := {}
  let initialized : HostResult.State := {resetFirst := true, resetSecond := true}
  let active := HostResult.next pins (outputs 3 0) initialized
  let completed := HostResult.next pins (outputs 5 0xa653) active
  unless completed.valid && completed.samples == 0xa653 && completed.outcome == 5 do
    throw (IO.userError "Completion was not retained")
  let occupied := HostResult.next pins (outputs 3 0) completed
  let overrun := HostResult.next pins (outputs 6 0x55aa) occupied
  unless overrun.valid && overrun.overrun && overrun.samples == 0xa653 && overrun.outcome == 5 do
    throw (IO.userError "Unread result was overwritten")
  let simultaneous := HostResult.next pins (outputs 7 0x1234 true true)
    {overrun with wasActive := true, controlSecond := 3, consumePrev := false, clearPrev := false}
  unless simultaneous.valid && !simultaneous.overrun && simultaneous.rejected &&
      simultaneous.samples == 0x1234 && simultaneous.outcome == 7 do
    throw (IO.userError "Consume/arrival or clear/new-error priority changed")
  let heldHigh := HostResult.next pins (outputs 0 0)
    {simultaneous with controlSecond := 3, consumePrev := true, clearPrev := true}
  unless heldHigh.valid && heldHigh.samples == 0x1234 do
    throw (IO.userError "Held consume consumed twice")
  let consumed := HostResult.next pins (outputs 0 0) {heldHigh with controlSecond := 1, consumePrev := false}
  unless !consumed.valid do throw (IO.userError "Consume did not release result")
  let empty := HostResult.next pins (outputs 0 0) {consumed with consumePrev := false}
  unless !empty.valid do throw (IO.userError "Empty consumption created a result")
  let immediate := HostResult.next pins (outputs 5 0)
    (HostResult.next pins (outputs 0 0 true) initialized)
  unless immediate.valid && immediate.outcome == 5 do
    throw (IO.userError "Halt-only start did not produce a result")
  let cancelled := HostResult.next pins (outputs 0 0) active
  unless !cancelled.valid do throw (IO.userError "Engine reset created a result")
  let reset := HostResult.next {pins with rstN := false} (outputs 5 0xffff true true) overrun
  unless !reset.valid && !reset.overrun && !reset.rejected && reset.samples == 0 do
    throw (IO.userError "Chip reset did not clear the mailbox")
  unless HostResult.shown (outputs 0 0) {completed with pageSecond := 1} .uoOut == 0x53 &&
      HostResult.shown (outputs 0 0) {completed with pageSecond := 2} .uoOut == 0xa6 &&
      HostResult.shown (outputs 0 0) {completed with pageSecond := 3} .uoOut == 0xb1 do
    throw (IO.userError "Result page order or interface version changed")
  IO.println "Host result: retention, overflow, consume/arrival, reset, immediate completion and pages passed"
