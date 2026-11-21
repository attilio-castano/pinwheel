import Pinwheel.Hardware.StreamingReady.SegmentTraceTimeout

/-! The raw readiness edge at the deadline is accepted. Moving that edge
    one clock later must produce a retained timeout on either store. -/
namespace Pinwheel.Test.StreamingReadyTraceContract

open Pinwheel.Hardware Pinwheel.Hardware.StreamingReady
open SegmentCore SegmentPathControl SegmentTiming
open Pinwheel.Program.StreamingReadySegments (Row)

private def imageRows : List Row :=
  [.cell (.driveWait ⟨0, 1⟩ ⟨1, 1, .misses 0⟩), .cell .halt]

private def installedState : Values (Register 1)
  | _, .base .valid => 1
  | _, .base .count => 2
  | _, .base (.word k) => (imageRows[k.toNat]?.map Row.encode).getD 0
  | _, .fetched => (imageRows[0]?.map Row.encode).getD 0
  | _, _ => 0

private theorem installed : Installed imageRows installedState := by
  refine ⟨by decide, rfl, rfl, ?_⟩
  intro atIndex
  have small : atIndex.val < 64 := Nat.lt_trans atIndex.isLt (by decide)
  simp [installedState, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]

private def clock (command : BitVec 4) (raw : BitVec 2) : Values StreamingReady.Core.Input
  | _, .command => command
  | _, .rawInputs => raw
  | _, _ => 0

private def started (registered : Bool) (raw : BitVec 2) : Values (Register 1) :=
  (circuit 1 registered).step (clock 3 raw) installedState

private theorem admitted (raw : BitVec 2) :
    StreamingReady.Core.starting.eval (clock 3 raw) (project installedState) = 1#1 := by
  decide +revert +kernel

example (registered : Bool) :
    SegmentTraceTimeout.accepts registered (started registered 1) [clock 0 0] (clock 0 0) = false := by
  cases registered <;> decide +kernel

example (registered : Bool) :
    run registered installedState [clock 3 1, clock 0 0, clock 0 0, clock 0 0] (.base .phase) = 5#3 := by
  have active : SegmentTrace.active registered (started registered 1) [clock 0 0, clock 0 0] = true := by
    cases registered <;> decide +kernel
  have closing : SegmentTrace.closing imageRows false (clock 0 0)
      (run registered (started registered 1) [clock 0 0, clock 0 0]) = true := by
    cases registered <;> decide +kernel
  exact (SegmentTrace.closes_from_start registered installedState (clock 3 1) (clock 0 0)
    [clock 0 0, clock 0 0] false installed (admitted 1) active closing).1

example (registered : Bool) :
    run registered installedState [clock 3 0, clock 0 1, clock 0 0] (.base .phase) = 6#3 ∧
      run registered installedState [clock 3 0, clock 0 1, clock 0 0] (.base .rxProduced) = 0#16 := by
  have expiry : SegmentTraceTimeout.accepts registered (started registered 0) [clock 0 1] (clock 0 0) = true := by
    cases registered <;> decide +kernel
  have result := SegmentTraceTimeout.from_start registered installedState (clock 3 0) (clock 0 0)
    installed (admitted 0) expiry
  have empty : (SegmentTrace.observe registered (started registered 0) [clock 0 1]).rx.length = 0 := by
    cases registered <;> decide +kernel
  exact ⟨result.2.1, result.2.2.2.2.2.1.trans (congrArg (BitVec.ofNat 16) empty)⟩

end Pinwheel.Test.StreamingReadyTraceContract
