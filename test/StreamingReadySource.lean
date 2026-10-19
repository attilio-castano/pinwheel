import Pinwheel.Program.StreamingReadyTiming

/-! Directed source controls distinguish delayed readiness, final-tick priority,
old-prefix timeout export, atomic FIFO credit, and 16-bit endpoints. These are
kernel computations on small independent fixtures, not a substitute for the
universal transition and conservation theorems. -/
namespace Pinwheel.Test.StreamingReadySource
open Pinwheel.Program.StreamingReady

private def program : Program :=
  ⟨Vector.replicate 64 .halt,⟨0,by decide⟩,{}⟩

private def duplex : Cell := {transmit := true,receive := true}
private def readyOne : Guard := ⟨1,1,.misses ⟨0,by decide⟩⟩
private def timeoutState : State 1 :=
  {phase := .waiting,current := .stream duplex (some readyOne),total := 9,remaining := 1,
    countdown := 0,rxPartial := 165,rxUsed := 8,rxProduced := 8,txConsumed := 9,
    txAccepted := 9,transfer := 1,pins := ⟨2,7⟩}

/-- Timeout returns the eight old samples, never a ninth current raw bit. -/
example : let s := step program {rawInputs := 3} timeoutState
    s.phase = .fault ∧ s.rxProduced = 8 ∧ s.txConsumed = 9 ∧ s.rxUsed = 0 ∧
      s.rxPartial = 0 ∧ s.rx.count = 1 ∧ s.rx.peek.data = 165 ∧ s.rx.peek.validBits = 8 := by decide

/-- The same zero-countdown cut accepts old sampled readiness before timeout. -/
example : let s := step program {rawInputs := 0} {timeoutState with samplerSecond := 1}
    s.phase = .high ∧ s.rxProduced = 9 ∧ s.rx.peek.data = 331 ∧ s.rx.peek.validBits = 9 ∧
      s.pins = timeoutState.pins := by decide

private def oldWord : Chunk := ⟨3,⟨1,by decide⟩⟩
private def queuedTimeout : State 1 :=
  {timeoutState with rx := timeoutState.rx.tick (some oldWord) false}

/-- A simultaneous host pop exports the old head; the timeout prefix remains owned. -/
example : let s := step program {rxPop := true,expectedTransfer := 1} queuedTimeout
    s.rxPopped = 2 ∧ s.rxProduced = 8 ∧ s.rx.count = 1 ∧
      s.rx.peek.data = 165 ∧ s.rx.peek.validBits = 8 := by decide

private def unboundedState : State 1 :=
  {timeoutState with
    current := .stream duplex (some ⟨1,1,.unbounded⟩)
    countdown := 173,rxPartial := 0,rxUsed := 0,rxProduced := 0,remaining := 9}

/-- Failed unbounded polls hold arbitrary timers while both samplers advance. -/
example : let s := run program unboundedState [{rawInputs := 1},{rawInputs := 1}]
    s.phase = .waiting ∧ s.countdown = 173 ∧ s.samplerFirst = 1 ∧ s.samplerSecond = 1 ∧
      s.rxProduced = 0 ∧ s.pins = unboundedState.pins := by decide

example : let s := run program unboundedState [{rawInputs := 1},{rawInputs := 1},{rawInputs := 0}]
    s.phase = .high ∧ s.rxProduced = 1 ∧ s.rxPartial = 1 ∧ s.countdown = 0 := by decide

private def boundaryState : State 1 :=
  {phase := .boundary,current := .stream {transmit := true} none,
    total := 1,remaining := 1,transfer := 1}
private def oneBit : Input :=
  {txPush := true,txData := 2147483648,txBits := 1,expectedTransfer := 1}

/-- A newly offered TX word cannot satisfy credit on that same boundary edge. -/
example : let s := step program oneBit boundaryState
    s.phase = .boundary ∧ s.txAccepted = 1 ∧ s.txConsumed = 0 ∧ s.tx.count = 1 := by decide

example : let s := step program {} (step program oneBit boundaryState)
    s.phase = .low ∧ s.txAccepted = 1 ∧ s.txConsumed = 1 ∧ s.cellBit = true ∧ s.tx.count = 0 := by decide

/-- Total represented WAIT states use opcode class, even without an encoded guard. -/
example : (engine program {unboundedState with current := .stream duplex none}).phase = .high := by decide
example : let s := engine program {unboundedState with current := .driveWait ⟨5,3⟩ {}}
    s.phase = .fetch ∧ s.pc = 1 ∧ s.countdown = 0 ∧ s.pins = unboundedState.pins := by decide

/-- Malformed expected bits are compared directly, not silently masked away. -/
example : (Guard.matches ⟨1,2,.unbounded⟩ 3) = false := by decide

/-- The last accepted bit reaches 65535 without wrapping to zero. -/
example : let s := step program oneBit {boundaryState with total := 65535,txAccepted := 65534}
    s.txAccepted = 65535 ∧ s.tx.count = 1 := by decide


/-- A previously reserved host word may arrive on the timeout edge. It remains
owned in the fixed TX FIFO and prevents a drained RELEASE; reset cancels it. -/
example : let failed := step program oneBit {timeoutState with total := 10}
    let drainedRx := step program {rxPop := true,expectedTransfer := 1} failed
    let rejectedRelease := step program {command := 4,expectedTransfer := 1} drainedRx
    let canceled := step program {command := 15} rejectedRelease
    rejectedRelease.phase = .fault ∧ rejectedRelease.tx.count = 1 ∧
      rejectedRelease.txAccepted = 10 ∧ rejectedRelease.txConsumed = 9 ∧
      canceled.phase = .free ∧ canceled.tx.count = 0 ∧ canceled.transfer = 1 := by decide

end Pinwheel.Test.StreamingReadySource
