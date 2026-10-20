import Pinwheel.Hardware.StreamingReady.Core

/-! Exact reuse boundary for the existing loader. FREE equivalence is universal
over register contents and inputs. Cold observations are deliberately absent:
the old and Ready pre-edge BUSY meanings differ at phase7. -/
namespace Pinwheel.Hardware.StreamingReady.LoaderEquivalence
open Pinwheel.Hardware
set_option linter.unusedSimpArgs false

private theorem and_one (x : BitVec 1) : x &&& 1#1 = x := by
  have all : ∀ x : BitVec 1, x &&& 1#1 = x := by decide +kernel
  exact all x
attribute [local simp] and_one

theorem cold_step_equal (i : Values Core.Input) (r : Values (Core.Register a))
    (cold : i .initialize = 1) (port : Core.Register a w) :
    (Core.circuit a).step i r port = (Streaming.Core.circuit a).step i r port := by
  cases port <;>
    simp [Core.circuit,Streaming.Core.circuit,Circuit.step,Core.next,Streaming.Core.next,
      Core.clearedRuntime,Streaming.Core.clearedRuntime,Core.resetting,Streaming.Core.resetting,
      Core.cold,Streaming.Core.cold,Core.either,Streaming.Core.either,Expr.eval,cold]
  done

theorem free_step_equal (i : Values Core.Input) (r : Values (Core.Register a))
    (free : r .phase = 0) (port : Core.Register a w) :
    (Core.circuit a).step i r port = (Streaming.Core.circuit a).step i r port := by
  cases port <;>
    simp [Core.circuit,Streaming.Core.circuit,Circuit.step,
      Core.next,Streaming.Core.next,Core.nextRaw,Streaming.Core.nextRaw,
      Core.nextPins,Streaming.Core.nextPins,Core.clearedRuntime,Streaming.Core.clearedRuntime,
      Core.queueCount,Streaming.Core.queueCount,
      Core.busy,Streaming.Core.busy,Core.retained,Streaming.Core.retained,
      Core.owned,Streaming.Core.owned,Core.hostOwner,Streaming.Core.hostOwner,
      Core.pushing,Streaming.Core.pushing,Core.popping,Streaming.Core.popping,
      Core.releasing,Streaming.Core.releasing,
      Core.reserving,Streaming.Core.reserving,Core.takingTX,Streaming.Core.takingTX,
      Core.loadingTX,Streaming.Core.loadingTX,
      Core.lowEnd,Core.capture,Streaming.Core.capture,Core.highEnd,Streaming.Core.highEnd,
      Core.guardedLowEnd,Core.waitSuccess,Core.waitFault,Core.waitDecrement,Core.standaloneSuccess,
      Core.capturingRX,Streaming.Core.capturingRX,Core.emittingRX,Streaming.Core.emittingRX,
      Core.normalEmit,Core.timeoutFlush,
      Core.fetching,Streaming.Core.fetching,Core.enteringCell,Streaming.Core.enteringCell,
      Core.advancing,Streaming.Core.advancing,Core.isPhase,Streaming.Core.isPhase,
      Core.both,Streaming.Core.both,Core.either,Streaming.Core.either,Expr.eval,free]
  all_goals rfl
  done

theorem free_observe_equal (i : Values Core.Input) (r : Values (Core.Register a))
    (free : r .phase = 0) (port : Core.Output w) :
    (Core.circuit a).observe i r port = (Streaming.Core.circuit a).observe i r port := by
  cases port <;>
    simp [Core.circuit,Streaming.Core.circuit,Circuit.observe,Core.output,Streaming.Core.output,
      Core.busy,Streaming.Core.busy,Core.retained,Streaming.Core.retained,
      Core.owned,Streaming.Core.owned,Core.hostOwner,Streaming.Core.hostOwner,
      Core.rejected,Streaming.Core.rejected,Core.pushing,Streaming.Core.pushing,
      Core.popping,Streaming.Core.popping,Core.releasing,Streaming.Core.releasing,
      Core.isPhase,Streaming.Core.isPhase,Core.both,Streaming.Core.both,
      Core.either,Streaming.Core.either,Expr.eval,free]
  all_goals rfl
  done

end Pinwheel.Hardware.StreamingReady.LoaderEquivalence
