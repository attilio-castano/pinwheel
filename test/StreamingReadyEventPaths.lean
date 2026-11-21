import Pinwheel.Program.StreamingReadyReceiveImages
import Pinwheel.Program.StreamingReadySegmentExecution

open Pinwheel.Program.StreamingReadySegments
open Pinwheel.Program.StreamingReadyReceiveImages

example : can.outcomes.map PathEnd.maxCoreClocks = [none] := by decide +kernel
example : ps2.outcomes.map PathEnd.externalPolls = [11] := by decide +kernel

example : ∀ q : Fin 125, ∀ pin : Fin 2, (check (uartRows ⟨q, pin⟩) 0).isSome = true := by
  decide +kernel

private def startBit : Pinwheel.Program.StreamingReady.Guard := {mask := 1}

example : Execution.pollWindow startBit (List.replicate 300 1 ++ [0]) = some (some 0) := by decide +kernel
example : Execution.pollWindow startBit (List.replicate 300 1) = none := by decide +kernel
example : Execution.pollWindow startBit [1, 0, 0] = none := by decide +kernel
example : check (ps2Rows.set 0 (.count 0)) 0 = none := by decide +kernel
