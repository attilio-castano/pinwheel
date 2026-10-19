import Pinwheel.Hardware.Buffered.GenericStart

/-! Distinguishing START-edge regressions evaluate the existing source start
and actual circuit independently. Kernel checks cover sampler age, preserved
pins, ignored terminal operands, and consume-before-overflow diagnostics. -/
namespace Pinwheel.Test.GenericStartBoundary
open Pinwheel.Hardware Pinwheel.Program Pinwheel.Engine.Reactive
open Pinwheel.Hardware.Buffered

private def program (instruction : Program.Buffered.Instruction) : Program.Buffered.Program :=
  ⟨.emit instruction, ⟨0, 0⟩, by simp [Counted.Schedule.span],
    by simp [Counted.Schedule.nodes], by simp [Counted.Schedule.nesting]⟩

private def inputs (rxCapacity : BitVec 6 := 1) : Values Reactive.Input
  | _, .command => 3
  | _, .expectedGeneration => 1
  | _, .rawInputs => 3
  | _, .txData => 2
  | _, .txLength => 1
  | _, .rxCapacity => rxCapacity
  | _, _ => 0

private def registers (instruction : Program.Buffered.Instruction) : Values Reactive.Register
  | _, .word k => if k == 0 then 0#56 ++ 0#24 ++ GenericEncoding.encode instruction else 0
  | _, .valid => 1
  | _, .count => 1
  | _, .virtualSpan => 1
  | _, .generation => 1
  | _, .levels => 5
  | _, .enabled => 3
  | _, .scratch => 65535
  | _, .stage1 => 0
  | _, .stage2 => 2
  | _, _ => 0

private def captureAppend : Program.Buffered.Instruction :=
  {operation := .drive ⟨⟨1, 7⟩, 0, some ⟨1, 5⟩⟩, append := some 1}

private def keep : Program.Buffered.Instruction :=
  {operation := .keep 7 7 ⟨⟨0, 0⟩, 0, none⟩}

private def terminal : Program.Buffered.Instruction := {operation := .halt, append := some 1}

private def shiftAppend : Program.Buffered.Instruction :=
  {operation := .shift 0 false false ⟨⟨0, 7⟩, 0, none⟩, append := some 1}

private def actual (instruction : Program.Buffered.Instruction) (rxCapacity : BitVec 6 := 1) :
    Values Reactive.Register :=
  Reactive.circuit.step (inputs rxCapacity) (registers instruction)

private def source (instruction : Program.Buffered.Instruction) (rxCapacity : BitVec 6 := 1) :
    Program.Buffered.State :=
  GenericStart.started (program instruction) (registers instruction) (inputs rxCapacity)

private def diagnostic (s : Program.Buffered.State) : Option (Transfer.Execution × Option Transfer.Outcome) :=
  match s.buffers.slot with
  | .running e => some (e, none)
  | .completed c => some (c.execution, some c.outcome)
  | _ => none

private def rx (s : Program.Buffered.State) : List Bool :=
  ((diagnostic s).map (fun pair => pair.1.rx)).getD []

private def consumed (s : Program.Buffered.State) : Nat :=
  ((diagnostic s).map (fun pair => pair.1.txConsumed)).getD 0

private def outcome (s : Program.Buffered.State) : Option Transfer.Outcome :=
  (diagnostic s).bind Prod.snd

private def wrongSampler : Program.Buffered.State :=
  let r : Values Reactive.Register := registers captureAppend
  let i : Values Reactive.Input := inputs 1
  let p := program captureAppend
  GenericStart.resample
    (Program.Buffered.start p Refinement.capacity
      {GenericStart.seed p r i with samplerSecond := r .stage1})
    (i .rawInputs) (r .stage1)

private def wrongIdlePins : Program.Buffered.State :=
  let r : Values Reactive.Register := registers keep
  let i : Values Reactive.Input := inputs 1
  let p := program keep
  let seed := GenericStart.seed p r i
  GenericStart.resample
    (Program.Buffered.start p Refinement.capacity {seed with core := {seed.core with pins := p.idle}})
    (i .rawInputs) (r .stage1)

private def captureBoundary : Bool :=
  Reactive.starting.eval (inputs 1) (registers captureAppend) == 1 &&
  (actual captureAppend) .phase == 1 &&
  (actual captureAppend) .scratch == 32 &&
  (actual captureAppend) .rxLength == 1 &&
  (actual captureAppend) .rxData == 1 &&
  (source captureAppend).core.samples[5] && rx (source captureAppend) == [true] &&
  (source captureAppend).samplerFirst == 3 && (source captureAppend).samplerSecond == 0 &&
  (actual captureAppend) .stage1 == 3 && (actual captureAppend) .stage2 == 0

private def captureMutation : Bool :=
  !(wrongSampler.core.samples[5]) && rx wrongSampler == [false] &&
  (source captureAppend).core.samples[5] != wrongSampler.core.samples[5] &&
  rx (source captureAppend) != rx wrongSampler

private def keepBoundary : Bool :=
  Reactive.starting.eval (inputs 1) (registers keep) == 1 &&
  (actual keep) .phase == 1 &&
  (actual keep) .levels == 5 && (actual keep) .enabled == 3 &&
  (source keep).core.pins == (⟨5, 3⟩ : Pins)

private def keepMutation : Bool :=
  wrongIdlePins.core.pins == (⟨0, 0⟩ : Pins) &&
  (source keep).core.pins != wrongIdlePins.core.pins

private def terminalBoundary : Bool :=
  Reactive.starting.eval (inputs 1) (registers terminal) == 1 &&
  (actual terminal) .phase == 5 && (actual terminal) .retained == 1 &&
  (actual terminal) .rxLength == 0 && (actual terminal) .rxData == 0 &&
  rx (source terminal) == [] && outcome (source terminal) == some .complete &&
  !(GenericEffects.result terminal (GenericStart.execution (registers terminal) (inputs 1))
    ((registers terminal) .stage2)).receive

private def unusedSampleMutation : Bool :=
  (Reactive.sampled.eval (inputs 1) (registers terminal)).getLsbD 0 !=
    (GenericEffects.result terminal (GenericStart.execution (registers terminal) (inputs 1))
      ((registers terminal) .stage2)).sample

private def overflowBoundary : Bool :=
  Reactive.starting.eval (inputs 0) (registers shiftAppend) == 1 &&
  (actual shiftAppend 0) .phase == 7 && (actual shiftAppend 0) .retained == 1 &&
  (actual shiftAppend 0) .txConsumed == 1 && (actual shiftAppend 0) .txData == 1 &&
  (actual shiftAppend 0) .rxLength == 0 && consumed (source shiftAppend 0) == 1 &&
  rx (source shiftAppend 0) == [] && outcome (source shiftAppend 0) == some .fault

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
example : captureBoundary = true := by decide +kernel
example : captureMutation = true := by decide +kernel
example : keepBoundary = true := by decide +kernel
example : keepMutation = true := by decide +kernel
example : terminalBoundary = true := by decide +kernel
example : unusedSampleMutation = true := by decide +kernel
example : overflowBoundary = true := by decide +kernel

private def check : IO Unit := do
  let checks := [captureBoundary, keepBoundary, terminalBoundary, overflowBoundary]
  let mutations := [captureMutation, keepMutation, unusedSampleMutation]
  unless checks.all id && mutations.all id do
    throw (IO.userError "generic START boundary regression")
  IO.println "Generic START boundaries: 4 independent source/circuit controls, 3 rejected semantic mutations; passed"

end Pinwheel.Test.GenericStartBoundary

def main : IO Unit := Pinwheel.Test.GenericStartBoundary.check
