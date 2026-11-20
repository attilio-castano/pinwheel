import Pinwheel.Program.StreamingReadyRegisterReadVariants
import Pinwheel.Program.StreamingReadySegmentReadback
import Pinwheel.Program.StreamingReadySegmentSplit

open Pinwheel
open Program.StreamingReadySegments Program.StreamingReadySegments.Execution
open Program.StreamingReadyRegisterReadVariants

private def request : I2C.RegisterRead.Request := ⟨0x53, 0xA6⟩

private def goodTarget : I2C.RegisterReadPeer.Target := {payload := 0x96}

private def targets : List I2C.RegisterReadPeer.Target :=
  [goodTarget, {goodTarget with nack := some 0}, {goodTarget with nack := some 1},
    {goodTarget with nack := some 2}]

private def serviceCell (bit : Bool) : Observation :=
  .cell 0 [BitVec.ofNat 2 (1 + 2 * bit.toNat)]

private def peerService (target : I2C.RegisterReadPeer.Target) : List Observation :=
  let sampled := (expectedRegisterRead request target).map serviceCell
  let start := Observation.wait [3]
  let stop := Observation.wait [1]
  if sampled.length ≤ 18 then [start] ++ sampled ++ [stop]
  else [start] ++ sampled.take 18 ++ [start] ++ sampled.drop 18 ++ [stop]

private def fixture (rows : List Row) (target : I2C.RegisterReadPeer.Target) : Option Result :=
  run rows 36 (registerReadTX request) (peerService target)

private def nominalRows := registerReadRows .standard
private def refactoredRows := splitRows .standard
private def invertedRows := invertedAckRows .standard

private def matchesPeer (rows : List Row) (target : I2C.RegisterReadPeer.Target) : Bool :=
  match fixture rows target with
  | some result =>
    match result.terminal with
    | .planned endpoint =>
      endpoint.exit == (if target.nack.isSome then .discard else .complete) &&
        endpoint.tx == target.stopAfter && endpoint.rx == target.stopAfter &&
        result.rxBits == expectedRegisterRead request target &&
        projectRegisterRead request result.rxBits == some target.outcome &&
        result.txBits == (registerReadTX request).take target.stopAfter &&
        result.remainingObservations.isEmpty
    | .timeout .. => false
  | none => false

private def publicEvents (result : Result) : List Event :=
  (result.events.foldl (fun kept event =>
    match event, kept with
    | .fetch _, _ => kept
    | .drive pins, .drive last :: _ => if pins == last then kept else event :: kept
    | _, _ => event :: kept) []).reverse

private def timedOut (rows : List Row) : Option Result :=
  let captured := ((expectedRegisterRead request goodTarget).take 13).map serviceCell
  let polls := (Program.StreamingReady.I2cProfile.standard.budgetMinusOne.val + 1)
  run rows 36 (registerReadTX request) ([.wait [3]] ++ captured ++ [.cell 0 (List.replicate polls 0)])

set_option maxRecDepth 8192 in
example : targets.all (fun target => matchesPeer nominalRows target && matchesPeer refactoredRows target) = true :=
  by decide +kernel

/- Repartitioning preserves cell events and branch decisions. An inserted
fetch can restate the same LOW drive. Path clock bounds are checked separately. -/
set_option maxRecDepth 8192 in
example : targets.all (fun target =>
    (fixture nominalRows target).map publicEvents == (fixture refactoredRows target).map publicEvents) = true :=
  by decide +kernel

set_option maxRecDepth 8192 in
example :
    (timedOut nominalRows).map (fun result => (result.terminal, result.txBits.length, result.rxBits.length)) =
      some (.timeout 6 4, 14, 13) ∧
    (timedOut refactoredRows).map (fun result => (result.terminal, result.txBits.length, result.rxBits.length)) =
      some (.timeout 8 4, 14, 13) ∧
    (timedOut nominalRows).map publicEvents = (timedOut refactoredRows).map publicEvents := by
  decide +kernel

set_option maxRecDepth 8192 in
example : matchesPeer invertedRows goodTarget = false := by decide +kernel

/- An ACK produces an early STOP in the inverted image when given a STOP
poll. The public result cannot decode as a write-address NACK. -/
set_option maxRecDepth 8192 in
example :
    let firstByte := ((expectedRegisterRead request goodTarget).take 9).map serviceCell
    let ran := run invertedRows 36 (registerReadTX request) ([.wait [3]] ++ firstByte ++ [.wait [1]])
    ran.map (fun result => (result.branches, projectRegisterRead request result.rxBits)) =
      some ([(false, true)], none) := by
  decide +kernel
