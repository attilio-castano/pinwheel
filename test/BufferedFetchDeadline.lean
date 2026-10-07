import Pinwheel.Hardware.Buffered.FetchDeadline
import Pinwheel.Hardware.Buffered.Reactive
import Lean

/-! Small deadline fixtures use the actual buffered reactive expressions and
`Memory.spec`. They establish the demonstrated local obligations only, not a
complete latency-one implementation of the reactive controller. -/
open Pinwheel.Hardware
open Pinwheel.Hardware.Buffered.FetchDeadline
open Pinwheel.Hardware.Buffered.Reactive
  (circuit dispatch entryRecord entryPC entryOuter entryInner entryVirtual heldTimeout)

open Lean Elab Command in
elab "#audit_fetch_deadline" : command => do
  let env ← getEnv
  let mut declarations : Nat := 0
  let mut proofs : Nat := 0
  for (name, info) in env.constants.toList do
    if name.toString.startsWith "Pinwheel.Hardware.Buffered.FetchDeadline." then
      declarations := declarations + 1
      if info.isTheorem then proofs := proofs + 1
      let axioms ← collectAxioms name
      let unexpected := axioms.filter fun ax =>
        ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound
      unless unexpected.isEmpty do
        throwError "Unapproved fetch deadline axioms: {unexpected}"
  logInfo m!"Fetch deadline: {declarations} declarations, {proofs} theorems; standard axioms only."

#audit_fetch_deadline

private def check (ok : Bool) (label : String) : IO Unit :=
  unless ok do throw (IO.userError ("Fetch deadline failure: " ++ label))

private def singleRequest (address : BitVec 6) : Memory.Request 6 144 1 :=
  ⟨⟨false, 0, 0⟩, fun _ => address⟩

private def memory (rows : Array (BitVec 144)) : Memory.Contents 6 144 :=
  fun address => rows[address.toNat]?.getD 0

private def singleResponseCounterexample : IO Unit := do
  let contents := memory #[0, 3, 4]
  let initial : Memory.State 6 144 1 1 := ⟨contents, fun _ _ => 0⟩
  for requested in [1, 2] do
    let pending := (Memory.spec 6 144 1 1).step (singleRequest requested) initial
    let yes := (Memory.spec 6 144 1 1).observe (singleRequest 2) pending 0
    let no := (Memory.spec 6 144 1 1).observe (singleRequest 1) pending 0
    check (yes == no) "decision-edge requests cannot change registered response"
    check (!(yes == contents 2 && no == contents 1)) "single response cannot cover both rows"
    check ((if requested == 1 then no == 3 && yes != 4 else yes == 4 && no != 3))
      "each prefetch choice has a concrete failing decision"

private abbrev R := Pinwheel.Hardware.Buffered.Reactive.Register
private abbrev I := Pinwheel.Hardware.Buffered.Reactive.Input

/-- Materialize a step before evaluating another edge, so the executable fixture
does not repeatedly evaluate the preceding circuit through register closures. -/
private structure Snapshot where
  bank : Array Nat

private def snapshot (s : Values R) : Snapshot :=
  ⟨Pinwheel.Hardware.Buffered.Reactive.registers.map fun ⟨_, r⟩ => (s r).toNat⟩

private def Snapshot.values (s : Snapshot) : Values R := fun {w} r =>
  BitVec.ofNat w (s.bank[Pinwheel.Hardware.Buffered.Reactive.registerIndex r]?.getD 0)

private def inputs (command : BitVec 3 := 0) (raw : BitVec 2 := 0) : Values I
  | _, .command => command
  | _, .rawInputs => raw
  | _, .expectedGeneration => 1
  | _, _ => 0

private def word (kind levels : Nat) (terminal : Bool := false)
    (budget : Nat := 1) (waitLevel : Bool := false) : BitVec 64 :=
  BitVec.ofNat 64 (kind + levels*2^3 + 7*2^6 + terminal.toNat*2^35 +
    (budget-1)*2^47 + waitLevel.toNat*2^46)

private def endpoint (physical : Nat) : Nat := physical*2 + physical*2^11

private def branch : BitVec 56 := BitVec.ofNat 56 (2 + endpoint 2*2^6 + endpoint 1*2^30)

private def controlWord (depth outerStart outerBound innerStart innerBound : Nat)
    (outerEnd innerEnd : Bool) : BitVec 24 :=
  BitVec.ofNat 24 (depth + outerStart*4 + outerBound*256 + innerStart*2048 +
    innerBound*131072 + outerEnd.toNat*1048576 + innerEnd.toNat*2097152)

private def row (instruction : BitVec 64) (metadata : BitVec 24 := 0)
    (branches : BitVec 56 := 0) : BitVec 144 := branches ++ (metadata ++ instruction)

private def initialCore (rows : Array (BitVec 144)) : Values R
  | _, .word k => memory rows k
  | _, .valid => 1
  | _, .count => BitVec.ofNat 7 rows.size
  | _, .virtualSpan => 32
  | _, .generation => 1
  | _, _ => 0

private def sampled (s : Values R) (bits : BitVec 2) : Values R
  | _, .stage2 => bits
  | _, r => s r

private def firstStage (s : Values R) (bits : BitVec 2) : Values R
  | _, .stage1 => bits
  | _, r => s r

private def remaining (s : Values R) (n : BitVec 8) : Values R
  | _, .remaining => n
  | _, r => s r

private def selectedResponse (contents : Memory.Contents 6 144)
    (taken untaken : BitVec 6) (decision : Bool) : BitVec 144 :=
  let initial : Memory.State 6 144 2 1 := ⟨contents, fun _ _ => 0⟩
  let pending := (Memory.spec 6 144 2 1).step (dualRequest taken untaken) initial
  (Memory.spec 6 144 2 1).observe (dualRequest 0 0) pending (selectedPort decision)

private def checkedDeadline : IO Unit := do
  let rows := #[row (word 6 0 true) 0 branch, row (word 0 1), row (word 0 2)]
  let entered := snapshot (circuit.step (inputs 3) (initialCore rows))
  check (entered.values .phase == 3 && entered.values .remaining == 0) "one-cycle CHECKED entry"
  for decision in [false, true] do
    let s : Values R := sampled entered.values (if decision then 1 else 0)
    let required := entryRecord.eval inputs s
    let expectedPC : BitVec 7 := if decision then 2 else 1
    check (dispatch.eval inputs s == 1) "CHECKED terminal dispatch"
    check (entryPC.eval inputs s == expectedPC) "terminal capture forwards branch choice"
    check (selectedResponse (memory rows) 2 1 decision == required)
      "both prefetch responses cover terminal branch row"
    let stepped : Values R := circuit.step inputs s
    check (stepped .pc == expectedPC && stepped .levels == expectedPC.setWidth 3)
      "selected successor takes effect on terminal edge"
    check (stepped .scratch == (if decision then 1 else 0)) "terminal capture retained"

private def waitDeadline : IO Unit := do
  let rows := #[row (word 5 0 (budget := 3) (waitLevel := true)), row (word 0 3)]
  let entered := snapshot (circuit.step (inputs 3) (initialCore rows))
  check (entered.values .phase == 2 && entered.values .remaining == 2) "WAIT entry full budget"
  let pending : Memory.State 6 144 1 1 :=
    (Memory.spec 6 144 1 1).step (singleRequest 1) ⟨memory rows, fun _ _ => 0⟩
  for budget in ([2, 1, 0] : List (BitVec 8)) do
    let ready : Values R := sampled (remaining entered.values budget) 1
    check (dispatch.eval inputs ready == 1 && heldTimeout.eval inputs ready == 0)
      "WAIT unpredictable ready edge, including final budget edge"
    check (pending.observe (singleRequest 0) 0 == entryRecord.eval inputs ready)
      "known WAIT successor can be prefetched before readiness"
    let stepped : Values R := circuit.step inputs ready
    check (stepped .pc == 1 && stepped .levels == 3) "WAIT successor takes effect on ready edge"
  let blocked : Values R := sampled entered.values 0
  let held : Values R := circuit.step inputs blocked
  check (dispatch.eval inputs blocked == 0 && held .phase == 2 && held .remaining == 1)
    "blocked WAIT does not consume a successor"
  let exhausted : Values R := sampled (remaining entered.values 0) 0
  check (dispatch.eval inputs exhausted == 0 &&
      (circuit.step inputs exhausted) .phase == 6)
    "exhausted blocked WAIT times out without dispatch"

private def loopState (rows : Array (BitVec 144)) (outer inner : BitVec 3) : Values R
  | _, .phase => 1
  | _, .pc => 2
  | _, .virtualPC => 5
  | _, .currentControl => (controlWord 2 0 1 1 1 true true).setWidth 22
  | _, .outer => outer
  | _, .inner => inner
  | _, r => initialCore rows r

private def countedCandidates : IO Unit := do
  let rows := #[row (word 0 0) (controlWord 1 0 1 0 0 false false),
    row (word 0 1) (controlWord 2 0 1 1 1 false false),
    row (word 0 2) (controlWord 2 0 1 1 1 true true), row (word 0 3)]
  let cases : List (BitVec 3 × BitVec 3 × BitVec 7 × BitVec 3 × BitVec 3) :=
    [(0, 0, 1, 0, 1), (0, 1, 0, 1, 0), (1, 1, 3, 0, 0)]
  for (outer, inner, address, nextOuter, nextInner) in cases do
    let s : Values R := loopState rows outer inner
    let actual := entryPC.eval inputs s
    check (actual == address && entryOuter.eval inputs s == nextOuter &&
      entryInner.eval inputs s == nextInner)
      "inner rollover, outer rollover and nested exit candidate addresses"
    check (entryVirtual.eval inputs s == 6) "virtual position increments across physical reuse"
    let candidate := actual.setWidth 6
    check (selectedResponse (memory rows) candidate candidate false == entryRecord.eval inputs s)
      "latency-one prefetch matches counted physical row"

/-- Finite actual-step evidence for the sampler lookahead opportunity. The
predicted post-edge state replaces this edge's raw sample by zero: this changes
stage1 but does not change the next edge's dispatch/endpoint/address in these
fixtures. Prediction evaluates the existing transition; it is not a new fetch
controller, nor a claim that its combinational path meets timing. -/
private def samplerLookahead : IO Unit := do
  let checked := row (word 6 0 true) 0 branch
  let wait := row (word 5 0 (budget := 3) (waitLevel := true))
  let qualify := row (word 7 0 + BitVec.ofNat 64 (2^41 + 2^43))
  for first in [checked, wait, qualify] do
    let rows := #[first, row (word 0 1), row (word 0 2)]
    for oldStage1 in ([0, 1] : List (BitVec 2)) do
      let before : Values R := firstStage (initialCore rows) oldStage1
      let predicted := snapshot (circuit.step (inputs 3 0) before)
      let predictedDispatch := dispatch.eval inputs predicted.values
      let predictedEndpoint := Pinwheel.Hardware.Buffered.Reactive.endpoint.eval inputs predicted.values
      let predictedPC := entryPC.eval inputs predicted.values
      let fetch : Memory.State 6 144 1 1 := (Memory.spec 6 144 1 1).step
        (singleRequest (predictedPC.setWidth 6)) ⟨memory rows, fun _ _ => 0⟩
      for rawNow in ([0, 3] : List (BitVec 2)) do
        let actual := snapshot (circuit.step (inputs 3 rawNow) before)
        check (actual.values .stage1 == rawNow && actual.values .stage2 == oldStage1)
          "raw sample affects stage1; next synchronized sample is old stage1"
        for rawNext in ([0, 3] : List (BitVec 2)) do
          let following : Values I := inputs 0 rawNext
          check (dispatch.eval following actual.values == predictedDispatch &&
              Pinwheel.Hardware.Buffered.Reactive.endpoint.eval following actual.values == predictedEndpoint &&
              entryPC.eval following actual.values == predictedPC)
            "CHECKED/WAIT/QUALIFY next deadline ignores new raw samples"
          if predictedDispatch == 1 then
            check (fetch.observe (singleRequest 0) 0 == entryRecord.eval following actual.values)
              "one-port predicted row covers the next dispatch in this fixture"

def main : IO Unit := do
  singleResponseCounterexample
  checkedDeadline
  waitDeadline
  countedCandidates
  samplerLookahead
  IO.println "Fetch deadline: both one-port counterexamples, two one-cycle CHECKED branches, three WAIT readiness deadlines, blocked/timeout WAIT, three counted loop candidates and 24 sampler lookahead cases passed."
