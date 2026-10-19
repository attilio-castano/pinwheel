import Pinwheel.Hardware.Buffered.SpiStartRefinement
import Pinwheel.Hardware.Buffered.SpiSimulation
import Pinwheel.Hardware.Buffered.MemoEval

/-! Independent finite source/circuit regression checks. This executable evaluates the
existing source interpreter and actual packed Reactive equations separately.
It is finite diagnostic evidence, not a universal refinement proof. -/
namespace Pinwheel.Test.BufferedSpiRefinement
open Pinwheel.Hardware Pinwheel.Program Pinwheel.Engine.Reactive
open Hardware.Buffered

/-- The START theorem constructs its source from actual START operands. There is
no caller-supplied source/circuit relation or successful-transfer premise. -/
example (c : SpiSource.Config) (i : Values Reactive.Input) (r : Values Reactive.Register)
    (image : ∀ k, r (.word k) = SpiSource.fullWords c k)
    (geometry : SpiGeometry.Geometry c r) (starting : Reactive.starting.eval i r = 1) :
    SpiRefinement.Related c (i .txData) (Reactive.circuit.step i r)
      (Program.Buffered.start (BufferedSPI.program c) SpiRefinement.capacity
        (SpiStart.seed c r i)) :=
  SpiRefinement.start_related c i r image geometry starting

/-- The initialized theorem derives the image and SRAM/circuit relation from
actual accepted source uploads. Arbitrary raw histories and prefix lengths are
quantified directly, including immediate faults and retained terminal prefixes.
-/
example (c : SpiSource.Config) (s : SramState.State)
    (cold : Values Reactive.Input) (coldInit : cold .initialize = 1)
    (loading : List (Values Reactive.Input))
    (source : SpiSource.SourceHistory c (s.step cold) loading)
    (valid : (SramLoading.run (s.step cold) SramLoading.Ledger.initial loading).1.registers
      (.core .valid) = 1)
    (start : Values Reactive.Input)
    (starting : Reactive.starting.eval start
      (SramExecution.core (SramLoading.run (s.step cold) SramLoading.Ledger.initial loading).1.registers) = 1)
    (incoming : Nat → BitVec 2) (edges : Nat) :
    let after := SramLoading.run (s.step cold) SramLoading.Ledger.initial loading
    SpiRefinement.RelatedSram c (start .txData)
      ((after.1.step start).run (SpiStart.clocks incoming edges))
      (Program.Buffered.run (BufferedSPI.program c) SpiRefinement.capacity
        (Program.Buffered.start (BufferedSPI.program c) SpiRefinement.capacity
          (SpiStart.seed c (SramExecution.core after.1.registers) start)) incoming edges) :=
  SpiRefinement.initialized_run c s cold coldInit loading source valid start starting incoming edges

private def inputs (command : BitVec 3 := 0) (raw : BitVec 2 := 0)
    (payload : BitVec 32 := 0) (txLength rxCapacity : Nat := 0) : Values Reactive.Input
  | _, .command => command
  | _, .rawInputs => raw
  | _, .txData => payload
  | _, .txLength => BitVec.ofNat 6 txLength
  | _, .rxCapacity => BitVec.ofNat 6 rxCapacity
  | _, .expectedGeneration => 1
  | _, _ => 0

private structure Snapshot where
  data : Array Nat

private def snapshot (s : Values Reactive.Register) : Snapshot :=
  ⟨Reactive.registers.map fun ⟨_, r⟩ => (s r).toNat⟩

private def Snapshot.values (s : Snapshot) : Values Reactive.Register := fun {w} r =>
  BitVec.ofNat w (s.data[Reactive.registerIndex r]?.getD 0)

private def expressions : Array (Sigma (Expr Reactive.Input Reactive.Register)) :=
  Reactive.registers.map fun ⟨w, r⟩ => ⟨w, Reactive.next r⟩

private def tick (s : Snapshot) (i : Values Reactive.Input) : Snapshot :=
  ⟨MemoEval.evalMany i s.values expressions⟩

private def initialCircuit (c : BufferedSPI.Config) : Values Reactive.Register
  | _, .word k => SpiSource.fullWords c k
  | _, .valid => 1
  | _, .count => 4
  | _, .virtualSpan => BitVec.ofNat 11 (16 * (c.bytesMinusOne.val + 1) + 2)
  | _, .idleLevels => 4
  | _, .idleEnabled => 7
  | _, .levels => 4
  | _, .enabled => 7
  | _, .generation => 1
  | _, .stage1 => 2
  | _, .stage2 => 1
  | _, _ => 0

private def txBits (payload : BitVec 32) (length : Nat) : List Bool :=
  (List.range length).map payload.getLsbD

private def sourceSeed (c : BufferedSPI.Config) (payload : BitVec 32)
    (txLength rxCapacity : Nat) (aligned : Bool := true) : Program.Buffered.State :=
  let id : Transfer.Identity := ⟨1, 1⟩
  let request : Transfer.Request := ⟨id, 1, txBits payload txLength, rxCapacity⟩
  let buffers : Transfer.State := ⟨1, 2, .running ⟨request, 0, []⟩⟩
  {Program.Buffered.initial (BufferedSPI.program c) buffers id with
    samplerFirst := if aligned then 3 else 2
    samplerSecond := if aligned then 2 else 1}

private def capacity : Transfer.Capacity := ⟨32, 32⟩

private def rxWord (bits : List Bool) : BitVec 32 :=
  BitVec.ofNat 32 ((List.range 32).foldl (fun n k =>
    if bits[k]?.getD false then n + 2^k else n) 0)

private def raw (n : Nat) : Inputs := BitVec.ofNat 2
  ((if n % 3 = 0 then 1 else 0) + (if n % 5 = 0 then 2 else 0))

private def check (ok : Bool) (label : String) : IO Unit :=
  unless ok do throw (IO.userError label)

private def execution (s : Program.Buffered.State) : IO Transfer.Execution :=
  match s.buffers.slot with
  | .running e => pure e
  | .completed result => pure result.execution
  | _ => throw (IO.userError "source left the owned execution/completion slot")

private def compare (tag : String) (edge : Nat) (c : BufferedSPI.Config)
    (payload : BitVec 32) (txLength rxCapacity : Nat)
    (source : Program.Buffered.State) (circuit : Snapshot) : IO Unit := do
  let e ← execution source
  let actual : Values Reactive.Register := circuit.values
  let label := fun field => s!"{tag}: edge {edge}: {field}"
  check (actual .levels == source.core.pins.levels) (label "pin levels")
  check (actual .enabled == source.core.pins.enabled) (label "pin enables")
  check ((actual .txConsumed).toNat == e.txConsumed) (label "TX consumed")
  check (actual .txData == payload >>> e.txConsumed) (label "full unmasked TX suffix")
  check ((actual .txLength).toNat == txLength) (label "TX length")
  check ((actual .rxLength).toNat == e.rx.length) (label "RX prefix length")
  check (actual .rxData == rxWord e.rx) (label "RX packed prefix")
  check ((actual .rxCapacity).toNat == rxCapacity) (label "RX reservation")
  check (actual .scratch == 0 && source.core.samples == Vector.replicate 16 false)
    (label "canonical SPI scratch")
  check (actual .generation == 1 && actual .transfer == 1) (label "admitted identity")
  match source.core.control with
  | .active pc remaining =>
    check (actual .phase == 1 && actual .retained == 0) (label "active phase")
    check ((actual .virtualPC).toNat == pc.val) (label "virtual PC")
    check ((actual .remaining).toNat == remaining.val) (label "countdown")
    let inLoop := pc.val < 16 * (c.bytesMinusOne.val + 1)
    check ((actual .pc).toNat == if inLoop then pc.val % 2 else 2) (label "physical row")
    check ((actual .inner).toNat == if inLoop then (pc.val / 2) % 8 else 0)
      (label "inner rollover")
    check ((actual .outer).toNat == if inLoop then pc.val / 16 else 0)
      (label "outer rollover")
    check (actual .stage1 == source.samplerFirst && actual .stage2 == source.samplerSecond)
      (label "active sampler alignment")
  | .stopped reason =>
    let expected : BitVec 3 := match reason with
      | .completed => 5 | .fault => 7 | .timeout => 6 | .ready => 0
    check (actual .phase == expected && actual .retained == 1) (label "retained terminal phase")
    check (actual .pc == 0 && actual .virtualPC == 0 && actual .remaining == 0 &&
      actual .outer == 0 && actual .inner == 0 && actual .currentControl == 0)
      (label "terminal coordinate canonicalization")
  | _ => throw (IO.userError (label "SPI entered a reactive-only source phase"))

private def runCase (tag : String) (c : BufferedSPI.Config) (payload : BitVec 32)
    (txLength rxCapacity : Nat) (outcome : Transfer.Outcome)
    (expectedTx expectedRx : Nat) : IO Nat := do
  let p := BufferedSPI.program c
  let mut source := Program.Buffered.start p capacity (sourceSeed c payload txLength rxCapacity)
  let mut circuit := tick (snapshot (initialCircuit c)) (inputs 3 3 payload txLength rxCapacity)
  compare tag 0 c payload txLength rxCapacity source circuit
  let edges := (16 * (c.bytesMinusOne.val + 1) + 1) * (c.halfCyclesMinusOne.val + 1)
  for n in [:edges] do
    source := Program.Buffered.advance p capacity source (raw n)
    circuit := tick circuit (inputs 0 (raw n))
    compare tag (n + 1) c payload txLength rxCapacity source circuit
  check (!busy source.core) s!"{tag}: did not terminate within the exact source horizon"
  match source.buffers.slot with
  | .completed result =>
    check (result.outcome == outcome && result.execution.txConsumed == expectedTx &&
      result.execution.rx.length == expectedRx)
      s!"{tag}: fixture did not exercise its intended outcome/TX/RX boundary"
  | _ => throw (IO.userError s!"{tag}: terminal source did not retain a completion")
  let frozen := source.samplerSecond
  let afterStop : Inputs := ~~~frozen
  for extra in [:3] do
    source := Program.Buffered.advance p capacity source afterStop
    circuit := tick circuit (inputs 0 afterStop)
    compare tag (edges + extra + 1) c payload txLength rxCapacity source circuit
  check (source.samplerSecond == frozen && circuit.values .stage2 != frozen)
    s!"{tag}: stopped sampler abstraction has no distinguishing witness"
  IO.println s!"{tag}: {edges + 4} independent source/circuit prefixes passed"
  return edges + 4

private def put (s : Snapshot) (r : Reactive.Register w) (value : BitVec w) : Snapshot :=
  ⟨s.data.set! (Reactive.registerIndex r) value.toNat⟩

private def rejectMutation (label : String) (c : BufferedSPI.Config)
    (payload : BitVec 32) (txLength rxCapacity edge : Nat)
    (source : Program.Buffered.State) (mutated : Snapshot) : IO Unit := do
  let accepted ← try
    compare label edge c payload txLength rxCapacity source mutated
    pure true
  catch _ => pure false
  check (!accepted) s!"{label}: independently changed circuit state was accepted"

private def controls : IO Unit := do
  let c : BufferedSPI.Config := ⟨1, 2, by decide⟩
  let p := BufferedSPI.program c
  let payload : BitVec 32 := 0xd639ac71
  let seed := snapshot (initialCircuit c)
  let start : Values Reactive.Input := inputs 3 3 payload 32 32
  let mut circuit := tick seed start
  let ordinary := snapshot (Reactive.circuit.step start seed.values)
  check (circuit.data == ordinary.data) "ordinary actual START differs from MemoEval"
  let mut source := Program.Buffered.start p capacity (sourceSeed c payload 32 32)
  for n in [:48] do
    let before := circuit
    let i : Values Reactive.Input := inputs 0 (raw n)
    circuit := tick circuit i
    source := Program.Buffered.advance p capacity source (raw n)
    if n = 2 then
      let ordinary := snapshot (Reactive.circuit.step i before.values)
      check (circuit.data == ordinary.data) "ordinary actual first KEEP differs from MemoEval"
      check ((circuit.values .rxData).getLsbD 0 != (raw n).getLsbD 0)
        "sampler fixture does not distinguish preedge stage2 from current raw input"
      rejectMutation "current-raw-rx-mutation" c payload 32 32 (n + 1) source
        (put circuit .rxData 0)
      rejectMutation "rx-append-index-mutation" c payload 32 32 (n + 1) source
        (put circuit .rxData 2)
  check (circuit.values .outer == 1 && circuit.values .inner == 0 &&
    circuit.values .pc == 0 && circuit.values .virtualPC == 16)
    "byte rollover fixture did not reach its intended boundary"
  rejectMutation "outer-rollover-mutation" c payload 32 32 48 source (put circuit .outer 0)
  let short := tick (snapshot (initialCircuit c)) (inputs 3 3 2 1 32)
  check (short.values .txData == 1 && rxWord ((txBits 2 1).drop 1) == 0)
    "unused high TX bits did not distinguish the full hardware shift register"
  IO.println "Controls: 2 ordinary actual-state parity boundaries, 3 rejected independent state mutations, and a short-TX high-bit counterexample passed"

def main : IO Unit := do
  controls
  let small : BufferedSPI.Config := ⟨0, 2, by decide⟩
  let default := BufferedSPI.Config.default
  let mut total := 0
  total := total + (← runCase "zero-tx" small 0x80000000 0 8 .fault 0 0)
  total := total + (← runCase "unused-high-tx-bits" small 2 1 8 .fault 1 1)
  total := total + (← runCase "rx-zero" small 0x5a 8 0 .fault 1 0)
  total := total + (← runCase "rx-one-short" default 0xd639ac71 32 31 .fault 32 31)
  total := total + (← runCase "last-tx-bit" default 0xd639ac71 31 32 .fault 31 31)
  for bytes in List.finRange 4 do
    let c : BufferedSPI.Config := ⟨bytes, 2, by decide⟩
    total := total + (← runCase s!"byte-rollover-{bytes.val+1}" c 0xd639ac71 32 32
      .complete (8 * (bytes.val + 1)) (8 * (bytes.val + 1)))
  let max : BufferedSPI.Config := ⟨3, 255, by decide⟩
  total := total + (← runCase "max-duration" max 0xd639ac71 32 32 .complete 32 32)
  let naive := Program.Buffered.start (BufferedSPI.program small) capacity
    (sourceSeed small 1 8 8 false)
  let actual := tick (snapshot (initialCircuit small)) (inputs 3 3 1 8 8)
  check (naive.samplerSecond != actual.values .stage2)
    "naive pre-START sampler relation did not fail"
  IO.println s!"SPI source/circuit semantic probes: 10 cases, {total} compared prefixes; START sampler and stopped sampler counterexamples witnessed"
end Pinwheel.Test.BufferedSpiRefinement

def main : IO Unit := Pinwheel.Test.BufferedSpiRefinement.main
