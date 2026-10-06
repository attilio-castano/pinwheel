import Pinwheel.Hardware.Buffered.CountedProofs
import Pinwheel.Engine.Counted
import Lean

open Pinwheel.Hardware Pinwheel.Hardware.Buffered.Counted
open Pinwheel.Engine.Reactive.Counted (Schedule)

open Lean Elab Command in
elab "#audit_buffered_counted" : command => do
  let env ← getEnv
  let mut count : Nat := 0
  let mut proofs : Nat := 0
  for (name, info) in env.constants.toList do
    if name.toString.startsWith "Pinwheel.Hardware.Buffered.Counted." then
      count := count + 1
      if info.isTheorem then proofs := proofs + 1
      let axioms ← collectAxioms name
      let unexpected := axioms.filter fun ax =>
        ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound
      unless unexpected.isEmpty do
        throwError "Unapproved buffered circuit axioms: {unexpected}"
  logInfo m!"Buffered counted circuit: {count} declarations, {proofs} local theorems; standard axioms only."

#audit_buffered_counted

private structure Command where
  coldInit : Bool := false
  command : BitVec 3 := 0
  address : BitVec 6 := 0
  word : BitVec 32 := 0
  control : BitVec 24 := 0
  virtualSpan : BitVec 11 := 1
  count : BitVec 7 := 0
  idleLevels : BitVec 3 := 0
  idleEnabled : BitVec 3 := 0
  txData : BitVec 32 := 0
  txLength : BitVec 6 := 0
  rxCapacity : BitVec 6 := 0
  expectedGeneration : BitVec 16 := 0
  expectedTransfer : BitVec 16 := 0
  readIndex : BitVec 5 := 0
  rawInputs : BitVec 2 := 0

private def Command.values (c : Command) : Values Input
  | _,.initialize => BitVec.ofBool c.coldInit | _,.command => c.command
  | _,.address => c.address | _,.word => c.word | _,.control => c.control
  | _,.virtualSpan => c.virtualSpan | _,.count => c.count
  | _,.idleLevels => c.idleLevels | _,.idleEnabled => c.idleEnabled
  | _,.txData => c.txData | _,.txLength => c.txLength | _,.rxCapacity => c.rxCapacity
  | _,.expectedGeneration => c.expectedGeneration | _,.expectedTransfer => c.expectedTransfer
  | _,.readIndex => c.readIndex | _,.rawInputs => c.rawInputs

private structure Snapshot where
  bank : Array Nat

private def snapshot (s : Values Register) : Snapshot :=
  ⟨registers.map fun ⟨_,r⟩ => (s r).toNat⟩

private def Snapshot.values (s : Snapshot) : Values Register := fun {w} r =>
  BitVec.ofNat w (s.bank[registerIndex r]?.getD 0)

private def tick (s : Snapshot) (c : Command := {}) : Snapshot :=
  snapshot (circuit.step c.values s.values)

private def seeded (generation transfer : Nat := 1) (count : Nat := 1)
    (word : BitVec 56 := 3) : Values Register
  | _,.word _ => word
  | _,.generation => BitVec.ofNat 16 generation
  | _,.transfer => BitVec.ofNat 16 transfer
  | _,.valid => 1
  | _,.count => BitVec.ofNat 7 count
  | _,.virtualSpan => 1
  | _,.idleLevels => 4
  | _,.idleEnabled => 7
  | _,_ => 0

private def check (ok : Bool) (label : String) : IO Unit :=
  unless ok do throw (IO.userError ("Buffered counted hardware failure: " ++ label))

private def out (s : Snapshot) (o : Output w) (c : Command := {}) : Nat :=
  (circuit.observe c.values s.values o).toNat

private def expect (s : Snapshot) (o : Output w) (n : Nat) (label : String)
    (c : Command := {}) : IO Unit := check (out s o c == n) label

private def controlWord (depth outerStart outerBound innerStart innerBound : Nat)
    (outerEnd innerEnd : Bool) : BitVec 24 :=
  BitVec.ofNat 24 (depth + outerStart*4 + outerBound*256 + innerStart*2048 +
    innerBound*131072 + outerEnd.toNat*1048576 + innerEnd.toNat*2097152)

private def row (word : BitVec 32) (metadata : BitVec 24 := 0) : BitVec 56 := metadata ++ word

private def program (rows : Array (BitVec 56)) (span : Nat) : Snapshot :=
  snapshot (fun {w} r => BitVec.ofNat w
    (if registerIndex r < 64 then (rows[registerIndex r]?.getD 0).toNat
      else if registerIndex r == 67 then rows.size
      else if registerIndex r == 76 then span
      else ((seeded 1 0 1 3) r).toNat))

private def checkLocate (s : Snapshot)
    (code : Pinwheel.Engine.Reactive.Counted.Schedule (BitVec 32)) (virtual : Nat) : IO Unit := do
  let some (word,env) := code.locate (Vector.replicate 2 0) virtual
    | throw (IO.userError "Typed counted schedule rejected a tested virtual position")
  expect s .virtualPC virtual "typed schedule virtual PC"
  expect s .env0 env[0].val "typed schedule inner environment"
  expect s .env1 env[1].val "typed schedule outer environment"
  let physical := BitVec.ofNat 6 (out s .pc)
  check (((s.values (.word physical)).extractLsb' 0 32) == word)
    "hardware-selected leaf differs from typed Schedule.locate"

private def countedCases : IO Unit := do
  let shift : BitVec 32 := 0x1c1
  let keepRx : BitVec 32 := 0x4201d2
  let drive : BitVec 32 := 0x1c0
  let spi : Schedule (BitVec 32) := .seq
    (.repeat 3 (.repeat 7 (.seq (.emit shift) (.emit keepRx))))
    (.seq (.emit drive) (.emit 3))
  let rows := #[row shift (controlWord 2 0 3 0 7 false false),
    row keepRx (controlWord 2 0 3 0 7 true true), row drive, row 3]
  let start : Command := { command := 3, expectedGeneration := 1, txLength := 32, rxCapacity := 32, txData := 0x96553ca5 }
  let mut spiState := tick (program rows spi.span) start
  for v in [:65] do
    if v != 0 then spiState := tick spiState
    checkLocate spiState spi v
    expect spiState .busy 1 "nested SPI active positions"
  spiState := tick spiState
  expect spiState .mode 2 "nested SPI HALT"
  expect spiState .txConsumed 32 "nested SPI exactly 32 TX entries"
  expect spiState .rxLength 32 "nested SPI exactly 32 RX entries"
  expect spiState .virtualPC 0 "nested SPI terminal virtual PC"
  expect spiState .env0 0 "nested SPI terminal environment"

  -- Inner loop exit reaches a tail in its outer body, then an adjacent loop.
  let a : BitVec 32 := 0x4001c0
  let b : BitVec 32 := 0x4001c8
  let c : BitVec 32 := 0x4001d0
  let tails : Schedule (BitVec 32) := .seq
    (.repeat 1 (.seq (.repeat 1 (.emit a)) (.emit b)))
    (.seq (.repeat 2 (.emit c)) (.emit 3))
  let rows := #[row a (controlWord 2 0 1 0 1 false true),
    row b (controlWord 1 0 1 0 0 true false),
    row c (controlWord 1 2 2 0 0 true false), row 3]
  let mut tailsState := tick (program rows tails.span)
    { command := 3, expectedGeneration := 1, rxCapacity := 9 }
  for v in [:9] do
    if v != 0 then tailsState := tick tailsState
    checkLocate tailsState tails v
    expect tailsState .rxLength (v+1) "tail/adjacent loop single RX entry"
  tailsState := tick tailsState
  expect tailsState .mode 2 "tail/adjacent loop HALT"
  expect tailsState .rxLength 9 "tail/adjacent loop total RX"

  -- A two-edge leaf inside a repeat executes one RX effect per entry.
  let slow : BitVec 32 := a + 512
  let rows := #[row slow (controlWord 1 0 2 0 0 true false), row 3]
  let mut slowState := tick (program rows 4)
    { command := 3, expectedGeneration := 1, rxCapacity := 3 }
  for v in [:3] do
    expect slowState .rxLength (v+1) "counted timed entry once"
    let held := tick slowState
    expect held .rxLength (v+1) "counted timed hold no append"
    expect held .virtualPC v "counted timed hold no dispatch"
    slowState := tick held
  expect slowState .mode 2 "counted timed HALT"

  for bad in [(1 : Nat)*4194304, 3, 256, 1+2048, 2+1048576, 1+4] do
    let corrupt := tick (program #[row (0x4001c1) (BitVec.ofNat 24 bad)] 1)
      { command := 3, expectedGeneration := 1, txLength := 1, rxCapacity := 1 }
    expect corrupt .mode 3 "malformed loop control faults"
    expect corrupt .txConsumed 0 "malformed control before TX"
    expect corrupt .rxLength 0 "malformed control before RX"

  let boundary : Values Register := fun {w} r => BitVec.ofNat w
    (if registerIndex r < 64 then (row 0x4001c1).toNat
      else if registerIndex r == 72 then 1
      else if registerIndex r == 75 then 1023
      else if registerIndex r == 76 then 1024
      else if registerIndex r == 67 then 2
      else if registerIndex r == 84 || registerIndex r == 88 then 20
      else if registerIndex r == 85 || registerIndex r == 87 then 3
      else ((seeded 1 0 1 3) r).toNat)
  let stopped := tick (snapshot boundary)
  expect stopped .mode 3 "virtual PC1024 fault before wrap"
  expect stopped .virtualPC 0 "virtual boundary terminal convention"
  expect stopped .txConsumed 3 "virtual boundary no TX effect"
  expect stopped .rxLength 3 "virtual boundary no RX effect"
  IO.println "Counted hardware: typed Schedule.locate bindings, nested rollover, tails/adjacent loops, timed entry, malformed controls and virtual boundary passed."

def main : IO Unit := do
  countedCases
  IO.println "Checking buffered hardware directed lifecycle cases."
  (← IO.getStdout).flush
  let start : Command := { command := 3, expectedGeneration := 1 }
  let cold : Snapshot := tick (snapshot (seeded 65535 65535)) { coldInit := true }
  expect cold .generation 0 "cold generation"
  expect cold .transfer 0 "cold transfer"
  expect cold .valid 0 "cold image invalidation"

  let warm : Snapshot := tick (snapshot (seeded 6 42)) { command := 7 }
  expect warm .generation 7 "warm generation advances"
  expect warm .transfer 42 "warm transfer preserved"
  expect warm .valid 0 "warm image invalidation"
  expect warm .retained 0 "warm ownership invalidation"
  let saturatedWarm : Snapshot := tick (snapshot (seeded 65535 42)) { command := 7 }
  expect saturatedWarm .generation 65535 "warm fail closed saturation"
  expect saturatedWarm .transfer 42 "saturated warm transfer preserved"

  let exhausted : Snapshot := snapshot (seeded 1 65535)
  expect exhausted .rejected 1 "exhausted transfer admission" start
  let noStart : Snapshot := tick exhausted start
  expect noStart .transfer 65535 "exhausted transfer no wrap"
  expect noStart .retained 0 "exhausted start no result"

  let dirtyValues : Values Register := fun {w} r => BitVec.ofNat w
    (if registerLabel r == "pending" || registerLabel r == "written" then 1
      else ((seeded 65535 42 1 3) r).toNat)
  let dirty := snapshot dirtyValues
  expect dirty .rejected 1 "exhausted image admission" { command := 2, count := 1 }
  let noCommit : Snapshot := tick dirty { command := 2, count := 1 }
  expect noCommit .generation 65535 "exhausted generation no wrap"
  IO.println "Finite ownership boundaries passed."
  (← IO.getStdout).flush

  let malformed : Snapshot := tick (snapshot (seeded 1 0 1 0x10000e1)) { start with txLength := 1, rxCapacity := 1 }
  expect malformed .mode 3 "malformed entry faults"
  expect malformed .txConsumed 0 "malformed no TX"
  expect malformed .rxLength 0 "malformed no RX"
  expect malformed .levels 4 "malformed idle restored"

  -- SHIFT plus RX: underflow precedes RX capacity failure; overflow occurs
  -- after successful TX consumption, preserving that one-bit prefix.
  let shiftRx : BitVec 56 := 0x4001c1
  let under : Snapshot := tick (snapshot (seeded 1 0 1 shiftRx)) start
  expect under .mode 3 "TX underflow"
  expect under .txConsumed 0 "underflow empty prefix"
  expect under .rxLength 0 "underflow before RX"
  let over : Snapshot := tick (snapshot (seeded 1 0 1 shiftRx)) { start with txLength := 1, txData := 1 }
  expect over .mode 3 "RX overflow"
  expect over .txConsumed 1 "overflow retains consumed TX"
  expect over .rxLength 0 "overflow RX unchanged"
  expect over .levels 4 "overflow restores idle"
  IO.println "Entry failure priorities passed."
  (← IO.getStdout).flush

  let boundaryValues : Values Register := fun {w} r => BitVec.ofNat w
    (if registerLabel r == "mode" then 1
      else if registerLabel r == "pc" then 63
      else if registerLabel r == "virtual_span" then 1024
      else ((seeded 1 0 64 0x1c2) r).toNat)
  let endOfBank : Snapshot := tick (snapshot boundaryValues)
  expect endOfBank .mode 3 "physical PC64 faults instead of wrapping"
  expect endOfBank .pc 0 "terminal PC convention"
  expect endOfBank .retained 1 "physical PC64 retained fault"

  let resultValues : Values Register := fun {w} r => BitVec.ofNat w
    (if registerLabel r == "retained" then 1
      else if registerLabel r == "mode" then 2
      else if registerLabel r == "rx_data" then 42
      else if registerLabel r == "rx_length" || registerLabel r == "tx_consumed" then 6
      else ((seeded 1 7 1 3) r).toNat)
  let result := snapshot resultValues
  expect result .readValid 1 "indexed retained read" { readIndex := 3 }
  expect result .readBit 1 "indexed bit order" { readIndex := 3 }
  expect result .rejected 1 "unread upload blocked" { command := 1 }
  expect result .rejected 1 "unread start blocked" start
  let held : Snapshot := tick result { readIndex := 3 }
  expect held .rxData 42 "read nondestructive"
  expect held .rxLength 6 "read retains length"
  let stale : Command := { command := 4, expectedGeneration := 1, expectedTransfer := 6 }
  expect held .rejected 1 "stale release rejected" stale
  expect (tick held stale) .retained 1 "stale release retains ownership"
  let released : Snapshot := tick held { stale with expectedTransfer := 7 }
  expect released .retained 0 "matching release"
  expect released .readValid 0 "released read invalid"
  IO.println "Buffered counted hardware: cold/warm lifecycle, finite counter boundaries, malformed/underflow/overflow priority, physical PC64 boundary, and retained indexed read/release passed."
