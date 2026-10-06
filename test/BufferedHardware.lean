import Pinwheel.Hardware.Buffered.LinearProofs
import Lean

open Pinwheel.Hardware Pinwheel.Hardware.Buffered.Linear

open Lean Elab Command in
elab "#audit_buffered_linear" : command => do
  let env ← getEnv
  let mut count : Nat := 0
  let mut proofs : Nat := 0
  for (name, info) in env.constants.toList do
    if name.toString.startsWith "Pinwheel.Hardware.Buffered.Linear." then
      count := count + 1
      if info.isTheorem then proofs := proofs + 1
      let axioms ← collectAxioms name
      let unexpected := axioms.filter fun ax =>
        ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound
      unless unexpected.isEmpty do
        throwError "Unapproved buffered circuit axioms: {unexpected}"
  logInfo m!"Buffered linear circuit: {count} declarations, {proofs} local theorems; standard axioms only."

#audit_buffered_linear

private structure Command where
  coldInit : Bool := false
  command : BitVec 3 := 0
  address : BitVec 7 := 0
  word : BitVec 32 := 0
  count : BitVec 8 := 0
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
  | _,.address => c.address | _,.word => c.word | _,.count => c.count
  | _,.idleLevels => c.idleLevels | _,.idleEnabled => c.idleEnabled
  | _,.txData => c.txData | _,.txLength => c.txLength | _,.rxCapacity => c.rxCapacity
  | _,.expectedGeneration => c.expectedGeneration | _,.expectedTransfer => c.expectedTransfer
  | _,.readIndex => c.readIndex | _,.rawInputs => c.rawInputs

private structure Snapshot where
  bank : Array (String × Nat)

private def snapshot (s : Values Register) : Snapshot :=
  ⟨registers.map fun ⟨_,r⟩ => (registerLabel r,(s r).toNat)⟩

private def Snapshot.values (s : Snapshot) : Values Register := fun {w} r =>
  BitVec.ofNat w (((s.bank.find? fun p => p.1 == registerLabel r).map Prod.snd).getD 0)

private def tick (s : Snapshot) (c : Command := {}) : Snapshot :=
  snapshot (circuit.step c.values s.values)

private def seeded (generation transfer : Nat := 1) (count : Nat := 1)
    (word : BitVec 32 := 3) : Values Register
  | _,.word _ => word
  | _,.generation => BitVec.ofNat 16 generation
  | _,.transfer => BitVec.ofNat 16 transfer
  | _,.valid => 1
  | _,.count => BitVec.ofNat 8 count
  | _,.idleLevels => 4
  | _,.idleEnabled => 7
  | _,_ => 0

private def check (ok : Bool) (label : String) : IO Unit :=
  unless ok do throw (IO.userError ("Buffered hardware failure: " ++ label))

private def out (s : Snapshot) (o : Output w) (c : Command := {}) : Nat :=
  (circuit.observe c.values s.values o).toNat

private def expect (s : Snapshot) (o : Output w) (n : Nat) (label : String)
    (c : Command := {}) : IO Unit := check (out s o c == n) label

def main : IO Unit := do
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
  let shiftRx : BitVec 32 := 0x4001c1
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
      else if registerLabel r == "pc" then 127
      else ((seeded 1 0 128 0x1c2) r).toNat)
  let endOfBank : Snapshot := tick (snapshot boundaryValues)
  expect endOfBank .mode 3 "PC128 faults instead of wrapping"
  expect endOfBank .pc 0 "terminal PC convention"
  expect endOfBank .retained 1 "PC128 retained fault"

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
  IO.println "Buffered hardware: cold/warm lifecycle, finite counter boundaries, malformed/underflow/overflow priority, PC128 boundary, and retained indexed read/release passed."
