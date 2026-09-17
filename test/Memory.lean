import Pinwheel
import Pinwheel.Hardware.Memory.Registered
import Pinwheel.Hardware.Storage.Prefetch

/-! Executable evidence for the memory contract: the two structural
implementations against the specification, and the prefetch machine (the
reference machine against a memory of latency one) run closed-loop with a bus
target, edge for edge against the atomic reference, with a single-port variant
shown to diverge. -/
open Pinwheel Pinwheel.Hardware

private def ensure (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

/-! ## Implementations against the contract -/

private def lcg (x : Nat) : Nat := (x * 1103515245 + 12345) % 2147483648

/-- Deterministic requests: writes to every address, reads that sometimes hit the
word written on the same edge. -/
private def requests (n : Nat) : List (Memory.Request 3 8 2) :=
  let rec go (seed : Nat) : Nat → List (Memory.Request 3 8 2)
    | 0 => []
    | k + 1 =>
      let a := lcg seed
      let b := lcg a
      let c := lcg b
      ⟨⟨a % 3 != 0, BitVec.ofNat 3 (a / 8), BitVec.ofNat 8 (b / 16)⟩,
        fun port => if port = 0 then BitVec.ofNat 3 (a / 8) else BitVec.ofNat 3 (c / 4)⟩ :: go c k
  go 7 n

private def sameReads (x y : Fin 2 → BitVec 8) : Bool := x 0 == y 0 && x 1 == y 1

private def sameTrace (xs ys : List ((Fin 2 → BitVec 8) × (Fin 2 → BitVec 8))) : Bool :=
  xs.length == ys.length && (List.zip xs ys).all fun (a, b) => sameReads a.1 b.1 && sameReads a.2 b.2

private def contract : IO Nat := do
  let c0 : Memory.Contents 3 8 := fun k => BitVec.ofNat 8 (k.toNat * 17 + 3)
  let inputs := requests 400
  let flops := (Memory.Flops.component 3 8 2).trace (@Memory.Flops.contentsValues 3 8 c0) inputs
  let spec0 := (Memory.spec 3 8 2 0).trace ⟨c0, fun k => k.elim0⟩ inputs
  ensure (sameTrace flops spec0) "flip-flop memory diverged from the latency-0 specification"
  let s1 : Memory.State 3 8 2 1 := ⟨c0, fun _ _ => 0⟩
  let registered := (Memory.Registered.component 3 8 2).trace (@Memory.Registered.stateValues 3 8 2 s1) inputs
  let spec1 := (Memory.spec 3 8 2 1).trace s1 inputs
  ensure (sameTrace registered spec1) "registered memory diverged from the latency-1 specification"
  -- The latencies are observably different, and the registered read is the earlier read.
  ensure (!sameTrace spec0 spec1) "latency 0 and 1 are not distinguished by these requests"
  let shifted := (List.zip spec0 (spec1.drop 1)).all fun (a, b) => sameReads a.1 b.1
  ensure shifted "a latency-1 read is not the latency-0 read of the previous edge"
  pure inputs.length

/-! ## The prefetch machine, closed-loop, against the atomic reference -/

private def upload (p : Execution.Image) : IO (List (BitVec 64)) := do
  let some image := Execution.lowerIndexed (Execution.imageWords p)
    | throw (IO.userError "program does not fit the 64-entry dictionary")
  let idle : BitVec 6 := p.idle.enabled ++ p.idle.levels
  pure (image.val.dictionary.toList ++ image.val.addresses.toList.map (·.zeroExtend 64) ++
    [idle.zeroExtend 64, BitVec.ofNat 64 p.last.val])

private structure Pair where
  reference : Loader.Machine.State
  prefetch : Storage.Prefetch.State
  edges : Nat := 0
  branches : Nat := 0
  rejected : Nat := 0

private def initialMachine : Loader.Machine.State :=
  ⟨{}, ⟨0, 0, 0, 0, {}, Vector.replicate 16 false⟩, fun _ {_} _ => 0⟩

private def initialPair : Pair := ⟨initialMachine, ⟨initialMachine, 0, fun _ => 0⟩, 0, 0, 0⟩

private def probes : List ((w : Nat) × Loader.Machine.Output w) :=
  [⟨1, .core .busy⟩, ⟨8, .core .readB⟩, ⟨8, .core .readA⟩, ⟨3, .core (.state .mode)⟩,
    ⟨3, .core (.state .levels)⟩, ⟨3, .core (.state .enabled)⟩, ⟨1, .control .push⟩,
    ⟨1, .control .commit⟩, ⟨1, .control .rejected⟩]

private def observe (v : Values Loader.Machine.Output) : List Nat :=
  probes.map fun ⟨_, o⟩ => (v o).toNat

/-- One edge of both machines under the same input; the prefetch machine's
control, core and every probed output must agree with the reference. -/
private def step (pair : Pair) (i : Loader.Machine.Inputs) (variant : Option (Loader.Machine.Inputs →
    Storage.Prefetch.State → Storage.Prefetch.State) := none) : IO (Pair × Bool) := do
  let outputs := observe (Storage.Prefetch.component.observe i pair.prefetch)
  let expected := observe (Storage.Cache.referenceComponent.observe i pair.reference)
  let reference := Loader.Machine.next i pair.reference
  let prefetch := (variant.getD Storage.Prefetch.next) i pair.prefetch
  let taken := Storage.Prefetch.branch i pair.prefetch && pair.prefetch.machine.core.mode == 3 &&
    reference.core.pc != pair.reference.core.pc
  let agree := outputs == expected && prefetch.machine.control == reference.control &&
    prefetch.machine.core == reference.core
  let rejected := if (Storage.Cache.referenceComponent.observe i pair.reference (.control .rejected)) == 1 then 1 else 0
  pure (⟨reference, prefetch, pair.edges + 1, pair.branches + (if taken then 1 else 0), pair.rejected + rejected⟩, agree)

private def stepEnsure (pair : Pair) (i : Loader.Machine.Inputs) (what : String) : IO Pair := do
  let (pair, agree) ← step pair i
  ensure agree s!"prefetch machine diverged from the reference at edge {pair.edges} ({what})"
  pure pair

private def load (pair : Pair) (words : List (BitVec 64)) : IO Pair := do
  let mut pair ← stepEnsure pair {command := 1} "begin"
  for word in words do
    pair ← stepEnsure pair {command := 2, data := word} "push"
  -- A busy or malformed command is rejected without touching the staged image.
  pair ← stepEnsure pair {command := 6} "reject"
  stepEnsure pair {command := 3} "commit"

/-- The pins the core drives, from its probed outputs: open-drain, enabled bits pull low. -/
private def commandOf (v : Values Loader.Machine.Output) : I2C.Pins :=
  let enabled := v (.core (.state .enabled))
  let levels := v (.core (.state .levels))
  ⟨if enabled[0] && !levels[0] then .low else .release, if enabled[1] && !levels[1] then .low else .release⟩

/-- Run the started program closed-loop with an acknowledging or not acknowledging
target that changes SDA only while SCL is low. Ordinary protocols see a patterned
input. Returns the pair and the number of completed clock pulses. -/
private def run (pair : Pair) (targetLow : Nat → Bool) (limit : Nat)
    (variant : Option (Loader.Machine.Inputs → Storage.Prefetch.State → Storage.Prefetch.State) := none) :
    IO (Pair × Nat × Bool) := do
  let mut pair := pair
  let mut target : I2C.Pins := {}
  let mut previous : I2C.Bus := {}
  let mut pulses := 0
  let mut pending : Option Bool := none
  let mut agreed := true
  for t in [:limit] do
    if pair.reference.core.mode.toNat ≥ 5 then break
    let command := commandOf (Storage.Cache.referenceComponent.observe {} pair.reference)
    let bus := I2C.resolve command target
    if !previous.scl && bus.scl then pending := some bus.sda
    if previous.scl && !bus.scl then
      if pending.isSome then pulses := pulses + 1
      pending := none
    if !bus.scl then target := {target with sda := if targetLow pulses then .low else .release}
    let observed := I2C.resolve command target
    let incoming := BitVec.ofNat 2 ((if observed.scl then 1 else 0) + (if observed.sda then 2 else 0))
    -- Loader commands during execution are rejected while busy.
    let i : Loader.Machine.Inputs := {incoming, command := if t % 7 == 3 then 2 else 0, data := 4}
    let (next, agree) ← step pair i variant
    pair := next
    agreed := agreed && agree
    previous := observed
  pure (pair, pulses, agreed)

private def writeTarget (addressAck dataAck : Bool) (pulses : Nat) : Bool :=
  if pulses == 8 then addressAck else if pulses == 17 then dataAck else false

private def readTarget (byte : BitVec 8) (pulses : Nat) : Bool :=
  if pulses == 8 || pulses == 17 || pulses == 26 then true
  else if 27 ≤ pulses && pulses < 35 then !byte.toNat.testBit (34 - pulses) else false

private def machines : IO (Nat × Nat × Nat) := do
  let cfg : I2C.Config := ⟨3, 7⟩
  let write := Execution.widenProgram (Compile.I2C.program cfg ⟨0x53, 0xa6⟩)
  let read := Compile.I2CRead.program cfg ⟨0x53, 0xa6⟩
  let uart := Execution.widenProgram (Engine.Reactive.embedProgram (Compile.UART.program ⟨3⟩ 0x53))
  let spi := Execution.widenProgram (Engine.Reactive.embedProgram (Compile.SPI.program ⟨3⟩ 0xa6))
  let mut pair := initialPair
  pair ← stepEnsure pair {init := true} "initialize"
  -- A start before any commit is rejected; the fetched words are owed nothing.
  pair ← stepEnsure pair {command := 5} "start-before-commit"
  let mut transactions := 0
  for (p, targets) in [(write, [writeTarget true true, writeTarget false true, writeTarget true false]),
      (read, [readTarget 0x96, readTarget 0x00, readTarget 0xff]),
      (uart, [fun _ => false]), (spi, [fun p => p % 2 == 0])] do
    pair ← load pair (← upload p)
    for target in targets do
      pair ← stepEnsure pair {command := 5} "start"
      let (next, _, agreed) ← run pair target 4000
      ensure agreed "prefetch machine diverged from the reference during a run"
      ensure (next.reference.core.mode.toNat ≥ 5) "program did not finish"
      pair := next
      transactions := transactions + 1
    -- Reset between programs, then a second image is staged while the core is stopped.
    pair ← stepEnsure pair {reset := true} "reset"
  -- Interleave: stage the write program, start the read program that is committed,
  -- and commit the staged image only after the run: the switch must refill the fetch.
  pair ← load pair (← upload read)
  pair ← stepEnsure pair {command := 1} "begin-while-stopped"
  for word in (← upload write).take 100 do
    pair ← stepEnsure pair {command := 2, data := word} "stage"
  pair ← stepEnsure pair {command := 5} "start-read"
  let (next, _, agreed) ← run pair (readTarget 0x5a) 4000
  ensure agreed "prefetch machine diverged during the interleaved run"
  pair := next
  for word in (← upload write).drop 100 do
    pair ← stepEnsure pair {command := 2, data := word} "stage-rest"
  pair ← stepEnsure pair {command := 3} "commit-staged"
  pair ← stepEnsure pair {command := 5} "start-write"
  let (next, _, agreed) ← run pair (writeTarget true true) 4000
  ensure agreed "prefetch machine diverged after the bank switch"
  ensure (next.reference.core.mode.toNat = 5) "the switched-in write did not complete"
  pair := next
  transactions := transactions + 2
  ensure (pair.branches > 0) "no branch was taken"
  ensure (pair.rejected > 0) "no command was rejected"
  pure (pair.edges, transactions, pair.branches)

/-- Fetching only the untaken candidate — one read port — diverges on a taken
branch: the address NACK of the write program branches to STOP. -/
private def singlePort : IO Nat := do
  let naive (i : Loader.Machine.Inputs) (s : Storage.Prefetch.State) : Storage.Prefetch.State :=
    let n := Storage.Prefetch.next i s
    {n with fetched := fun _ => n.fetched false}
  let cfg : I2C.Config := ⟨3, 7⟩
  let write := Execution.widenProgram (Compile.I2C.program cfg ⟨0x53, 0xa6⟩)
  let mut pair := initialPair
  pair ← stepEnsure pair {init := true} "initialize"
  pair ← load pair (← upload write)
  pair ← stepEnsure pair {command := 5} "start"
  let (acked, _, agreedAck) ← run pair (writeTarget true true) 4000 (some naive)
  ensure agreedAck "single-port variant should agree while no branch is taken"
  ensure (acked.reference.core.mode.toNat = 5) "acknowledged write did not complete"
  pair ← stepEnsure acked {command := 5} "start"
  let (_, _, agreedNack) ← run pair (writeTarget false true) 4000 (some naive)
  ensure (!agreedNack) "single-port variant did not diverge on the taken branch"
  pure 2

def main : IO Unit := do
  let n ← contract
  let (edges, transactions, branches) ← machines
  let variants ← singlePort
  IO.println s!"Memory: {n} requests match latency 0 and 1; prefetch machine matched the reference on {edges} edges, {transactions} closed-loop transactions, {branches} taken branches; {variants} single-port runs, the second diverged."
