import Pinwheel
import Pinwheel.Hardware.Memory.Registered
import Pinwheel.Hardware.Storage.Decoupled
import Pinwheel.Hardware.Storage.SinglePort
import Pinwheel.Hardware.Storage.TwoPort
import Pinwheel.Hardware.Storage.Readiness

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

/-- The words the host pushes for an image: the library's definition, the one
`Readiness.upload_ready` speaks about. -/
private def upload (p : Execution.Image) : IO (List (BitVec 64)) := do
  let some words := Loader.ProgramImage.upload p
    | throw (IO.userError "program does not fit the 64-entry dictionary")
  pure words

/-- A machine under test: how to step it, what it shows, and which of its fields
mirror the reference. -/
private structure Driver (σ : Type) where
  next : Loader.Machine.Inputs → σ → σ
  observe : Loader.Machine.Inputs → σ → Values Loader.Machine.Output
  machine : σ → Loader.Machine.State
  branch : Loader.Machine.Inputs → σ → Bool
  /-- Force lazily held register values after an edge; the state it denotes is unchanged. -/
  normalize : σ → σ := id

private structure Pair (σ : Type) where
  reference : Loader.Machine.State
  candidate : σ
  edges : Nat := 0
  branches : Nat := 0
  rejected : Nat := 0

private def initialMachine : Loader.Machine.State :=
  ⟨{}, ⟨0, 0, 0, 0, {}, Vector.replicate 16 false⟩, fun _ {_} _ => 0⟩

private def prefetchDriver : Driver Storage.Prefetch.State :=
  { next := Storage.Prefetch.next, observe := Storage.Prefetch.component.observe, machine := (·.machine),
    branch := Storage.Prefetch.branch }

/-- Force a two-word policy's fetched registers, so closures do not chain across edges. -/
private def forceFetched (s : Storage.FetchPolicy.State Storage.Decoupled.Registers) :
    Storage.FetchPolicy.State Storage.Decoupled.Registers :=
  let taken := s.policy.fetched true
  let untaken := s.policy.fetched false
  {s with policy := {s.policy with fetched := fun b => if b then taken else untaken}}

private def decoupledDriver : Driver Storage.Decoupled.State :=
  { next := Storage.Decoupled.next, observe := Storage.Decoupled.component.observe, machine := (·.machine),
    branch := Storage.FetchPolicy.branch, normalize := forceFetched }

private def probes : List ((w : Nat) × Loader.Machine.Output w) :=
  [⟨1, .core .busy⟩, ⟨8, .core .readB⟩, ⟨8, .core .readA⟩, ⟨3, .core (.state .mode)⟩,
    ⟨3, .core (.state .levels)⟩, ⟨3, .core (.state .enabled)⟩, ⟨1, .control .push⟩,
    ⟨1, .control .commit⟩, ⟨1, .control .rejected⟩]

private def observe (v : Values Loader.Machine.Output) : List Nat :=
  probes.map fun ⟨_, o⟩ => (v o).toNat

/-- One edge of both machines under the same input; the candidate's control, core
and every probed output must agree with the reference. -/
private def step (d : Driver σ) (pair : Pair σ) (i : Loader.Machine.Inputs) : IO (Pair σ × Bool) := do
  let outputs := observe (d.observe i pair.candidate)
  let expected := observe (Storage.Cache.referenceComponent.observe i pair.reference)
  let reference := Loader.Machine.next i pair.reference
  let candidate := d.normalize (d.next i pair.candidate)
  let taken := d.branch i pair.candidate && (d.machine pair.candidate).core.mode == 3 &&
    reference.core.pc != pair.reference.core.pc
  let agree := outputs == expected && (d.machine candidate).control == reference.control &&
    (d.machine candidate).core == reference.core
  let rejected := if (Storage.Cache.referenceComponent.observe i pair.reference (.control .rejected)) == 1 then 1 else 0
  pure (⟨reference, candidate, pair.edges + 1, pair.branches + (if taken then 1 else 0), pair.rejected + rejected⟩, agree)

private def stepEnsure (d : Driver σ) (pair : Pair σ) (i : Loader.Machine.Inputs) (what : String) : IO (Pair σ) := do
  let (pair, agree) ← step d pair i
  ensure agree s!"candidate diverged from the reference at edge {pair.edges} ({what})"
  pure pair

private def load (d : Driver σ) (pair : Pair σ) (words : List (BitVec 64)) : IO (Pair σ) := do
  let mut pair ← stepEnsure d pair {command := 1} "begin"
  for word in words do
    pair ← stepEnsure d pair {command := 2, data := word} "push"
  -- A busy or malformed command is rejected without touching the staged image.
  pair ← stepEnsure d pair {command := 6} "reject"
  stepEnsure d pair {command := 3} "commit"

/-- The pins the core drives, from its probed outputs: open-drain, enabled bits pull low. -/
private def commandOf (v : Values Loader.Machine.Output) : I2C.Pins :=
  let enabled := v (.core (.state .enabled))
  let levels := v (.core (.state .levels))
  ⟨if enabled[0] && !levels[0] then .low else .release, if enabled[1] && !levels[1] then .low else .release⟩

/-- Run the started program closed-loop with an acknowledging or not acknowledging
target that changes SDA only while SCL is low. Ordinary protocols see a patterned
input. Returns the pair, the number of completed clock pulses and whether every
edge agreed. -/
private def run (d : Driver σ) (pair : Pair σ) (targetLow : Nat → Bool) (limit : Nat) :
    IO (Pair σ × Nat × Bool) := do
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
    let (next, agree) ← step d pair i
    pair := next
    agreed := agreed && agree
    previous := observed
  pure (pair, pulses, agreed)

private def writeTarget (addressAck dataAck : Bool) (pulses : Nat) : Bool :=
  if pulses == 8 then addressAck else if pulses == 17 then dataAck else false

private def readTarget (byte : BitVec 8) (pulses : Nat) : Bool :=
  if pulses == 8 || pulses == 17 || pulses == 26 then true
  else if 27 ≤ pulses && pulses < 35 then !byte.toNat.testBit (34 - pulses) else false

/-- The full scenario against the reference: every fixture program, ACK and NACK
targets, an image staged around a run, resets and rejected commands. -/
private def machines (d : Driver σ) (initial : σ) : IO (Nat × Nat × Nat) := do
  let cfg : I2C.Config := ⟨3, 7⟩
  let write := Execution.widenProgram (Compile.I2C.program cfg ⟨0x53, 0xa6⟩)
  let read := Compile.I2CRead.program cfg ⟨0x53, 0xa6⟩
  let uart := Execution.widenProgram (Engine.Reactive.embedProgram (Compile.UART.program ⟨3⟩ 0x53))
  let spi := Execution.widenProgram (Engine.Reactive.embedProgram (Compile.SPI.program ⟨3⟩ 0xa6))
  let mut pair : Pair σ := ⟨initialMachine, initial, 0, 0, 0⟩
  pair ← stepEnsure d pair {init := true} "initialize"
  -- A start before any commit is rejected; the fetched words are owed nothing.
  pair ← stepEnsure d pair {command := 5} "start-before-commit"
  let mut transactions := 0
  for (p, targets) in [(write, [writeTarget true true, writeTarget false true, writeTarget true false]),
      (read, [readTarget 0x96, readTarget 0x00, readTarget 0xff]),
      (uart, [fun _ => false]), (spi, [fun p => p % 2 == 0])] do
    pair ← load d pair (← upload p)
    for target in targets do
      pair ← stepEnsure d pair {command := 5} "start"
      let (next, _, agreed) ← run d pair target 4000
      ensure agreed "candidate diverged from the reference during a run"
      ensure (next.reference.core.mode.toNat ≥ 5) "program did not finish"
      pair := next
      transactions := transactions + 1
    -- Reset between programs, then a second image is staged while the core is stopped.
    pair ← stepEnsure d pair {reset := true} "reset"
  -- A start on the edge right after a halt: no idle edge in between.
  pair ← load d pair (← upload uart)
  pair ← stepEnsure d pair {command := 5} "start"
  let (next, _, agreed) ← run d pair (fun _ => false) 4000
  ensure agreed "candidate diverged in the immediate-restart run"
  pair := next
  pair ← stepEnsure d pair {command := 5} "restart-immediately"
  let (next, _, agreed) ← run d pair (fun _ => false) 4000
  ensure agreed "candidate diverged after an immediate restart"
  pair := next
  transactions := transactions + 2
  -- Interleave: stage the write program around a run of the committed read program,
  -- and commit the staged image only after the run: the switch must refill the fetch.
  pair ← load d pair (← upload read)
  pair ← stepEnsure d pair {command := 1} "begin-while-stopped"
  for word in (← upload write).take 100 do
    pair ← stepEnsure d pair {command := 2, data := word} "stage"
  pair ← stepEnsure d pair {command := 5} "start-read"
  let (next, _, agreed) ← run d pair (readTarget 0x5a) 4000
  ensure agreed "candidate diverged during the interleaved run"
  pair := next
  for word in (← upload write).drop 100 do
    pair ← stepEnsure d pair {command := 2, data := word} "stage-rest"
  pair ← stepEnsure d pair {command := 3} "commit-staged"
  pair ← stepEnsure d pair {command := 5} "start-write"
  let (next, _, agreed) ← run d pair (writeTarget true true) 4000
  ensure agreed "candidate diverged after the bank switch"
  ensure (next.reference.core.mode.toNat = 5) "the switched-in write did not complete"
  pair := next
  transactions := transactions + 2
  ensure (pair.branches > 0) "no branch was taken"
  ensure (pair.rejected > 0) "no command was rejected"
  pure (pair.edges, transactions, pair.branches)

/-! ## One read port: the per-program rule -/

private def singlePortDriver : Driver Storage.SinglePort.State :=
  { next := Storage.SinglePort.next, observe := Storage.SinglePort.component.observe, machine := (·.machine),
    branch := Storage.FetchPolicy.branch
    normalize := fun s =>
      let taken := s.policy.fetched true
      let untaken := s.policy.fetched false
      {s with policy := {s.policy with fetched := fun b => if b then taken else untaken}} }

/-- The decoupled organization with the start word sharing port 0 on commit edges. -/
private def twoPortDriver : Driver (Storage.FetchPolicy.State Storage.Decoupled.Registers) :=
  { next := Storage.FetchPolicy.next Storage.TwoPort.policy
    observe := (Storage.FetchPolicy.component Storage.TwoPort.policy).observe
    machine := (·.machine), branch := Storage.FetchPolicy.branch, normalize := forceFetched }

/-- Words of a program's upload that the one-port machine's rule rejects: branching
`checked` records with a zero duration field. -/
private def unready (p : Execution.Image) : IO Nat := do
  pure ((← upload p).filter (fun w => !Storage.SinglePort.Ready w)).length

/-- The rule is checkable per program: the fixture programs are ready, an I²C
configuration whose phases last one cycle and the UART receiver are not. -/
private def readiness : IO (Nat × Nat) := do
  let cfg : I2C.Config := ⟨3, 7⟩
  let fixtures : List (String × Execution.Image) :=
    [("I2C write", Execution.widenProgram (Compile.I2C.program cfg ⟨0x53, 0xa6⟩)),
     ("I2C read", Compile.I2CRead.program cfg ⟨0x53, 0xa6⟩),
     ("UART", Execution.widenProgram (Engine.Reactive.embedProgram (Compile.UART.program ⟨3⟩ 0x53))),
     ("SPI", Execution.widenProgram (Engine.Reactive.embedProgram (Compile.SPI.program ⟨3⟩ 0xa6)))]
  for (name, p) in fixtures do
    ensure ((← unready p) = 0) s!"{name} program has a word the one-port rule rejects"
  let short ← unready (Execution.widenProgram (Compile.I2C.program ⟨0, 7⟩ ⟨0x53, 0xa6⟩))
  ensure (short = 1) "the one-cycle-phase I2C write should have exactly one unready word"
  ensure ((← unready (Compile.I2CRead.program ⟨0, 7⟩ ⟨0x53, 0xa6⟩)) = 3)
    "the one-cycle-phase I2C read should have three unready words"
  let receiver ← unready (Compile.UARTRx.program ⟨16, by decide, by decide, 0⟩)
  ensure (receiver = 2) "the UART receiver should have two unready words"
  pure (fixtures.length, receiver)

/-- The one-port machine on a program the rule rejects: it agrees while the
zero-duration branch is not taken and diverges on the edge it is. -/
private def unreadyDiverges : IO Unit := do
  let write := Execution.widenProgram (Compile.I2C.program ⟨0, 7⟩ ⟨0x53, 0xa6⟩)
  let mut pair : Pair Storage.SinglePort.State :=
    ⟨initialMachine, ⟨initialMachine, 0, ⟨fun _ => 0, 0, false⟩⟩, 0, 0, 0⟩
  pair ← stepEnsure singlePortDriver pair {init := true} "initialize"
  pair ← load singlePortDriver pair (← upload write)
  pair ← stepEnsure singlePortDriver pair {command := 5} "start"
  let (acked, _, agreedAck) ← run singlePortDriver pair (writeTarget true true) 4000
  ensure agreedAck "one-port machine should agree while the unready branch is not taken"
  ensure (acked.reference.core.mode.toNat = 5) "acknowledged one-cycle write did not complete"
  pair ← stepEnsure singlePortDriver acked {command := 5} "start"
  let (_, _, agreedNack) ← run singlePortDriver pair (writeTarget false true) 4000
  ensure (!agreedNack) "one-port machine did not diverge on the unready taken branch"

def main : IO Unit := do
  let n ← contract
  let (edges, transactions, branches) ← machines prefetchDriver ⟨initialMachine, 0, fun _ => 0⟩
  let (edges', transactions', branches') ← machines decoupledDriver ⟨initialMachine, 0, ⟨fun _ => 0, 0⟩⟩
  let (edges'', transactions'', branches'') ←
    machines singlePortDriver ⟨initialMachine, 0, ⟨fun _ => 0, 0, false⟩⟩
  let (edges2, transactions2, branches2) ← machines twoPortDriver ⟨initialMachine, 0, ⟨fun _ => 0, 0⟩⟩
  let (ready, receiver) ← readiness
  unreadyDiverges
  IO.println s!"Memory: {n} requests match latency 0 and 1; prefetch machine matched the reference on {edges} edges, {transactions} closed-loop transactions, {branches} taken branches; decoupled machine on {edges'} edges, {transactions'} transactions, {branches'} taken branches; one-port machine on {edges''} edges, {transactions''} transactions, {branches''} taken branches; two-port machine on {edges2} edges, {transactions2} transactions, {branches2} taken branches; {ready} fixture programs ready, the UART receiver has {receiver} unready words, and the one-port machine diverges on an unready taken branch."
