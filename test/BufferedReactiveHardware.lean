import Pinwheel.Hardware.Buffered.ReactiveProofs
import Pinwheel.Engine.Counted
import Lean

open Pinwheel.Hardware Pinwheel.Hardware.Buffered.Reactive
open Pinwheel.Engine.Reactive.Counted (Schedule)

open Lean Elab Command in
elab "#audit_buffered_reactive" : command => do
  let env ← getEnv
  let mut count : Nat := 0
  let mut proofs : Nat := 0
  for (name, info) in env.constants.toList do
    if name.toString.startsWith "Pinwheel.Hardware.Buffered.Reactive." ||
        name.toString.startsWith "Pinwheel.Hardware.Buffered.MemoEmit." then
      count := count + 1
      if info.isTheorem then proofs := proofs + 1
      let axioms ← collectAxioms name
      let unexpected := axioms.filter fun ax =>
        ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound
      unless unexpected.isEmpty do
        throwError "Unapproved buffered circuit axioms: {unexpected}"
  logInfo m!"Buffered reactive circuit: {count} declarations, {proofs} local theorems; standard axioms only."

#audit_buffered_reactive

private structure Command where
  coldInit : Bool := false
  command : BitVec 3 := 0
  address : BitVec 6 := 0
  word : BitVec 64 := 0
  control : BitVec 24 := 0
  branch : BitVec 56 := 0
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
  | _,.address => c.address | _,.word => c.word | _,.control => c.control | _,.branch => c.branch
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
    (word : BitVec 144 := 3) : Values Register
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
  unless ok do throw (IO.userError ("Buffered reactive hardware failure: " ++ label))

private def out (s : Snapshot) (o : Output w) (c : Command := {}) : Nat :=
  (circuit.observe c.values s.values o).toNat

private def expect (s : Snapshot) (o : Output w) (n : Nat) (label : String)
    (c : Command := {}) : IO Unit := check (out s o c == n) label

private def put (s : Snapshot) (r : Register w) (n : Nat) : Snapshot :=
  ⟨s.bank.set! (registerIndex r) n⟩

private def word (kind : Nat) (duration : Nat := 1) (enabled : Nat := 7)
    (append : Nat := 0) (capture : Nat := 0) (terminal : Nat := 0)
    (mask value : Nat := 0) (budget : Nat := 1)
    (waitInput : Nat := 0) (waitLevel : Bool := false)
    (pin : Nat := 0) (shiftEnable invert : Bool := false)
    (preserveLevels preserveEnabled : Nat := 0) (levels : Nat := 0) : BitVec 64 :=
  BitVec.ofNat 64 (kind + levels*2^3 + enabled*2^6 + (duration-1)*2^9 + preserveLevels*2^17 +
    pin*2^20 + append*2^22 + shiftEnable.toNat*2^24 + invert.toNat*2^25 +
    preserveEnabled*2^26 + capture*2^29 + terminal*2^35 + mask*2^41 + value*2^43 +
    waitInput*2^45 + waitLevel.toNat*2^46 + (budget-1)*2^47)

private def controlWord (depth outerStart outerBound innerStart innerBound : Nat)
    (outerEnd innerEnd : Bool) : BitVec 24 :=
  BitVec.ofNat 24 (depth + outerStart*4 + outerBound*256 + innerStart*2048 +
    innerBound*131072 + outerEnd.toNat*1048576 + innerEnd.toNat*2097152)

private def endpointWord (virtual physical outer inner : Nat) : Nat :=
  virtual*2 + physical*2^11 + outer*2^18 + inner*2^21

private def branchWord (finish sample yes no : Nat) : BitVec 56 :=
  BitVec.ofNat 56 (finish + sample*4 + yes*2^6 + no*2^30)

private def row (word : BitVec 64) (metadata : BitVec 24 := 0)
    (branch : BitVec 56 := 0) : BitVec 144 := branch ++ (metadata ++ word)

private def program (rows : Array (BitVec 144)) (span : Nat) : Snapshot :=
  snapshot (fun {w} r => BitVec.ofNat w
    (if registerIndex r < 64 then (rows[registerIndex r]?.getD 0).toNat
      else if registerIndex r == 67 then rows.size
      else if registerIndex r == 76 then span
      else if registerIndex r == 89 || registerIndex r == 90 then 3
      else ((seeded 1 0 1 3) r).toNat))

private def start : Command := {command := 3, expectedGeneration := 1, rawInputs := 3}

private def directed : IO Unit := do
  check (registers.size == 99) "declared register count"
  check ((registers.foldl (fun n p => n+p.1) 0) == 9599) "declared register bit count"
  let idle := snapshot (fun _ => 0)
  let cold := tick idle {coldInit := true}
  expect cold .mode 0 "cold ready"
  expect cold .phase 0 "cold phase"
  expect cold .scratch 0 "cold scratch"
  expect cold .stage1 0 "cold sampler first"
  expect cold .stage2 0 "cold sampler second"
  let written := tick cold {command := 1, word := 3, rawInputs := 3}
  expect written .pending 1 "row write coverage pending"
  expect written .valid 0 "write invalidates old image"
  let loaded := tick written {command := 2,count := 1,virtualSpan := 1,idleLevels := 4,idleEnabled := 7,rawInputs := 3}
  expect loaded .valid 1 "coverage admitted"
  expect loaded .generation 1 "commit generation"
  let complete := tick loaded start
  expect complete .phase 5 "halt retained complete"
  expect complete .mode 2 "legacy complete projection"
  expect complete .retained 1 "halt owns result"
  expect complete .transfer 1 "start identity"
  let stale := tick complete {command := 4, expectedGeneration := 1,expectedTransfer := 2}
  expect stale .retained 1 "stale release blocked"
  let released := tick complete {command := 4,expectedGeneration := 1,expectedTransfer := 1}
  expect released .retained 0 "matching release"
  let warm := tick complete {command := 7}
  expect warm .generation 2 "warm invalidates image identity"
  expect warm .transfer 1 "warm keeps transfer identity"
  expect warm .valid 0 "warm invalidates image"

  -- Entry scratch is committed before buffer faults, while malformed records do nothing.
  let data := word 1 (append := 2) (capture := 9)
  let under := tick (program #[row data,row 3] 2) {start with rxCapacity := 1}
  expect under .phase 7 "TX underflow fault"
  expect under .txConsumed 0 "underflow no TX"
  expect under .rxLength 0 "underflow blocks RX"
  expect under .scratch 4 "underflow retains entry scratch"
  let overflow := tick (program #[row data,row 3] 2) {start with txLength := 1,txData := 1}
  expect overflow .phase 7 "RX overflow fault"
  expect overflow .txConsumed 1 "overflow retains consumed TX"
  expect overflow .rxLength 0 "overflow preserves empty RX"
  expect overflow .scratch 4 "overflow retains entry scratch"
  let malformed := tick (program #[row (data + BitVec.ofNat 64 (2^56)),row 3] 2)
    {start with txLength := 1,rxCapacity := 1}
  expect malformed .phase 7 "reserved word faults"
  expect malformed .scratch 0 "malformed prevents entry scratch"
  expect malformed .txConsumed 0 "malformed prevents TX"
  expect malformed .rxLength 0 "malformed prevents RX"

  -- WAIT entry neither observes readiness nor repeats its RX effect on held edges.
  let wait := word 5 (enabled := 0) (append := 2) (budget := 2) (waitLevel := true)
  let waiting := tick (program #[row wait,row 3] 2) {start with rxCapacity := 1}
  expect waiting .phase 2 "WAIT entry phase"
  expect waiting .remaining 1 "WAIT full budget on entry"
  expect waiting .rxLength 1 "WAIT single entry RX"
  let ready := tick waiting
  expect ready .phase 5 "WAIT readiness on following edge"
  expect ready .rxLength 1 "WAIT held no repeat append"
  let blocked := put (put (program #[row (word 5 (enabled := 0) (waitLevel := true)),row 3] 2) .stage1 0) .stage2 0
  let timed := tick (tick blocked start)
  expect timed .phase 6 "WAIT exhausted timeout"
  expect timed .mode 3 "legacy failure projection"
  expect timed .levels 4 "timeout restores idle"

  -- CHECKED guards start on the following edge and precede terminal capture.
  let guarded := word 6 (append := 1) (terminal := 1) (mask := 1) (value := 1)
  let low := put (put (program #[row guarded,row 3] 2) .stage1 0) .stage2 0
  let entered := tick low {start with rxCapacity := 1}
  expect entered .phase 3 "CHECKED guard not applied on entry"
  expect entered .rxLength 1 "CHECKED entry RX"
  let failed := tick entered
  expect failed .phase 7 "CHECKED guard fault"
  expect failed .scratch 0 "guard prevents terminal capture"
  expect failed .rxLength 1 "guard retains RX prefix"

  -- The terminal capture is forwarded into this edge's branch selection.
  let branch := branchWord 2 0 (endpointWord 2 2 0 0) (endpointWord 1 1 0 0)
  let selected := tick (tick (program #[row (word 6 (terminal := 1)) 0 branch,row 3,row 4] 3) start)
  expect selected .phase 7 "same-edge terminal capture selected true fault"
  expect selected .scratch 1 "terminal capture survives stop"
  let selectedInvalid := tick (tick (program #[row (word 6 (append := 1) (terminal := 1)) 0
      (branchWord 2 0 (endpointWord 7 64 0 0) 1),row 3] 2) {start with rxCapacity := 1})
  expect selectedInvalid .phase 7 "selected invalid absolute fault"
  expect selectedInvalid .scratch 1 "invalid destination retains terminal capture"
  expect selectedInvalid .rxLength 1 "invalid destination retains entry prefix"
  let unselectedInvalid := tick (tick (program #[row (word 6 (append := 1)) 0
      (branchWord 2 0 (endpointWord 7 64 0 0) 1),row 3] 2) {start with rxCapacity := 1})
  expect unselectedInvalid .phase 5 "unselected invalid absolute admitted"
  expect unselectedInvalid .rxLength 1 "unselected invalid absolute entry effects"

  -- Jump into a nested body restores both indices, then ordinary exit reaches its tail.
  let nested := controlWord 2 1 1 1 1 true true
  let jumping := program #[row (word 6) 0 (branchWord 1 0 (endpointWord 4 1 1 1) 0),
    row (word 0 (append := 2)) nested,row 3] 6
  let atTarget := tick (tick jumping {start with rxCapacity := 1})
  expect atTarget .pc 1 "absolute jump physical row"
  expect atTarget .virtualPC 4 "absolute jump virtual position"
  expect atTarget .env0 1 "absolute jump inner restored"
  expect atTarget .env1 1 "absolute jump outer restored"
  expect atTarget .rxLength 1 "absolute target entry append"
  let atTail := tick atTarget
  expect atTail .phase 5 "nested jump exit tail"
  expect atTail .env0 0 "nested jump stopped environment"

  -- A self jump is a new entry even when both PCs remain equal.
  let looping := program #[row (word 6 (append := 1)) 0 (branchWord 1 0 0 0),row 3] 2
  let mut self := tick looping {start with rxCapacity := 3}
  for length in [1,2,3] do
    expect self .rxLength length "self entry appends exactly once"
    expect self .phase 3 "self entry remains checked"
    self := tick self
  expect self .phase 7 "self entry RX overflow"
  expect self .rxLength 3 "self entry retained prefix"

  -- Qualification resets its interval on blockage and replenishes budget on progress.
  let q := tick (program #[row (word 7 3 0 (mask := 3) (value := 3) (budget := 2)),row 3] 2) start
  expect q .remaining 2 "qualify entry duration"
  expect q .waitLeft 1 "qualify entry budget"
  let progress := tick q
  expect progress .remaining 1 "qualify ready interval decremented"
  expect progress .waitLeft 1 "qualify ready budget replenished"
  let retry := tick (put progress .stage2 0)
  expect retry .remaining 2 "qualify blockage resets interval"
  expect retry .waitLeft 0 "qualify blockage consumes budget"
  let timeout := tick (put retry .stage2 0)
  expect timeout .phase 6 "qualify blocked timeout"
  let renewed := tick (put retry .stage2 3)
  expect renewed .remaining 1 "qualify progress after blockage"
  expect renewed .waitLeft 1 "qualify progress replenishes budget"

  -- NEXT normalization rejects either arm at1023 before the new entry's effects.
  let rows := #[row (word 0),row (word 6 (append := 1) (capture := 9)) 0 (branchWord 2 0 1 0)]
  let boundary := put (put (put (put (put (program rows 1024) .phase 1) .virtualPC 1022) .scratch 8) .rxLength 3) .rxCapacity 20
  let badNext := tick boundary
  expect badNext .phase 7 "eager unselected NEXT normalization fault"
  expect badNext .scratch 8 "eager NEXT no scratch effects"
  expect badNext .rxLength 3 "eager NEXT no RX effects"
  let terminalInLoop := tick (program #[row 3 (controlWord 1 0 7 0 0 true false)] 8) start
  expect terminalInLoop .phase 5 "terminal in repeat admitted"
  expect terminalInLoop .env0 0 "terminal in repeat canonical stop"

  -- Open-drain SHIFT modifies enables with inversion, KEEP preserves that enable.
  let shifted := tick (program #[row (word 1 (enabled := 1) (pin := 1) (shiftEnable := true) (invert := true)),
    row (word 2 (enabled := 0) (preserveEnabled := 2)),row 3] 3) {start with txLength := 1,txData := 0}
  expect shifted .levels 0 "open drain levels zero"
  expect shifted .enabled 3 "open drain inverted zero pulls low"
  expect (tick shifted) .enabled 2 "KEEP enable preservation"
  IO.println "Reactive hardware: lifecycle, scratch/data priorities, wait/guard/qualification, forwarded branch, invalid and nested targets, self-entry, eagerNEXT and open-drain cases passed."

/-- A tractable DAG compares the target-local native optimization against the
safe emitter, including shared children across next-state and output roots. -/
private def emitterComparison : IO Unit := do
  let shared : E 32 := .sub (.band (.input .txData) (.inv (.reg .txData))) (.lit 3735928559)
  let wide : E 64 := .concat shared shared
  let selected : E 32 := .mux (.ult shared (.lit 2147483648))
    (.slice 7 32 (by decide) wide) shared
  let flag : E 1 := .band (.inv (.zero shared)) (.equal selected (.lit 0))
  let small : Circuit Input Register Output := {
    next := fun {w} r => match r with
      | .txData => selected
      | .phase => .mux flag (.lit 7) (.reg .phase)
      | r => .reg r
    output := fun {w} o => match o with
      | .rxData => selected
      | .phase => .mux (.input .initialize) (.lit 0) (.reg .phase)
      | .readBit => flag
      | _ => .lit 0 }
  let ins : Array (Sigma Input) := #[⟨32,.txData⟩,⟨1,.initialize⟩]
  let regs : Array (Sigma Register) := #[⟨32,.txData⟩,⟨3,.phase⟩]
  let outs : Array (Sigma Output) := #[⟨32,.rxData⟩,⟨3,.phase⟩,⟨1,.readBit⟩]
  let safe := Emit.moduleText "shared_expression_fixture" small ins regs outs
    inputLabel registerLabel outputLabel
  let optimized := Pinwheel.Hardware.Buffered.MemoEmit.moduleText
    "shared_expression_fixture" small ins regs outs inputLabel registerLabel outputLabel
  check (safe.toOption == optimized.toOption) "native memo emitter equals safe emitter on every Expr constructor"
  match optimized with
  | .error e => throw (IO.userError e)
  | .ok text => check (text.contains "3735928559") "wide literal and emission succeeded"

def main : IO Unit := do
  emitterComparison
  directed
