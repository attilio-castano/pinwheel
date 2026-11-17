import Lean
import Pinwheel.Hardware.Processor.CoreModel

open Lean Elab Command Pinwheel.Hardware.Processor
open RV32I
namespace ProcessorCoreTests

abbrev CState := CoreModel.State
abbrev CInput := CoreModel.Input

def modulus : Nat := 2^32
def ext (n bits : Nat) : Nat := if n < 2^(bits-1) then n else n+modulus-2^bits
def flag (b : Bool) : Nat := if b then 1 else 0

def bank (state : RV32I.Semantics.State) : Array Nat :=
  Array.ofFn fun k : Fin 32 => (RV32I.Semantics.read state.registers (BitVec.ofFin k)).toNat

def intentView : RV32I.Semantics.Intent → Array Nat
  | .load a size signed => #[0, a.toNat, size.bytes, flag signed, 0]
  | .store a size data => #[1, a.toNat, size.bytes, 0, data.toNat]
  | .fenceAll => #[2, 0, 0, 0, 0]

def replyView : CoreModel.DataReply → Array Nat
  | .success data => #[0, data.toNat]
  | .fault .misaligned => #[1, 0]
  | .fault .accessFault => #[2, 0]

def faultView (fault : CoreModel.Fault) : Array Nat :=
  let detail := match fault.cause with
    | .fetchMisaligned => #[0, fault.pc.toNat]
    | .fetchAccessFault => #[1, fault.pc.toNat]
    | .instruction .illegalInstruction => #[2, 0]
    | .instruction .environmentCall => #[3, 0]
    | .instruction .breakpoint => #[4, 0]
    | .instruction (.instructionAddressMisaligned target) => #[5, target.toNat]
    | .instruction (.loadFault .misaligned a) => #[6, a.toNat]
    | .instruction (.loadFault .accessFault a) => #[7, a.toNat]
    | .instruction (.storeFault .misaligned a) => #[8, a.toNat]
    | .instruction (.storeFault .accessFault a) => #[9, a.toNat]
  #[fault.pc.toNat, flag fault.word.isSome, fault.word.getD 0 |>.toNat] ++ detail

def completionView : CoreModel.Completion → Array Nat
  | .execute => #[0]
  | .fence => #[1]
  | .data path intent reply => #[2, match path with | .atomic => 0 | .deferred => 1] ++ intentView intent ++ replyView reply

def eventView : Option CoreModel.Event → Array Nat
  | none => #[]
  | some .reset => #[0]
  | some (.retired word completion after) => #[1, word.toNat] ++ completionView completion ++ #[after.pc.toNat] ++ bank after
  | some (.trapped fault completion) => #[2] ++ faultView fault ++ (completion.map completionView |>.getD #[])

def phaseNumber : CoreModel.Phase → Nat
  | .fetchRequest => 0 | .fetchResponse => 1 | .execute _ => 2
  | .dataRequest _ => 3 | .dataResponse _ => 4 | .fence _ => 5 | .terminal _ => 6

def stateView (state : CState) : Array Nat :=
  let suffix := match state.phase with
    | .execute word => #[word.toNat]
    | .dataRequest request | .dataResponse request =>
        let dest := match request with | .load _ _ d _ => d.toNat | _ => 0
        #[request.context.word.toNat, dest, request.context.state.pc.toNat] ++
          bank request.context.state ++ intentView request.intent
    | .fence context => #[context.word.toNat, context.state.pc.toNat] ++ bank context.state
    | .terminal fault => faultView fault
    | _ => #[]
  #[state.arch.pc.toNat, phaseNumber state.phase] ++ bank state.arch ++ suffix

structure Reference where
  pc : Nat := 0
  regs : Array Nat := Array.replicate 32 0
  phase : Nat := 0
  word : Nat := 0
  dest : Nat := 0
  address : Nat := 0
  size : Nat := 4
  signed : Bool := false
  store : Bool := false
  operand : Nat := 0
  fault : Array Nat := #[]
  deriving Inhabited, Repr

def Reference.intent (r : Reference) : Array Nat :=
  #[flag r.store, r.address, r.size, if r.store then 0 else flag r.signed, if r.store then r.operand else 0]

def Reference.view (r : Reference) : Array Nat :=
  #[r.pc, r.phase] ++ r.regs ++
  (if r.phase = 2 then #[r.word]
   else if r.phase = 3 || r.phase = 4 then #[r.word, r.dest, r.pc] ++ r.regs ++ r.intent
   else if r.phase = 5 then #[r.word, r.pc] ++ r.regs
   else if r.phase = 6 then r.fault else #[])

def retired (r : Reference) (pc dest value : Nat) (completion : Array Nat) : Reference × Array Nat :=
  let regs := if dest = 0 then r.regs else r.regs.set! dest (value%modulus)
  let after := {r with pc := pc%modulus, regs := regs, phase := 0}
  (after, #[1, r.word] ++ completion ++ #[after.pc] ++ regs)

def trapped (r : Reference) (known : Bool) (cause detail : Nat) (completion : Array Nat) : Reference × Array Nat :=
  let fault := #[r.pc, flag known, if known then r.word else 0, cause, detail]
  ({r with phase := 6, fault := fault}, #[2] ++ fault ++ completion)

def refFinish (r : Reference) (path : Nat) (reply : CoreModel.DataReply) : Reference × Array Nat :=
  let completion := #[2, path] ++ r.intent ++ replyView reply
  match reply with
  | .fault reason => trapped r true ((if r.store then 8 else 6) + (if reason = .accessFault then 1 else 0)) r.address completion
  | .success data =>
      let bits := r.size*8
      let selected := data.toNat % 2^bits
      let value := if r.signed then ext selected bits else selected
      retired r (r.pc+4) (if r.store then 0 else r.dest) value completion

/-- Numeric instruction decoding and array-based state update for the programs
below. It calls no production decode/execute/finish/ALU/address helper. The full
40-instruction semantic oracle is separately retained in RV32ISemantics.lean. -/
def refExecute (r : Reference) : Reference × Array Nat := Id.run do
  let w := r.word
  let opcode := w%128
  let rd := w/128%32
  let f3 := w/4096%8
  let rs1 := w/32768%32
  let rs2 := w/1048576%32
  let f7 := w/33554432
  let v1 := r.regs[rs1]!
  let v2 := r.regs[rs2]!
  let iimm := ext (w/1048576) 12
  let sequential := r.pc+4
  let jump := fun target dest =>
    if target%4 = 0 then retired r target dest sequential #[0]
    else trapped r true 5 target #[0]
  if opcode = 0x13 && f3 = 0 then return retired r sequential rd (v1+iimm) #[0]
  if opcode = 0x37 then return retired r sequential rd (w/4096*4096) #[0]
  if opcode = 0x17 then return retired r sequential rd (r.pc+w/4096*4096) #[0]
  if opcode = 0x33 && f3 = 0 && f7 = 0 then return retired r sequential rd (v1+v2) #[0]
  if opcode = 0x6f then
    let offset := w/2147483648*1048576 + w/2097152%1024*2 + w/1048576%2*2048 + w/4096%256*4096
    return jump ((r.pc+ext offset 21)%modulus) rd
  if opcode = 0x67 && f3 = 0 then return jump (((v1+iimm)%modulus)/2*2) rd
  if opcode = 0x63 && (f3 = 0 || f3 = 1) then
    let taken := if f3 = 0 then v1 == v2 else v1 != v2
    let offset := w/2147483648*4096 + w/128%2*2048 + w/33554432%64*32 + w/256%16*2
    return if taken then jump ((r.pc+ext offset 13)%modulus) 0 else retired r sequential 0 0 #[0]
  if opcode = 0x03 && (f3 = 0 || f3 = 1 || f3 = 2 || f3 = 4 || f3 = 5) then
    return ({r with
      phase := 3, dest := rd, address := (v1+iimm)%modulus,
      size := 2^(f3%4), signed := f3 < 2, store := false, operand := 0}, #[])
  if opcode = 0x23 && f3 < 3 then
    let immediate := ext (f7*32+w/128%32) 12
    return ({r with
      phase := 3, dest := 0, address := (v1+immediate)%modulus,
      size := 2^f3, signed := false, store := true, operand := v2}, #[])
  if opcode = 0x0f && f3 = 0 then return ({r with phase := 5}, #[])
  if w = 0x73 then return trapped r true 3 0 #[0]
  if w = 0x100073 then return trapped r true 4 0 #[0]
  return trapped r true 2 0 #[0]

def reference (input : CInput) (r : Reference) : Reference × Array Nat :=
  if input.reset then ({}, #[0]) else
  if r.phase = 0 then
    if r.pc%4 ≠ 0 then trapped r false 0 r.pc #[]
    else ({r with phase := if input.fetchReady then 1 else 0}, #[])
  else if r.phase = 1 then match input.fetchResponse with
    | none => (r, #[])
    | some .accessFault => trapped r false 1 r.pc #[]
    | some (.instruction word) => ({r with phase := 2, word := word.toNat}, #[])
  else if r.phase = 2 then refExecute r
  else if r.phase = 3 then match input.dataService with
    | none => (r, #[])
    | some .deferred => ({r with phase := 4}, #[])
    | some (.atomic reply) => refFinish r 0 reply
  else if r.phase = 4 then match input.dataResponse with
    | none => (r, #[])
    | some reply => refFinish r 1 reply
  else if r.phase = 5 then retired r (r.pc+4) 0 0 #[1]
  else (r, #[])

def ports (input : CInput) (state : CState) : Array Nat :=
  let o := CoreModel.observe input state
  #[flag o.cancel, flag o.fetch.isSome, (o.fetch.getD 0).toNat, flag o.fetchResponseReady,
    flag o.data.isSome] ++ (o.data.map intentView |>.getD #[]) ++
    #[flag o.dataResponseReady] ++ (o.terminal.map faultView |>.getD #[])

def referencePorts (input : CInput) (r : Reference) : Array Nat :=
  let fetch := !input.reset && r.phase == 0 && r.pc%4 == 0
  let data := !input.reset && r.phase == 3
  #[flag input.reset, flag fetch, if fetch then r.pc else 0,
    flag (!input.reset && r.phase == 1), flag data] ++ (if data then r.intent else #[]) ++
    #[flag (!input.reset && r.phase == 4)] ++ (if !input.reset && r.phase == 6 then r.fault else #[])

structure Machine where
  actual : CState := CoreModel.initial
  expected : Reference := {}
  edges : Nat := 0
  fetched : Nat := 0
  finished : Nat := 0
  canceled : Nat := 0
  nextId : Nat := 0
  outstanding : Option Nat := none
  seen : Array Nat := #[]

/-- The occurrence ledger is independent of value equality. Repeated raw
instructions and identical loads receive different monotonically increasing IDs. -/
def check (m : Machine) (input : CInput) : IO Machine := do
  unless stateView m.actual = m.expected.view do throw (IO.userError s!"Pre-state mismatch at {m.edges}: {stateView m.actual} vs {m.expected.view}")
  unless ports input m.actual = referencePorts input m.expected do throw (IO.userError s!"Ports mismatch at {m.edges}")
  let (expected, expectedEvent) := reference input m.expected
  let (actual, actualEvent) := CoreModel.tick input m.actual
  unless stateView actual = expected.view do throw (IO.userError s!"State mismatch at {m.edges}: {stateView actual} vs {expected.view}")
  unless eventView actualEvent = expectedEvent do throw (IO.userError s!"Event mismatch at {m.edges}: {eventView actualEvent} vs {expectedEvent}")
  let mut fetched := m.fetched
  let mut finished := m.finished
  let mut canceled := m.canceled
  let mut nextId := m.nextId
  let mut outstanding := m.outstanding
  let mut seen := m.seen
  if input.reset then
    if outstanding.isSome then canceled := canceled+1
    outstanding := none
  else
    if m.expected.phase = 1 then
      if let some (.instruction _) := input.fetchResponse then
        unless outstanding.isNone do throw (IO.userError "Duplicated fetch while instruction outstanding")
        outstanding := some nextId
        nextId := nextId+1
        fetched := fetched+1
    if expectedEvent[0]? = some 1 || (expectedEvent[0]? = some 2 && expectedEvent[2]? = some 1) then
      let some id := outstanding | throw (IO.userError "Retired/trapped without a fetched occurrence")
      unless !seen.contains id do throw (IO.userError "Duplicated instruction completion")
      seen := seen.push id
      outstanding := none
      finished := finished+1
  unless fetched = finished+canceled+(if outstanding.isSome then 1 else 0) do throw (IO.userError "Occurrence conservation failure")
  return ⟨actual, expected, m.edges+1, fetched, finished, canceled, nextId, outstanding, seen⟩

def runInputs (inputs : List CInput) : IO Machine := inputs.foldlM check {}

def raw (instruction : Instruction) : CoreModel.FetchReply := .instruction (encode instruction)
def fetch (instruction : Instruction) : List CInput :=
  [{fetchReady := true}, {fetchResponse := some (raw instruction)}, {}]

def lcg (n : Nat) : Nat := (1664525*n+1013904223)%modulus

/-- The environment schedules from its own numeric controller, never from
production offers. It loads/stores integer words only when the corresponding
completion edge is accepted; deferred requests save an address and store value.
ROM words come from the retained program below, rather than decoder output. -/
def program : Array Instruction := #[
  .aluImm .add 1 0 64, .aluImm .add 2 0 128,
  .store .word 1 2 0, .load .byte 3 1 0,
  .load .byteUnsigned 4 1 0, .store .half 1 2 2,
  .load .halfUnsigned 5 1 2, .load .word 0 1 0,
  .fence 31 17 15 3 3, .aluReg .add 6 4 5,
  .branch .eq 4 5 4, .ebreak,
  .aluImm .add 7 0 1, .aluImm .add 7 0 1,
  .jal 8 4, .ebreak, .aluImm .add 9 0 81,
  .jalr 10 9 0, .ebreak, .ebreak,
  .auipc 11 1, .ebreak]

def runProgram (seed : Nat) : IO Nat := do
  let mut m : Machine := {}
  let mut ram := Array.replicate 64 0
  let mut random := seed
  let mut writes := 0
  let mut reads := 0
  for _ in [:300] do
    random := lcg random
    let r := m.expected
    let reply : CoreModel.DataReply := if r.address%r.size ≠ 0 then .fault .misaligned
      else if r.address+r.size > 256 then .fault .accessFault
      else .success (BitVec.ofNat 32 (ram[r.address/4]! / 2^(8*(r.address%4))))
    let ready := random%4 != 0
    let input : CInput :=
      if r.phase = 0 then {fetchReady := ready, fetchResponse := some (.instruction 0x100073), dataResponse := some (.success 0xbad)}
      else if r.phase = 1 then {fetchResponse := if ready then some (if r.pc/4 < program.size then raw (program[r.pc/4]?.getD .ecall) else .accessFault) else none}
      else if r.phase = 3 then {
          dataService := if ready then some (if random%2 = 0 then .deferred else .atomic reply) else none,
          dataResponse := some (.success 0xbad)}
      else if r.phase = 4 then {dataResponse := if ready then some reply else none}
      else {fetchReady := true, fetchResponse := some (.instruction 0x100073), dataResponse := some (.success 0xbad)}
    let completion := (r.phase = 3 && input.dataService.isSome && random%2 != 0) || (r.phase = 4 && input.dataResponse.isSome)
    if completion then
      if let .success _ := reply then
        if r.store then
          let old := ram[r.address/4]!
          let shift := 2^(8*(r.address%4))
          let lane := 2^(8*r.size)
          ram := ram.set! (r.address/4) (old%shift + (r.operand%lane)*shift + old/(shift*lane)*(shift*lane))
          writes := writes+1
        else reads := reads+1
    m ← check m input
  unless m.expected.phase = 6 && m.expected.fault[3]? = some 4 do throw (IO.userError "Program did not reach its breakpoint")
  unless writes = 2 && reads = 4 && ram[16]! = 0x00800080 do throw (IO.userError s!"Program transaction count/value failure {writes}/{reads}/{ram[16]!}")
  unless m.expected.regs[3]! = 0xffffff80 && m.expected.regs[6]! = 256 && m.expected.regs[10]! = 72 do
    throw (IO.userError "Program integer register result mismatch")
  return m.edges

def fixtures : IO (Array Machine) := do
  let mut result : Array Machine := #[{}]
  result := result.push (← runInputs [{fetchReady := true}])
  for instruction in [Instruction.aluImm .add 1 0 128, .load .byte 0 0 64,
      .load .word 5 0 64, .store .half 0 0 66, .fence 31 17 15 3 3,
      .jal 7 1, .jal 7 16, .jalr 7 0 1, .jalr 7 0 3,
      .branch .ne 0 0 1, .branch .eq 0 0 1, .ecall, .ebreak] do
    let executing ← runInputs [{fetchReady := true}, {fetchResponse := some (raw instruction)}]
    result := result.push executing
    let issued ← check executing {}
    result := result.push issued
    if issued.expected.phase = 3 then
      result := result.push (← check issued {dataService := some .deferred})
  result := result.push (← runInputs [{fetchReady := true}, {fetchResponse := some (.instruction 0)}])
  for pc in [1, 2, 3, 0xfffffffc] do
    let actual : CState := ⟨⟨BitVec.ofNat 32 pc, fun _ => 0⟩, .fetchRequest⟩
    result := result.push ⟨actual, {pc := pc}, 0, 0, 0, 0, 0, none, #[]⟩
  return result

def directed : IO Nat := do
  let mut edges := 0
  for m in ← fixtures do
    for reset in [false, true] do
      for ready in [false, true] do
        for fetchReply in [none, some (.instruction 0x13), some (.instruction 0x100073), some .accessFault] do
          for service in [none, some .deferred, some (.atomic (.success 0)), some (.atomic (.success 0x80000080)),
              some (.atomic (.fault .misaligned)), some (.atomic (.fault .accessFault))] do
            for reply in [none, some (.success 0x80000080), some (.fault .misaligned), some (.fault .accessFault)] do
              let after ← check m ⟨reset, ready, fetchReply, service, reply⟩
              let _ ← check after {dataResponse := reply, fetchResponse := fetchReply}
              edges := edges+2
    -- Reset cancellation at every stage, then stale/unsolicited replies before
    -- a new request is admitted. No claim covers a provider violating reset
    -- and replaying a stale response after new untagged ownership is acquired.
    let reset ← check m {
      reset := true, fetchReady := true, fetchResponse := some (.instruction 0x13),
      dataService := some (.atomic (.success 0x1234)), dataResponse := some (.success 0x5678)}
    let _ ← check reset {fetchResponse := some (.instruction 0x100073), dataResponse := some (.success 0xbad)}
    edges := edges+2
  return edges

def mutant (mode : Nat) (input : CInput) (state : CState) : CState × Option CoreModel.Event :=
  let correct := CoreModel.tick input state
  if mode = 0 then
    match input.fetchResponse with
    | some (.instruction word) => (⟨state.arch, .execute word⟩, none)
    | _ => correct
  else if mode = 1 then
    match state.phase, input.dataResponse with
    | .dataRequest request, some reply =>
        CoreModel.acceptOutcome state (.data .deferred request.intent reply) (request.finish reply)
    | _, _ => correct
  else if mode = 2 then CoreModel.tick {input with reset := false} state
  else if mode = 3 then (⟨RV32I.Semantics.next state.arch, correct.1.phase⟩, correct.2)
  else if mode = 4 then CoreModel.tick {input with dataService := some .deferred} state
  else if mode = 5 then (⟨correct.1.arch, state.phase⟩, correct.2)
  else if mode = 6 then
    match state.phase with
    | .dataRequest (.load c _ _ _) => CoreModel.acceptOutcome state .execute (.retired c (RV32I.Semantics.next state.arch))
    | _ => correct
  else if mode = 7 then (⟨state.arch, .fetchResponse⟩, none)
  else if mode = 8 then (state, none)
  else if mode = 9 then
    match state.phase with
    | .terminal fault => (state, some (.trapped fault none))
    | _ => correct
  else if mode = 10 then (⟨RV32I.Semantics.next correct.1.arch, correct.1.phase⟩, correct.2)
  else if mode = 11 then (state, none)
  else if mode = 12 then
    match correct.2 with
    | some (.retired _ why after) => (correct.1, some (.retired 0 why after))
    | _ => correct
  else (⟨CoreModel.boot, state.phase⟩, some .reset)

def rejectMutation (mode : Nat) (m : Machine) (input : CInput) : IO Unit := do
  let _ ← check m input
  let expected := reference input m.expected
  let wrong := mutant mode input m.actual
  unless stateView wrong.1 ≠ expected.1.view || eventView wrong.2 ≠ expected.2 do
    throw (IO.userError s!"Controller semantic mutation {mode} escaped")

def mutations : IO Nat := do
  let load ← runInputs (fetch (.load .byte 0 0 64))
  let wait ← check load {dataService := some .deferred}
  let execute ← runInputs [{fetchReady := true}, {fetchResponse := some (raw (.aluImm .add 1 0 128))}]
  let terminal ← runInputs (fetch .ebreak)
  let misaligned : Machine := {actual := ⟨⟨2, fun _ => 0⟩, .fetchRequest⟩, expected := {pc := 2}}
  let fetchWait ← runInputs [{fetchReady := true}]
  let fence ← runInputs (fetch (.fence 31 17 15 3 3))
  rejectMutation 0 {} {fetchResponse := some (.instruction 0x100073)}
  rejectMutation 1 load {dataService := some .deferred, dataResponse := some (.success 0x80)}
  rejectMutation 2 wait {reset := true, dataResponse := some (.success 0x80)}
  rejectMutation 3 load {}
  rejectMutation 4 load {dataService := some (.atomic (.success 0x80))}
  rejectMutation 5 execute {}
  rejectMutation 6 load {}
  rejectMutation 7 misaligned {fetchReady := true}
  rejectMutation 8 fetchWait {fetchResponse := some .accessFault}
  rejectMutation 9 terminal {}
  rejectMutation 10 wait {dataResponse := some (.fault .accessFault)}
  rejectMutation 11 fence {}
  rejectMutation 12 execute {}
  rejectMutation 13 wait {reset := true}
  return 14

end ProcessorCoreTests

elab "#audit_processor_core" : command => do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "Pinwheel.Hardware.Processor.CoreModel." || name.toString.startsWith "ProcessorCoreTests." then
      count := count+1
      let axioms ← collectAxioms name
      let bad := axioms.filter fun a => a != ``propext && a != ``Classical.choice && a != ``Quot.sound
      unless bad.isEmpty do throwError "Unapproved core axiom {name}: {bad}"
  if count < 100 then throwError "Incomplete core declaration audit"
  logInfo m!"Core controller audit: {count} declarations, standard axioms only."

#audit_processor_core

def main : IO Unit := do
  let directed ← ProcessorCoreTests.directed
  let mut programs := 0
  for seed in [:32] do programs := programs + (← ProcessorCoreTests.runProgram (seed+1))
  let mutations ← ProcessorCoreTests.mutations
  IO.println s!"Core controller: {directed} adversarial protocol edges; {programs} independently scheduled integer/array program edges; {mutations} semantic corruption controls rejected."
