import Lean
import Pinwheel.Hardware.Processor.SystemModelProofs

open Lean Elab Command Pinwheel.Hardware Pinwheel.Hardware.Processor
namespace ProcessorSystemTests

abbrev Word := BitVec 32
def modulus : Nat := 2^32
def flag (b : Bool) : Nat := if b then 1 else 0
def signed (x bits : Nat) : Int := if x < 2^(bits-1) then x else (x : Int)-2^bits
def wrap (x : Int) : Nat := (x % modulus).toNat
def signExtend (x bits : Nat) : Nat := wrap (signed x bits)
def bit (x k : Nat) : Nat := x / 2^k % 2

def layout : AddressMap.Layout 6 3 :=
  ⟨⟨0x10000,0x40000000,0x40000100,0x40000200⟩, by decide +kernel⟩

def encodeI (opcode f rd rs imm : Nat) : Nat :=
  imm%4096*2^20 + rs*2^15 + f*2^12 + rd*2^7 + opcode

def encodeS (f base source imm : Nat) : Nat :=
  imm%4096/32*2^25 + source*2^20 + base*2^15 + f*2^12 + imm%32*2^7 + 35

def firmware : Array Nat := #[
  0x000100b7,                         -- LUI x1, RAM base
  encodeI 19 0 2 0 3968,             -- -128
  encodeS 0 1 2 1,
  encodeI 3 0 3 1 1, encodeI 3 4 4 1 1,
  encodeI 19 0 2 0 4095, encodeS 1 1 2 2,
  encodeI 3 1 5 1 2, encodeI 3 5 6 1 2,
  encodeI 3 2 0 1 0, encodeI 3 2 7 1 0,
  encodeS 2 1 7 4, encodeS 0 1 4 4,
  0x40000537, encodeS 2 10 7 4,
  encodeI 3 2 8 10 0, encodeI 3 2 9 10 4,
  encodeI 19 0 11 10 256, encodeI 3 2 12 11 0,
  encodeI 19 0 13 10 512, encodeI 3 2 14 13 0,
  encodeI 19 0 15 0 65, encodeS 2 13 15 4,
  encodeI 3 2 16 13 0, encodeI 3 2 17 13 8,
  encodeI 19 0 18 0 12, encodeS 2 13 18 12,
  encodeI 3 2 19 13 0, encodeI 3 2 0 13 0,
  encodeI 3 0 20 0 0, encodeI 3 4 21 0 0,
  0x0ff0000f, 0x00100073]

def rom (program : Array Nat) : SystemModel.Rom 6 :=
  fun address => BitVec.ofNat 32 (program[address.toNat]?.getD 0)

def initialWords (seed : Nat) : Array Nat := Array.ofFn fun j : Fin 8 =>
  (0x92a4c611 + seed*0x01020305 + j.val*0x11223345)%modulus

def bank (arch : RV32I.Semantics.State) : Array Nat :=
  Array.ofFn fun k : Fin 32 => (RV32I.Semantics.read arch.registers (BitVec.ofFin k)).toNat

def intentView : RV32I.Semantics.Intent → Array Nat
  | .load a size sign => #[0,a.toNat,size.bytes,flag sign,0]
  | .store a size data => #[1,a.toNat,size.bytes,0,data.toNat]
  | .fenceAll => #[2,0,0,0,0]

def requestView : Memory.ByteAdapterModel.Request 3 → Array Nat
  | .read sign size address offset => #[0,flag sign,size.toNat,address.toNat,offset.toNat,0]
  | .store size address offset data => #[1,0,size.toNat,address.toNat,offset.toNat,data.toNat]

def replyView : CoreModel.DataReply → Array Nat
  | .success data => #[0,data.toNat]
  | .fault .misaligned => #[1,0]
  | .fault .accessFault => #[2,0]

def faultView (f : CoreModel.Fault) : Array Nat :=
  let reason := match f.cause with
    | .fetchMisaligned => #[0,f.pc.toNat] | .fetchAccessFault => #[1,f.pc.toNat]
    | .instruction .illegalInstruction => #[2,0] | .instruction .environmentCall => #[3,0]
    | .instruction .breakpoint => #[4,0] | .instruction (.instructionAddressMisaligned a) => #[5,a.toNat]
    | .instruction (.loadFault .misaligned a) => #[6,a.toNat]
    | .instruction (.loadFault .accessFault a) => #[7,a.toNat]
    | .instruction (.storeFault .misaligned a) => #[8,a.toNat]
    | .instruction (.storeFault .accessFault a) => #[9,a.toNat]
  #[f.pc.toNat,flag f.word.isSome,(f.word.getD 0).toNat] ++ reason

def completionView : CoreModel.Completion → Array Nat
  | .execute => #[0]
  | .fence => #[1]
  | .data path intent reply => #[2,if path == .atomic then 0 else 1] ++ intentView intent ++ replyView reply

def eventView : Option CoreModel.Event → Array Nat
  | none => #[] | some .reset => #[0]
  | some (.retired word why after) => #[1,word.toNat] ++ completionView why ++ #[after.pc.toNat] ++ bank after
  | some (.trapped fault why) => #[2] ++ faultView fault ++ (why.map completionView).getD #[]

def phaseView : CoreModel.Phase → Nat
  | .fetchRequest => 0 | .fetchResponse => 1 | .execute _ => 2
  | .dataRequest _ => 3 | .dataResponse _ => 4 | .fence _ => 5 | .terminal _ => 6

def coreView (s : CoreModel.State) : Array Nat :=
  let suffix := match s.phase with
    | .execute w => #[w.toNat]
    | .dataRequest r | .dataResponse r =>
      let rd := match r with | .load _ _ d _ => d.toNat | _ => 0
      #[r.context.word.toNat,rd,r.context.state.pc.toNat] ++ bank r.context.state ++ intentView r.intent
    | .fence c => #[c.word.toNat,c.state.pc.toNat] ++ bank c.state
    | .terminal f => faultView f
    | _ => #[]
  #[s.arch.pc.toNat,phaseView s.phase] ++ bank s.arch ++ suffix

def mmioView (s : MmioModel.State) : Array Nat :=
  #[s.gpioOut.toNat,s.timer.toNat,flag s.tx.isSome,(s.tx.getD 0).toNat,
    flag s.rx.isSome,(s.rx.getD 0).toNat,flag s.overrun,flag s.framing]

structure Ref where
  pc : Nat := 0
  regs : Array Nat := Array.replicate 32 0
  phase : Nat := 0
  word : Nat := 0
  rd : Nat := 0
  address : Nat := 0
  size : Nat := 4
  sign : Bool := false
  store : Bool := false
  operand : Nat := 0
  fault : Array Nat := #[]
  words : Array Nat
  q : Nat
  pending : Option (Array Nat) := none
  fetch : Option (Option Nat) := none
  gpio : Nat := 0
  timer : Nat := 0
  tx : Option Nat := none
  rx : Option Nat := none
  overrun : Bool := false
  framing : Bool := false
  deriving Repr

def Ref.intent (s : Ref) : Array Nat := #[flag s.store,s.address,s.size,flag s.sign,s.operand]
def Ref.core (s : Ref) : Array Nat :=
  #[s.pc,s.phase] ++ s.regs ++
  (if s.phase = 2 then #[s.word]
   else if s.phase = 3 || s.phase = 4 then #[s.word,s.rd,s.pc] ++ s.regs ++ s.intent
   else if s.phase = 5 then #[s.word,s.pc] ++ s.regs
   else if s.phase = 6 then s.fault else #[])
def Ref.mmio (s : Ref) : Array Nat :=
  #[s.gpio,s.timer,flag s.tx.isSome,s.tx.getD 0,flag s.rx.isSome,s.rx.getD 0,flag s.overrun,flag s.framing]

def retire (s : Ref) (rd value : Nat) (why : Array Nat) : Ref × Array Nat :=
  let regs := if rd = 0 then s.regs else s.regs.set! rd value
  let next := {s with regs,pc := (s.pc+4)%modulus,phase := 0}
  (next,#[1,s.word] ++ why ++ #[next.pc] ++ regs)

def trap (s : Ref) (known : Bool) (cause target : Nat) (why : Array Nat) : Ref × Array Nat :=
  let fault := #[s.pc,flag known,if known then s.word else 0,cause,target]
  ({s with phase := 6,fault},#[2] ++ fault ++ why)

def loadValue (size : Nat) (sign : Bool) (offset word : Nat) : Nat :=
  let selected := word / 2^(8*offset) % 2^(8*size)
  if sign then signExtend selected (8*size) else selected

def storeValue (size offset word data : Nat) : Nat :=
  let shift := 2^(8*offset)
  let mask := 2^(8*size)
  word%shift + data%mask*shift + word/(shift*mask)*(shift*mask)

/-- Numeric region selection, independent of AddressMap and all model adapters. -/
def route (s : Ref) : Nat × Nat :=
  if s.address%s.size != 0 then (0,1)
  else if s.address < 256 && s.address+s.size ≤ 256 then (if s.store then (0,2) else (1,s.address))
  else if 65536 ≤ s.address && s.address+s.size ≤ 65568 then (2,s.address-65536)
  else if 0x40000000 ≤ s.address && s.address+s.size ≤ 0x40000100 then
    if s.size = 4 then (3,(s.address-0x40000000)/4) else (0,2)
  else if 0x40000100 ≤ s.address && s.address+s.size ≤ 0x40000200 then
    if s.size = 4 then (4,(s.address-0x40000100)/4) else (0,2)
  else if 0x40000200 ≤ s.address && s.address+s.size ≤ 0x40000300 then
    if s.size = 4 then (5,(s.address-0x40000200)/4) else (0,2)
  else (0,2)

def device (i : SystemModel.Input) (s : Ref) (region reg : Nat) : Ref × Nat × Nat :=
  if region = 3 then
    if reg = 0 then if s.store then (s,2,0) else (s,0,i.gpio.toNat)
    else if reg = 1 then if s.store then ({s with gpio := s.operand},0,0) else (s,0,s.gpio)
    else (s,2,0)
  else if region = 4 then if reg = 0 && !s.store then (s,0,s.timer) else (s,2,0)
  else if reg = 0 then
    if s.store then (s,2,0) else (s,0,(if s.tx.isNone then 1 else 0)+(if s.rx.isSome then 2 else 0)+
      (if s.overrun then 4 else 0)+(if s.framing then 8 else 0))
  else if reg = 1 then
    if s.store && s.tx.isNone then ({s with tx := some (s.operand%256)},0,0) else (s,2,0)
  else if reg = 2 then
    if !s.store then match s.rx with | some byte => ({s with rx := none},0,byte) | none => (s,2,0)
    else (s,2,0)
  else if reg = 3 then
    if s.store then ({s with overrun := s.overrun && bit s.operand 2 == 0, framing := s.framing && bit s.operand 3 == 0},0,0) else (s,2,0)
  else (s,2,0)

def finish (s : Ref) (path error data : Nat) : Ref × Array Nat :=
  let why := #[2,path] ++ s.intent ++ #[error,data]
  if error != 0 then trap s true ((if s.store then 8 else 6)+(if error = 2 then 1 else 0)) s.address why
  else retire s (if s.store then 0 else s.rd) data why

/-- Independent numeric execution for the deliberately small firmware ISA subset.
Unknown encodings trap; no production decoder or Semantics result is consulted. -/
def execute (s : Ref) : Ref × Array Nat := Id.run do
  let op := s.word%128
  let rd := s.word/128%32
  let f := s.word/4096%8
  let rs1 := s.word/32768%32
  let rs2 := s.word/1048576%32
  let left := s.regs[rs1]!
  if op = 55 then return retire s rd (s.word/4096*4096) #[0]
  if op = 19 && f = 0 then return retire s rd (wrap ((left : Int)+signed (s.word/1048576) 12)) #[0]
  if op = 3 && (f = 0 || f = 1 || f = 2 || f = 4 || f = 5) then
    return ({s with phase := 3,rd,address := wrap ((left : Int)+signed (s.word/1048576) 12), size := 2^(f%4),sign := f < 2,store := false,operand := 0},#[])
  if op = 35 && f < 3 then
    let imm := s.word/2^25*32 + s.word/128%32
    return ({s with phase := 3,rd := 0,address := wrap ((left : Int)+signed imm 12), size := 2^f,sign := false,store := true,operand := s.regs[rs2]!},#[])
  if op = 15 && f = 0 then return ({s with phase := 5},#[])
  if op = 103 && f = 0 then
    let target := wrap ((left : Int)+signed (s.word/1048576) 12)/2*2
    if target%4 != 0 then return trap s true 5 target #[0]
    let done := retire s rd ((s.pc+4)%modulus) #[0]
    let next := {done.1 with pc := target}
    return (next,#[1,s.word,0,target] ++ next.regs)
  if s.word = 0x00100073 then return trap s true 4 0 #[0]
  if s.word = 0x00000073 then return trap s true 3 0 #[0]
  return trap s true 2 0 #[0]

structure Edge where
  after : Ref
  event : Array Nat
  accepted : Option (Array Nat) := none
  completed : Option (Array Nat) := none
  mmio : Option (Array Nat) := none
  write : Option (Nat × Nat) := none
  deriving Repr

def cpu (program : Array Nat) (i : SystemModel.Input) (s : Ref) : Edge := Id.run do
  if s.phase = 0 then
    if s.pc%4 != 0 then let t := trap s false 0 s.pc #[]; return {after := t.1,event := t.2}
    return {after := {s with phase := 1,fetch := some (if s.pc < 256 then some (program[s.pc/4]?.getD 0) else none)},event := #[]}
  if s.phase = 1 then
    if let some fetched := s.fetch then
      if let some word := fetched then return {after := {s with phase := 2,word,fetch := none},event := #[]}
      let t := trap {s with fetch := none} false 1 s.pc #[]
      return {after := t.1,event := t.2}
    return {after := s,event := #[]}
  if s.phase = 2 then let t := execute s; return {after := t.1,event := t.2}
  if s.phase = 3 then
    let (region,relative) := route s
    if region = 2 then
      let physical := #[flag s.store,flag s.sign,if s.size = 1 then 0 else if s.size = 2 then 1 else 2,
        relative/4,relative%4,s.operand]
      return {after := {s with phase := 4,pending := some physical,q := s.words[relative/4]!}, event := #[],accepted := some physical}
    if region = 0 then let t := finish s 0 relative 0; return {after := t.1,event := t.2}
    if region = 1 then
      let t := finish s 0 0 (loadValue s.size s.sign (relative%4) (program[relative/4]?.getD 0))
      return {after := t.1,event := t.2}
    let (current,error,data) := device i s region relative
    let t := finish current 0 error data
    return {after := t.1,event := t.2,mmio := some #[region-3,relative,flag s.store,s.operand,error,data]}
  if s.phase = 4 then
    let physical := s.pending.getD #[]
    let address := physical[3]!
    let offset := physical[4]!
    let data := if s.store then 0 else loadValue s.size s.sign offset s.q
    let written := storeValue s.size offset s.q s.operand
    let words := if s.store then s.words.set! address written else s.words
    let t := finish {s with words,pending := none} 1 0 data
    return {after := t.1,event := t.2,completed := some (physical ++ #[if s.store then 1 else 0,data]), write := if s.store then some (address,written) else none}
  if s.phase = 5 then let t := retire s 0 0 #[1]; return {after := t.1,event := t.2}
  return {after := s,event := #[]}

def reference (program : Array Nat) (i : SystemModel.Input) (s : Ref) : Edge := Id.run do
  if i.reset then return {after := {words := s.words,q := s.q},event := #[0]}
  let e := cpu program i s
  let current := {e.after with timer := (s.timer+1)%modulus, tx := if i.txComplete && s.tx.isSome then none else e.after.tx}
  let received := match i.rxArrival with
    | none => current
    | some byte => if current.rx.isNone then {current with rx := some byte.toNat} else {current with overrun := true}
  return {e with after := {received with framing := received.framing || i.framingError}}

def mmioResponseView : MmioModel.Response → Array Nat
  | .read data => #[0,data.toNat] | .stored => #[1,0]
  | .fault reason => #[2,match reason with | .registerHole => 0 | .direction => 1 | .txBusy => 2 | .rxEmpty => 3]

def mmioEventView : MmioModel.Event → Array Nat
  | .cpu r gpio response => #[0,match r.device with | .gpio => 0 | .timer => 1 | .uart => 2,
      r.word.toNat,flag r.write,r.data.toNat,gpio.toNat] ++ mmioResponseView response
  | .tick => #[1] | .txComplete byte => #[2,byte.toNat]
  | .receive byte accepted => #[3,byte.toNat,flag accepted]
  | .framingError => #[4] | .reset => #[5]

def expectedMmioEvents (i : SystemModel.Input) (before : Ref) (e : Edge) : List (Array Nat) := Id.run do
  if i.reset then return [#[5]]
  let mut events := []
  if let some request := e.mmio then
    let device := request[0]!
    let reg := request[1]!
    let fault := if (device = 0 && reg ≥ 2) || (device = 1 && reg != 0) || reg ≥ 4 then 0
      else if device = 2 && reg = 1 && before.store && before.tx.isSome then 2
      else if device = 2 && reg = 2 && !before.store && before.rx.isNone then 3 else 1
    let response := if request[4]! = 0 then #[if before.store then 1 else 0,request[5]!] else #[2,fault]
    events := [#[0,device,reg,flag before.store,before.operand,i.gpio.toNat] ++ response]
  events := events ++ [#[1]]
  if i.txComplete then if let some byte := before.tx then events := events ++ [#[2,byte]]
  if let some byte := i.rxArrival then
    let consumed := e.mmio.any fun r => r[0]! == 2 && r[1]! == 2 && !before.store && r[4]! == 0
    events := events ++ [#[3,byte.toNat,flag (before.rx.isNone || consumed)]]
  if i.framingError then events := events ++ [#[4]]
  return events

def ramEventView (e : Memory.ByteAdapterEffects.Event 3) : Array Nat :=
  requestView e.request ++ match e.response with
  | .read data => #[0,data.toNat] | .stored => #[1,0]
  | .fault fault => #[2,if fault == .misaligned then 0 else 1]

def fetchView : Option CoreModel.FetchReply → Option (Option Nat)
  | none => none | some .accessFault => some none | some (.instruction word) => some (some word.toNat)

def equalState (s : SystemModel.State 3) (r : Ref) : Bool :=
  coreView s.core == r.core && Array.ofFn (fun k : Fin 8 => (s.ram.memory.contents (BitVec.ofFin k)).toNat) == r.words &&
    s.ram.memory.q.toNat == r.q && s.ram.pending.map requestView == r.pending &&
    fetchView s.fetch == r.fetch && mmioView s.mmio == r.mmio

def portView (o : CoreModel.Output) : Array Nat :=
  #[flag o.cancel,flag o.fetch.isSome,(o.fetch.getD 0).toNat,flag o.fetchResponseReady,
    flag o.data.isSome,flag o.dataResponseReady] ++
    (o.data.map intentView).getD #[] ++ (o.terminal.map faultView).getD #[]

def expectedPorts (i : SystemModel.Input) (s : Ref) : Array Nat :=
  if i.reset then #[1,0,0,0,0,0] else
  #[0,flag (s.phase == 0 && s.pc%4 == 0),if s.phase = 0 && s.pc%4 = 0 then s.pc else 0,
    flag (s.phase == 1),flag (s.phase == 3),flag (s.phase == 4)] ++
    (if s.phase = 3 then s.intent else #[]) ++ (if s.phase = 6 then s.fault else #[])

structure Machine where
  actual : SystemModel.State 3
  expected : Ref
  cycle : Nat := 0
  nextId : Nat := 0
  pendingId : Option Nat := none
  settled : List Nat := []
  completed : Nat := 0
  canceled : Nat := 0
  writes : Nat := 0
  mmio : Nat := 0
  retired : Nat := 0
  x0Loads : Nat := 0

def start (seed : Nat) : Machine :=
  let words := initialWords seed
  let q := (0xfedcba98+seed)%modulus
  {actual := SystemModel.initial (fun a => BitVec.ofNat 32 words[a.toNat]!) (BitVec.ofNat 32 q),
   expected := {words,q}}

def check (program : Array Nat) (m : Machine) (i : SystemModel.Input) : IO Machine := do
  unless equalState m.actual m.expected do throw (IO.userError s!"Pre-state mismatch at {m.cycle}")
  let e := reference program i m.expected
  let image := rom program
  let o := SystemModel.observe layout image i m.actual
  let next := SystemModel.step layout image i m.actual
  unless equalState next e.after do
    throw (IO.userError s!"Post-state mismatch at {m.cycle}, phase {m.expected.phase}, pc {m.expected.pc}\ncore {coreView next.core}\nexpected {e.after.core}\nMMIO {mmioView next.mmio} / {e.after.mmio}\nRAMQ {next.ram.memory.q.toNat} / {e.after.q}")
  unless eventView o.core.event == e.event do throw (IO.userError s!"Core event mismatch {m.cycle}: {eventView o.core.event} / {e.event}")
  unless portView o.core == expectedPorts i m.expected && o.gpio.toNat == (if i.reset then 0 else m.expected.gpio) &&
      o.tx.map BitVec.toNat == (if i.reset then none else m.expected.tx) do
    throw (IO.userError s!"Output mismatch {m.cycle}")
  let events := SystemModel.events layout image i m.actual
  unless events.ram.map ramEventView == e.completed.toList do throw (IO.userError s!"RAM event mismatch {m.cycle}")
  unless events.mmio.map mmioEventView == expectedMmioEvents i m.expected e do
    throw (IO.userError s!"Device event mismatch {m.cycle}: {events.mmio.map mmioEventView} / {expectedMmioEvents i m.expected e}")
  let accepted := Memory.ByteAdapterModel.acceptedRequests (SystemModel.ramInput layout image i m.actual) m.actual.ram
  unless accepted.map requestView == e.accepted.toList do throw (IO.userError s!"RAM acceptance mismatch {m.cycle}")
  let writes := SystemModel.committedWrites layout image i m.actual
  unless writes.map (fun (a,d) => (a.toNat,d.toNat)) == e.write.toList do throw (IO.userError s!"Write edge mismatch {m.cycle}")
  let mut nextId := m.nextId
  let mut pendingId := m.pendingId
  let mut settled := m.settled
  let mut completed := m.completed
  let mut canceled := m.canceled
  if i.reset || e.completed.isSome then
    if let some id := pendingId then
      settled := settled ++ [id]
      pendingId := none
      if i.reset then canceled := canceled+1 else completed := completed+1
    else if e.completed.isSome then throw (IO.userError "Completion without occurrence ownership")
  if e.accepted.isSome then
    unless pendingId.isNone do throw (IO.userError "Overlapping RAM ownership")
    pendingId := some nextId
    nextId := nextId+1
  unless settled ++ pendingId.toList == List.range nextId do throw (IO.userError "Occurrence loss, duplication or reordering")
  unless pendingId.isSome == next.ram.pending.isSome do throw (IO.userError "Ledger/provider ownership mismatch")
  let isRetire := e.event[0]? == some 1
  return {m with actual := next,expected := e.after,cycle := m.cycle+1,nextId,pendingId,settled,completed,canceled, writes := m.writes + flag e.write.isSome, mmio := m.mmio + flag e.mmio.isSome, retired := m.retired + flag isRetire, x0Loads := m.x0Loads + flag (isRetire && m.expected.phase ≥ 3 && m.expected.phase ≤ 4 && !m.expected.store && m.expected.rd == 0)}

def environment (cycle : Nat) (s : Ref) : SystemModel.Input :=
  {gpio := BitVec.ofNat 32 (0x87654321+cycle),
   txComplete := s.phase == 3 && s.address == 0x4000020c,
   rxArrival := if cycle = 0 then some 0x80 else if cycle = 1 then some 0x80
     else if s.phase == 3 && s.address == 0x40000208 then some 0x81 else none,
   framingError := cycle == 1 || (s.phase == 3 && s.address == 0x4000020c)}

def runFirmware (seed : Nat) : IO Machine := do
  let mut m := start seed
  for _ in [:250] do
    m ← check firmware m (environment m.cycle m.expected)
  unless m.expected.phase = 6 && m.expected.fault[3]! = 4 do throw (IO.userError "Firmware did not reach EBREAK")
  let regs := m.expected.regs
  unless regs[3]! = 0xffffff80 && regs[4]! = 128 && regs[5]! = 0xffffffff && regs[6]! = 65535 &&
      regs[0]! = 0 && regs[17]! = 128 && regs[20]! = 0xffffffb7 && regs[21]! = 183 do
    throw (IO.userError "Firmware independent result assertion failed")
  unless m.completed = 10 && m.writes = 4 && m.mmio = 11 && m.retired = 32 && m.x0Loads = 2 &&
      m.expected.rx == some 0x81 && m.expected.tx.isNone && m.expected.framing && !m.expected.overrun do
    throw (IO.userError s!"Firmware coverage failed {m.completed}/{m.writes}/{m.mmio}/{m.retired}/{m.x0Loads}")
  return m

def faultPrograms : Array (Array Nat × Nat) := #[
  (#[encodeS 2 0 0 0],9),
  (#[0x000100b7,encodeI 3 1 2 1 1],6),
  (#[0x000100b7,encodeS 2 1 0 2],8),
  (#[0x400000b7,encodeI 3 0 0 1 0],7),
  (#[0x400000b7,encodeS 2 1 0 0],9),
  (#[0x400000b7,encodeI 3 2 2 1 8],7),
  (#[0x400000b7,encodeI 19 0 1 1 512,encodeI 19 0 2 0 65,encodeS 2 1 2 4,encodeS 2 1 2 4],9),
  (#[0x400000b7,encodeI 19 0 1 1 512,encodeI 3 2 0 1 8],7),
  (#[0x000100b7,encodeI 103 0 0 1 0],1),
  (#[encodeI 103 0 0 0 3],5),
  (#[0x000100b7,encodeI 3 0 0 1 32],7),
  (#[0x000100b7,encodeS 0 1 0 32],9),
  (#[0x000100b7,encodeI 3 0 2 1 31,0x00100073],4),
  (#[0x000100b7,encodeI 3 5 2 1 30,0x00100073],4),
  (#[0xfffff0b7,encodeI 3 2 0 1 4092],7),
  (#[0],2),(#[0x00000073],3)]

def faults : IO Nat := do
  let mut count : Nat := 0
  for (program,cause) in faultPrograms do
    for seed in [:4] do
      let mut m := start seed
      for _ in [:36] do m ← check program m {}
      unless m.expected.phase = 6 && m.expected.fault[3]! = cause do
        throw (IO.userError s!"Expected fault {cause}, got {m.expected.fault}")
      count := count+m.cycle
  return count

def resetCuts : IO Nat := do
  let mut preRun := start 9
  let mut count : Nat := 0
  let mut cancellations := 0
  for cut in [:160] do
    let reset : SystemModel.Input := {reset := true,gpio := 0xffffffff,txComplete := true,rxArrival := some 0xff,framingError := true}
    let mut restart ← check firmware preRun reset
    cancellations := cancellations + (restart.canceled-preRun.canceled)
    for n in [:160] do restart ← check firmware restart (environment n restart.expected)
    unless restart.expected.phase = 6 && restart.expected.fault[3]! = 4 do
      throw (IO.userError s!"Reset recovery failed at cut {cut}")
    count := count+161
    preRun ← check firmware preRun (environment cut preRun.expected)
  unless cancellations = 10 do throw (IO.userError s!"Expected cancellation of every pending RAM occurrence, got {cancellations}")
  return count+160

def dirtyReset : IO Nat := do
  let mut count := 0
  for seed in [:32] do
    let base := start seed
    let values := Array.ofFn fun k : Fin 32 => if k.val = 0 then 0 else (seed*97+k.val*0x10204081)%modulus
    let word := (seed*0x81532621)%modulus
    let pending := #[1,0,3,seed%8,seed%4,0xfedcba98]
    let expected : Ref := {base.expected with pc := 0xfffffffd,regs := values,phase := 2,word, pending := some pending,fetch := some (some 0x12345678),gpio := 0xaabbccdd,timer := 0xffffffff, tx := some 65,rx := some 65,overrun := true,framing := true}
    let actual : SystemModel.State 3 :=
      {core := ⟨⟨0xfffffffd,fun k => BitVec.ofNat 32 values[k.val+1]!⟩,.execute (BitVec.ofNat 32 word)⟩,
       ram := {base.actual.ram with pending := some (.store 3 (BitVec.ofNat 3 seed) (BitVec.ofNat 2 seed) 0xfedcba98)},
       mmio := ⟨0xaabbccdd,0xffffffff,some 65,some 65,true,true⟩,fetch := some (.instruction 0x12345678)}
    let dirty : Machine := {actual,expected,nextId := 1,pendingId := some 0}
    let mut restarted ← check firmware dirty {reset := true,rxArrival := some 0xff,txComplete := true,framingError := true}
    for n in [:160] do restarted ← check firmware restarted (environment n restarted.expected)
    unless restarted.expected.phase = 6 && restarted.canceled = 1 do
      throw (IO.userError "Arbitrary dirty-state reset failed")
    count := count+161
  return count

/-- Actual component-composition faults; each witness first passes unchanged. -/
def mutant (mode : Nat) (program : Array Nat) (i : SystemModel.Input) (s : SystemModel.State 3) :
    SystemModel.State 3 × SystemModel.Output := Id.run do
  let image := rom program
  let next := SystemModel.step layout image i s
  let out := SystemModel.observe layout image i s
  if mode = 0 then
    let offered := (SystemModel.ramInput layout image i s).offered
    if let some request := offered then
      if let some (address,data) := request.write (s.ram.memory.contents request.address) then
        let memory := {next.ram.memory with contents := fun a => if a = address then data else next.ram.memory.contents a}
        return ({next with ram := {next.ram with memory}},out)
  if mode = 1 && i.reset then
    return ({next with ram := {next.ram with memory := {next.ram.memory with contents := fun _ => 0}}},out)
  if mode = 2 then
    let input := {SystemModel.coreInput layout image i s with dataResponse := some (.success 0)}
    return ({next with core := CoreModel.step input s.core},{out with core := CoreModel.observe input s.core})
  if mode = 3 then
    return ({next with mmio := {next.mmio with gpioOut := s.mmio.gpioOut}},out)
  if mode = 4 then
    let input := {SystemModel.coreInput layout image i s with dataService := some (.atomic (.success (s.mmio.timer+1)))}
    return ({next with core := CoreModel.step input s.core},{out with core := CoreModel.observe input s.core})
  if mode = 5 then return ({next with fetch := some (.instruction 0)},out)
  if mode = 6 && i.reset then return ({next with ram := s.ram},out)
  if mode = 7 && i.reset then return ({next with mmio := s.mmio},out)
  if mode = 8 then return ({next with mmio := {next.mmio with framing := false}},out)
  if mode = 9 then return ({next with ram := {next.ram with memory := {next.ram.memory with q := 0}}},out)
  return (next,out)

def reject (mode : Nat) (m : Machine) (i : SystemModel.Input) : IO Unit := do
  let _ ← check firmware m i
  let expected := reference firmware i m.expected
  let wrong := mutant mode firmware i m.actual
  unless !equalState wrong.1 expected.after || eventView wrong.2.core.event != expected.event do
    throw (IO.userError s!"System composition mutant {mode} escaped")

def mutations : IO Nat := do
  let mut m := start 7
  let mut seen : List Nat := []
  for n in [:160] do
    let i := environment n m.expected
    if m.expected.phase = 3 && m.expected.store && (route m.expected).1 = 2 && !seen.contains 0 then
      reject 0 m i; seen := seen ++ [0]
    if m.expected.phase = 4 && !m.expected.store && m.expected.rd != 0 && !seen.contains 2 then
      reject 2 m i; seen := seen ++ [2]
    if m.expected.phase = 3 && m.expected.address = 0x40000004 && m.expected.store then
      reject 3 m i; seen := seen ++ [3]
    if m.expected.phase = 3 && m.expected.address = 0x40000100 then
      reject 4 m i; seen := seen ++ [4]
    if n = 0 then reject 5 m i; seen := seen ++ [5]
    if m.expected.phase = 4 && !seen.contains 6 then
      reject 1 m {reset := true}; reject 6 m {reset := true}
      reject 9 m i; seen := seen ++ [1,6,9]
    if m.expected.phase = 3 && m.expected.address = 0x4000020c then
      reject 7 m {reset := true}; reject 8 m i; seen := seen ++ [7,8]
    m ← check firmware m i
  unless seen.length = 10 do throw (IO.userError s!"Missing corruption controls {seen}")
  return seen.length

end ProcessorSystemTests

elab "#audit_system_model" : command => do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "Pinwheel.Hardware.Processor.SystemModel." ||
       name.toString.startsWith "ProcessorSystemTests." then
      count := count+1
      let axioms ← collectAxioms name
      let bad := axioms.filter fun a => a != ``propext && a != ``Classical.choice && a != ``Quot.sound
      unless bad.isEmpty do throwError "Unapproved system model axiom {name}: {bad}"
  if count < 100 then throwError "Incomplete system model audit"
  logInfo m!"System model audit: {count} declarations, standard axioms only."

#audit_system_model

def main : IO Unit := do
  let mut firmwareEdges := 0
  for seed in [:32] do
    let m ← ProcessorSystemTests.runFirmware seed
    firmwareEdges := firmwareEdges+m.cycle
  let faults ← ProcessorSystemTests.faults
  let resets ← ProcessorSystemTests.resetCuts
  let dirty ← ProcessorSystemTests.dirtyReset
  let mutants ← ProcessorSystemTests.mutations
  IO.println s!"Closed system model: {firmwareEdges} firmware edges, {faults} fault/boundary edges, {resets} reset/restart edges, {dirty} dirty-state reset/restart edges, {mutants} actual composition mutants rejected."
