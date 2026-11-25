import Pinwheel.Program.StreamingI2CService
import Pinwheel.Program.StreamingReadySessionService
import Pinwheel.Program.StreamingReadyCustodySession
import Pinwheel.Program.StreamingReadyLoader

/-! A concrete host and I²C target for the 64-byte read. The scenario steps the
source session, a host that sends quad-link exchanges, and a target that
releases SCL and drives SDA from its payload, as one closed loop. It is the
witness that the service premises of the read-completion theorem can all hold
at once: every premise is checked on this one execution.

The loop also carries bookkeeping fields (the last two resolved samples and
target drives, the capture count and the count of accepted TX bits) that the
host and target never read; they let a single forward pass check the
premises. The custody trace is not carried: each clock checks that the bits it
accepts are the next slice of the host plan, and an induction rebuilds the
trace's accepted bits from that. -/
namespace Pinwheel.Program.StreamingI2CReadWitness
open Pinwheel Pinwheel.Program.StreamingReady

abbrev profile : I2cProfile := .standard
abbrev program : Program := (i2cImage profile).program

def payload : List (BitVec 8) := (List.range 64).map fun k => BitVec.ofNat 8 (37 * k + 5)

def bootPins : List Session.Pins := Streaming.BootPins.upload (i2cImage profile).words ⟨0, 0⟩ 0

def seed : Session.State 1 := Loader.seed bootPins

/-- Chronological TX bits from bit 63 down; unused low bits stay zero. -/
def packTop (bits : List Bool) : BitVec 64 :=
  (bits.foldl (fun (w : BitVec 64) b => (w <<< 1) ||| BitVec.ofNat 64 b.toNat) 0) <<< (64 - bits.length)

def nextSeq (s : Session.State 1) : BitVec 16 :=
  if s.host.lastValid then s.host.lastRequest.extractLsb' 144 16 + 1 else 0

def ownerTag (s : Session.State 1) : BitVec 32 := s.core.generation ++ s.core.transfer

def startRequest (s : Session.State 1) : BitVec 176 :=
  Streaming.BootPins.request 3 (nextSeq s) (1#16 ++ (585#16 ++ 0#96))

/-- Push as many planned TX bits as the queue has room for and pop RX. -/
def exchangeRequest (s : Session.State 1) : BitVec 176 :=
  let accepted := s.core.txAccepted.toNat
  let free := 2 - s.core.tx.count.val
  let room := 585 - accepted
  let (opcode, width) : BitVec 4 × Nat :=
    if room == 0 || free == 0 then (8, 0) else if free ≥ 2 && room > 32 then (10, 64) else (9, 32)
  let bits := (StreamingI2CRead.hostBits.drop accepted).take (min width room)
  Streaming.BootPins.request opcode (nextSeq s)
    (ownerTag s ++ (s.core.txAccepted ++ (s.host.exportEnd ++ packTop bits)))

def popRequest (s : Session.State 1) : BitVec 176 :=
  Streaming.BootPins.request 8 (nextSeq s) (ownerTag s ++ (s.core.txAccepted ++ (s.host.exportEnd ++ 0#64)))

def releaseRequest (s : Session.State 1) : BitVec 176 :=
  Streaming.BootPins.request 4 (nextSeq s) (ownerTag s ++ 0#96)

def transactionPins (word : BitVec 176) : List Session.Pins :=
  Streaming.BootPins.requestPins word ++ List.replicate 53 (Streaming.BootPins.idlePin 0) ++
    Streaming.BootPins.readPins 0

def released : I2C.Pins := ⟨.release, .release⟩

def framing (core : StreamingReady.State 1) : Bool :=
  core.phase == .fetch && (core.pc.toNat == 1 || core.pc.toNat == 6)

/-- The target releases SCL and drives SDA with the bit of the slot the engine
will capture next; it releases both lines at START and STOP. -/
def target (core : StreamingReady.State 1) : I2C.Pins :=
  if framing core then released else StreamingI2CRead.peerPins payload (585 - core.remaining.toNat) false

structure Loop where
  s : Session.State 1
  queue : List Session.Pins := []
  started : Bool := false
  idle : Bool := false
  raw1 : BitVec 2 := 0
  raw2 : BitVec 2 := 0
  peer1 : I2C.Pins := released
  peer2 : I2C.Pins := released
  captures : Nat := 0
  accepted : Nat := 0
  deriving DecidableEq

/-- The host's next pin, remaining transaction and START flag. -/
def Loop.host (l : Loop) : Session.Pins × List Session.Pins × Bool :=
  match l.queue with
  | p :: rest => (p, rest, l.started)
  | [] =>
    if !l.started then
      match transactionPins (startRequest l.s) with
      | p :: rest => (p, rest, true) | [] => ({}, [], true)
    else if l.s.core.phase == .completed || l.idle then ({}, [], true)
    else match transactionPins (exchangeRequest l.s) with
      | p :: rest => (p, rest, true) | [] => ({}, [], true)

def Loop.peer (l : Loop) : I2C.Pins := target l.s.core

def Loop.pin (l : Loop) : Session.Pins :=
  {l.host.1 with rawInputs := StreamingI2CRead.resolvedRaw l.s.core.pins l.peer}

def Loop.step (l : Loop) : Loop :=
  let pin := l.pin
  { s := l.s.step program false pin
    queue := l.host.2.1
    started := l.host.2.2
    idle := l.idle || l.s.core.phase == .completed
    raw1 := pin.rawInputs
    raw2 := l.raw1
    peer1 := l.peer
    peer2 := l.peer1
    captures := l.captures + (if l.s.core.captures then 1 else 0)
    accepted := l.accepted + (l.s.core.acceptedBits (l.s.command pin).runtime).length }

def runLoop : Nat → Loop → Loop
  | 0, l => l
  | n+1, l => runLoop n l.step

def initialLoop : Loop := {s := seed, queue := List.replicate 4 {rawInputs := 3}}

/-- START is accepted on this clock of the loop. -/
def startCut : Nat := 94

/-- The loop just after START, with the capture and accepted counts restarted. -/
def origin : Loop := {runLoop (startCut + 1) initialLoop with captures := 0, accepted := 0}

/-- Clocks after START until the loop is a fixed point. -/
def settle : Nat := 7505

/-- The first clock after START at which the engine has completed. -/
def completion : Nat := 7294

def traffic (n : Nat) : Session.Pins := (runLoop n origin).pin
def peer (n : Nat) : I2C.Pins := (runLoop n origin).peer

/-- The engine input of this clock: an ordinary runtime command other than
RESET, START or RELEASE. -/
def runtimeOK (l : Loop) : Bool :=
  let c := (l.s.command l.pin).runtime
  !c.initialize && c.command != 15 && c.command != 1 && c.command != 2 && c.command != 4 &&
    c.command != 3

/-- At START and STOP the target releases, and SDA moves while SCL is HIGH. -/
def framingOK (l : Loop) : Bool :=
  let q := l.s.core
  let next := (l.s.step program false l.pin).core
  !framing q || (l.peer == released &&
    (!(q.pc.toNat == 1) || (StreamingI2CRead.resolvedRaw q.pins l.peer == 3 &&
      StreamingI2CRead.resolvedRaw next.pins l.peer == 1)) &&
    (!(q.pc.toNat == 6) || (StreamingI2CRead.resolvedRaw q.pins l.peer == 1 &&
      StreamingI2CRead.resolvedRaw next.pins l.peer == 3)))

/-- At the last guard poll, the sample from two clocks earlier is ready. -/
def deadlineOK (t : Nat) (l : Loop) : Bool :=
  let q := l.s.core
  !(q.phase == .waiting && q.countdown == 0) || (2 ≤ t && q.current.guard.matches l.raw2)

/-- The target set up the captured slot two clocks before its capture. -/
def captureOK (t : Nat) (l : Loop) : Bool :=
  !l.s.core.captures || (2 ≤ t && l.peer2 == StreamingI2CRead.peerPins payload l.captures false)

/-- The bits accepted on this clock are the next slice of the host plan. -/
def acceptedOK (l : Loop) : Bool :=
  let bits := l.s.core.acceptedBits (l.s.command l.pin).runtime
  bits == (StreamingI2CRead.hostBits.drop l.accepted).take bits.length

/-- Per-clock premises, checked on every clock before `settle`. The engine has
not completed before `completion`. -/
def good (t : Nat) (l : Loop) : Bool :=
  runtimeOK l && framingOK l && deadlineOK t l && captureOK t l && acceptedOK l &&
    (completion ≤ t || l.s.core.phase != .completed)

def scan : Nat → Nat → Loop → Loop × Bool
  | 0, _, l => (l, true)
  | n+1, t, l => let rest := scan n (t+1) l.step; (rest.1, good t l && rest.2)

/-- From the settled loop: two pops and a RELEASE, accepted on clock `releaseAt`. -/
def drainRun (s : Session.State 1) : List Session.Pins :=
  let raw := fun (p : Session.Pins) => {p with rawInputs := StreamingI2CRead.resolvedRaw s.core.pins released}
  let first := (transactionPins (popRequest s)).map raw
  let a := s.run program false first
  let second := (transactionPins (popRequest a)).map raw
  let b := a.run program false second
  first ++ second ++ (transactionPins (releaseRequest b)).map raw

def releaseAt : Nat := 586

def drainPins (s : Session.State 1) : List Session.Pins := (drainRun s).take releaseAt
def releasePin (s : Session.State 1) : Session.Pins := (drainRun s)[releaseAt]?.getD {}

/-- Every pin is an ordinary runtime command other than RELEASE. -/
def ordinary : Session.State 1 → List Session.Pins → Bool
  | _, [] => true
  | s, p :: rest =>
    let d := (s.command p).runtime
    !d.initialize && d.command != 15 && d.command != 1 && d.command != 2 && d.command != 4 &&
      ordinary (s.step program false p) rest

def drainOK (s : Session.State 1) : Bool :=
  let final := s.run program false (drainPins s)
  let c := (final.command (releasePin s)).runtime
  ordinary s (drainPins s) && !c.initialize && c.command == 4 && final.core.canRelease c

/-- The loop after `settle` clocks; it no longer changes. -/
def settled : Loop := runLoop settle origin

/-! The settled loop is a fixed point. Deciding equality of whole loops is
slow in the kernel (the RX queue compared as a structure does not finish), so
the loops are compared field by field with queue storage compared as lists. -/

def sameQueue (a b : Streaming.Queue 1) : Bool :=
  decide (a.memory.toList = b.memory.toList) && decide (a.head = b.head) &&
    decide (a.tail = b.tail) && decide (a.count = b.count)

theorem sameQueue_iff {a b : Streaming.Queue 1} : sameQueue a b = true ↔ a = b := by
  constructor
  · intro h
    simp only [sameQueue, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨m, hd⟩, tl⟩, c⟩ := h
    cases a; cases b
    simp only [Streaming.Queue.mk.injEq] at *
    exact ⟨Vector.toList_inj.mp m, hd, tl, c⟩
  · rintro rfl; simp [sameQueue]

def sameCore (a b : StreamingReady.State 1) : Bool :=
  decide (a.phase = b.phase) && decide (a.pc = b.pc) && decide (a.current = b.current) &&
  decide (a.total = b.total) && decide (a.remaining = b.remaining) &&
  decide (a.countdown = b.countdown) && decide (a.cellBit = b.cellBit) &&
  sameQueue a.tx b.tx && sameQueue a.rx b.rx && decide (a.txShift = b.txShift) &&
  decide (a.txValid = b.txValid) && decide (a.rxPartial = b.rxPartial) &&
  decide (a.rxUsed = b.rxUsed) && decide (a.samplerFirst = b.samplerFirst) &&
  decide (a.samplerSecond = b.samplerSecond) && decide (a.pins = b.pins) &&
  decide (a.generation = b.generation) && decide (a.transfer = b.transfer) &&
  decide (a.txAccepted = b.txAccepted) && decide (a.txConsumed = b.txConsumed) &&
  decide (a.rxProduced = b.rxProduced) && decide (a.rxPopped = b.rxPopped)

theorem sameCore_iff {a b : StreamingReady.State 1} : sameCore a b = true ↔ a = b := by
  constructor
  · intro h
    simp only [sameCore, sameQueue_iff, Bool.and_eq_true, decide_eq_true_eq] at h
    cases a; cases b
    simp_all
  · rintro rfl; simp [sameCore, sameQueue_iff]

def sameLoop (a b : Loop) : Bool :=
  decide (a.s.host = b.s.host) && sameCore a.s.core b.s.core && decide (a.queue = b.queue) &&
  decide (a.started = b.started) && decide (a.idle = b.idle) && decide (a.raw1 = b.raw1) &&
  decide (a.raw2 = b.raw2) && decide (a.peer1 = b.peer1) && decide (a.peer2 = b.peer2) &&
  decide (a.captures = b.captures) && decide (a.accepted = b.accepted)

theorem sameLoop_iff {a b : Loop} : sameLoop a b = true ↔ a = b := by
  constructor
  · intro h
    simp only [sameLoop, sameCore_iff, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨ah, ac⟩, _⟩ := a
    obtain ⟨⟨bh, bc⟩, _⟩ := b
    simp_all
  · rintro rfl; simp [sameLoop, sameCore_iff]

/-! ### The checked facts

Each fact is its own kernel check: the kernel keeps its work until a
declaration ends, so one combined check would hold all of them at once. Each
recomputes the loop and costs about one to two minutes. -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every clock before `settle` meets the per-clock premises. -/
theorem scan_ok : (scan settle 0 origin).2 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem settled_same : sameLoop settled.step settled = true := by decide +kernel

theorem settled_fixed : settled.step = settled := sameLoop_iff.mp settled_same

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem settled_good : good settle settled = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem settled_reserve : settled.s.core.canReserve = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem settled_completed : settled.s.core.phase = .completed := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- From the settled loop, two pops and a RELEASE drain the transfer. -/
theorem settled_drain : drainOK settled.s = true := by decide +kernel

end Pinwheel.Program.StreamingI2CReadWitness
