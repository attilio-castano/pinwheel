import Pinwheel.Program.StreamingEthernetCore
import Pinwheel.Program.StreamingEthernetFrame
import Pinwheel.Program.StreamingReadyBootPins
import Pinwheel.Program.StreamingReadyCustodySession

/-! The host drives a complete Ethernet transmit session through sampled
quad-link transactions. The first pair of TX words is staged while GO is low.
Each later request reaches admission after the second old word has entered
the shifter and stages both new words before the shifter runs out. -/
namespace Pinwheel.Program.StreamingEthernetSchedule
open StreamingReady StreamingEthernetCore StreamingEthernetFrame

structure Loader where
  host : Streaming.Host.State := {csnPrev := true}
  written : Bool := false
  installed : Bool := false

def loaderCore (s : Loader) : State 1 := { generation := if s.installed then 1 else 0 }

def loaderStatus (s : Loader) (pin : Session.Pins) : Streaming.Host.Status :=
  { (loaderCore s).status (s.written && !s.installed) (s.host.command (pin.host {})).runtime with
    valid := s.installed, rejected := false }

def loaderStep (s : Loader) (pin : Session.Pins) : Loader :=
  let command := (s.host.command (pin.host {})).runtime.command
  ⟨Streaming.Host.step (pin.host (loaderStatus s pin)) s.host,
    s.written || command == 1, s.installed || command == 2⟩

def bootPins : List Session.Pins := Streaming.BootPins.upload image.words idlePins 0

def bootState : Loader := bootPins.foldl loaderStep {}

def seed : Session.State 1 := ⟨bootState.host, loaderCore bootState⟩

def startRequest : BitVec 176 := Streaming.BootPins.request 3 7 (1#16 ++ (576#16 ++ 0#96))

def startPins : List Session.Pins := Streaming.BootPins.transaction startRequest 0

def startCut : Nat := 90
def beforeStart : List Session.Pins := startPins.take startCut
def startPin : Session.Pins := startPins[startCut]?.getD {}

def exchangeRequest (word : Nat) : BitVec 176 :=
  Streaming.BootPins.request 10 (BitVec.ofNat 16 (8 + word))
    (65537#32 ++ (BitVec.ofNat 16 (64 * word) ++ (0#16 ++ frameWords[word]?.getD 0)))

/-- The extra three idle ticks cover admission and the two TX staging beats. -/
def exchangePins (word : Nat) : List Session.Pins :=
  Streaming.BootPins.requestPins (exchangeRequest word) ++
    List.replicate 53 (Streaming.BootPins.idlePin 0) ++ Streaming.BootPins.readPins 0

def idlePinsFor (clocks : Nat) : List Session.Pins := List.replicate clocks (Streaming.BootPins.idlePin 0)

def afterStart : List Session.Pins := startPins.drop (startCut + 1) ++ exchangePins 0
def ready : Session.State 1 := seed.run program false beforeStart
def started : Session.State 1 := ready.step program false startPin
def preloaded : Session.State 1 := started.run program false afterStart

def firstSample : Nat := 18
def refillStart (round : Nat) : Nat := firstSample + 116 + 384 * round
def wireLength : Nat := 3473

def phyRaw (highWidth k : Nat) : BitVec 2 := BitVec.ofNat 2 (if k % 6 < highWidth then 3 else 2)

def withClock (highWidth first : Nat) (pins : List Session.Pins) : List Session.Pins :=
  pins.zipIdx.map (fun (p, k) => {p with rawInputs := phyRaw highWidth (first + k)})

def refillBlock (round : Nat) : List Session.Pins := exchangePins (round + 1) ++ idlePinsFor 136

def bodyPins (highWidth : Nat) : List Session.Pins :=
  withClock highWidth 0
    (idlePinsFor (refillStart 0) ++ (List.range 8).flatMap refillBlock ++ idlePinsFor 267)

def releaseRequest : BitVec 176 := Streaming.BootPins.request 4 17 (65537#32 ++ 0#96)

def releasePins : List Session.Pins := Streaming.BootPins.transaction releaseRequest 0

def releaseClocked (highWidth : Nat) : List Session.Pins := withClock highWidth wireLength releasePins

def wireAt (highWidth cut : Nat) : Session.State 1 := preloaded.run program false ((bodyPins highWidth).take cut)

def wireComplete (highWidth : Nat) : Session.State 1 := preloaded.run program false (bodyPins highWidth)

def released (highWidth : Nat) : Session.State 1 := (wireComplete highWidth).run program false (releaseClocked highWidth)

def sampleMatches (cut : Nat) (core : State 1) : Bool :=
  if cut ≥ firstSample && (cut - firstSample) % 6 == 0 then
    let bit := (cut - firstSample) / 6
    if bit < 576 then core.pins.enabled == 3 && core.pins.levels[1] &&
      core.pins.levels[0] == frameBits[bit]?.getD false
    else !core.pins.levels[1]
  else true

def refillMatches (cut : Nat) (s : Session.State 1) (pin : Session.Pins) : Bool :=
  if cut ≥ refillStart 0 + 90 && (cut - refillStart 0 - 90) % 384 == 0 then
    let round := (cut - refillStart 0 - 90) / 384
    if round < 8 then
      s.host.phase == 1 && s.host.request == exchangeRequest (round + 1) &&
      s.core.tx.count.val == 0 && s.core.txValid != 0 &&
      s.host.bulkAdmitted (s.hostInput false pin).status
    else true
  else true

def reservationMatches (cut : Nat) (core : State 1) : Bool :=
  if cut ≥ firstSample - 2 && (cut - (firstSample - 2)) % 6 == 0 then
    let bit := (cut - (firstSample - 2)) / 6
    if bit < 576 then core.phase == .boundary && core.canReserve &&
      core.txConsumed == BitVec.ofNat 16 bit
    else true
  else true

def runtimeOK (s : Session.State 1) (pin : Session.Pins) : Bool :=
  let cmd := (s.command pin).runtime
  !cmd.initialize && cmd.command != 15 && cmd.command != 1 && cmd.command != 2

def enableMatches (cut : Nat) (core : State 1) : Bool :=
  core.pins.enabled == 3 &&
    core.pins.levels[1] == decide (firstSample - 2 ≤ cut ∧ cut < wireLength)

def checkCut (s : Session.State 1) (cut : Nat) (pin : Session.Pins) : Bool :=
  sampleMatches cut s.core && (refillMatches cut s pin && reservationMatches cut s.core) &&
    enableMatches cut s.core && sampleMatches (cut + 1) s.core

def scan (observe : Session.State 1 → Nat → Session.Pins → Bool)
    (s : Session.State 1) (cut : Nat) : List Session.Pins → Session.State 1 × Bool
  | [] => (s, true)
  | pin :: rest =>
    let next := scan observe (s.step program false pin) (cut + 1) rest
    (next.1, runtimeOK s pin && observe s cut pin && next.2)

def checkPrelude : Bool :=
  let before := scan (fun _ _ _ => true) seed 0 beforeStart
  let after := scan (fun _ _ _ => true) started (startCut + 1) afterStart
  before.2 && runtimeOK ready startPin && after.2 &&
    (ready.command startPin).runtime.command == 3 &&
    (ready.command startPin).runtime.startCount == 576 && ready.core.canStart (ready.command startPin).runtime &&
    after.1.core.phase == .waiting && after.1.core.txAccepted == 64 && after.1.core.tx.count.val == 2 &&
    after.1.core.txConsumed == 0 && after.1.host.code == 0

def checkBody (highWidth : Nat) : Bool :=
  let (final, good) := scan checkCut preloaded 0 (bodyPins highWidth)
  let (after, releaseGood) := scan checkCut final wireLength (releaseClocked highWidth)
  good && releaseGood && final.core.phase == .completed && final.core.drained &&
    final.core.txAccepted == 576 && final.core.txConsumed == 576 &&
    final.host.phase == 0 && !final.host.ready && !final.host.active &&
    after.core.phase == .free && after.core.transfer == 1 &&
    after.host.code == 0 && !after.host.ready && !after.host.active

set_option maxRecDepth 30000 in
theorem prelude_checked : checkPrelude = true := by decide +kernel

set_option maxRecDepth 30000 in
theorem body_one_checked : checkBody 1 = true := by decide +kernel

set_option maxRecDepth 30000 in
theorem body_two_checked : checkBody 2 = true := by decide +kernel

theorem body_checked (width : h = 1 ∨ h = 2) : checkBody h = true := by
  rcases width with rfl | rfl
  · exact body_one_checked
  · exact body_two_checked

end Pinwheel.Program.StreamingEthernetSchedule
