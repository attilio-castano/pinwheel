import Pinwheel.Hardware.Buffered.Serial

/-! A record description of the serial protocol. Its Boolean scheduling,
natural-number field arithmetic and explicit state update are separate from
the expression trees used by hardware emission. Executable fixtures compare
this description with every actual typed register and core-facing port. -/
namespace Pinwheel.Hardware.Buffered.Serial
open Pinwheel.Hardware

structure Inputs where
  cold : Bool := false
  sck : Bool := false
  mosi : Bool := false
  csn : Bool := true
  rawInputs : BitVec 2 := 0
  status : Values Reactive.Output := fun _ => 0

def Inputs.values (i : Inputs) : Values Input
  | _, .initialize => BitVec.ofBool i.cold
  | _, .sck => BitVec.ofBool i.sck
  | _, .mosi => BitVec.ofBool i.mosi
  | _, .csn => BitVec.ofBool i.csn
  | _, .rawInputs => i.rawInputs
  | _, .status o => i.status o

structure State where
  sckPrev : Bool := false
  csnPrev : Bool := true
  active : Bool := false
  reading : Bool := false
  count : BitVec 9 := 0
  request : BitVec 160 := 0
  dispatch : Bool := false
  capture : Bool := false
  code : BitVec 4 := 0
  sequence : BitVec 16 := 0
  rejected : Bool := false
  response : BitVec 192 := 0
  ready : Bool := false
  deriving DecidableEq, Repr

def State.values (s : State) : Values Register
  | _, .sckPrev => BitVec.ofBool s.sckPrev
  | _, .csnPrev => BitVec.ofBool s.csnPrev
  | _, .active => BitVec.ofBool s.active
  | _, .reading => BitVec.ofBool s.reading
  | _, .count => s.count
  | _, .request => s.request
  | _, .dispatch => BitVec.ofBool s.dispatch
  | _, .capture => BitVec.ofBool s.capture
  | _, .code => s.code
  | _, .sequence => s.sequence
  | _, .rejected => BitVec.ofBool s.rejected
  | _, .response => s.response
  | _, .ready => BitVec.ofBool s.ready

def requestOpcode (s : State) : Nat := (s.request.toNat / 2^144) % 16
def requestField (s : State) (start width : Nat) : BitVec width :=
  BitVec.ofNat width (s.request.toNat / 2^start)
def requestCode (s : State) : BitVec 4 :=
  if s.count.toNat != 160 then 1
  else if s.request.toNat / 2^148 != 0xA71 then 2
  else
    let used : Option Nat := match requestOpcode s with
      | 0 => some 5 | 1 => some 98 | 2 => some 24
      | 3 => some 60 | 4 => some 32 | 6 => some 60
      | 7 => some 0 | 8 => some 0 | _ => none
    match used with
    | none => 3
    | some n => if (s.request.toNat % 2^128) / 2^n == 0 then 0 else 3

def deliver (i : Inputs) (s : State) : Bool :=
  !i.cold && s.dispatch && s.code == 0
def State.coreInput (s : State) (i : Inputs) : Values Reactive.Input
  | _, .initialize => BitVec.ofBool (i.cold || (deliver i s && requestOpcode s == 8))
  | _, .command => if deliver i s && requestOpcode s != 8 then requestField s 144 3 else 0
  | _, .address => if requestOpcode s == 6 then
      BitVec.ofNat 6 ((s.request.toNat / 2^56) % 16) else requestField s 92 6
  | _, .word => requestField s 0 64
  | _, .control => requestField s 64 24
  | _, .branch => if requestOpcode s == 6 then requestField s 0 56
      else BitVec.ofNat 56 ((s.request.toNat / 2^88) % 16)
  | _, .count => requestField s 0 7
  | _, .virtualSpan => requestField s 7 11
  | _, .idleLevels => requestField s 18 3
  | _, .idleEnabled => requestField s 21 3
  | _, .txData => requestField s 0 32
  | _, .txLength => requestField s 32 6
  | _, .rxCapacity => requestField s 38 6
  | _, .expectedGeneration => if requestOpcode s == 4 then requestField s 0 16
      else requestField s 44 16
  | _, .expectedTransfer => requestField s 16 16
  | _, .readIndex => if s.request.toNat / 2^144 == 0xA710 &&
      (s.request.toNat % 2^128) / 2^5 == 0 then requestField s 0 5 else 0
  | _, .rawInputs => i.rawInputs

def statusNat (i : Inputs) (s : State) : Nat :=
  (Reactive.outputs.foldl (fun (acc : Nat × Nat) ⟨w,o⟩ =>
    let v := if Reactive.outputLabel o == "rejected" then (BitVec.ofBool s.rejected).toNat
      else (i.status o).toNat
    (acc.1 + v*2^acc.2,acc.2+w)) (0,0)).1
def State.capturedResponse (s : State) (i : Inputs) : BitVec 192 :=
  let code := if s.code == 0 && s.rejected then 4 else s.code.toNat
  BitVec.ofNat 192 ((0x5A10+code)*2^176 + s.sequence.toNat*2^160 + statusNat i s)
def State.miso (s : State) (i : Inputs) : BitVec 1 :=
  BitVec.ofBool (!i.cold && s.active && s.reading && s.count.toNat < 192 &&
    s.response.getLsbD (191-s.count.toNat))
def State.readyOutput (s : State) (i : Inputs) : BitVec 1 :=
  BitVec.ofBool (!i.cold && s.ready)

/-- POR uses sampled current pins as the previous levels. A new CS assertion
is required after POR or after a blocked transaction. Counts saturate at 193. -/
def State.step (s : State) (i : Inputs) : State :=
  if i.cold then { sckPrev := i.sck, csnPrev := i.csn }
  else
    let start := s.csnPrev && !i.csn && !i.sck && !s.active && !s.dispatch && !s.capture
    let close := s.active && i.csn
    let requestClose := close && !s.reading
    let exactRead := close && s.reading && s.count == 192
    let take := s.active && !i.csn && i.sck && !s.sckPrev
    { sckPrev := i.sck
      csnPrev := i.csn
      active := if start then true else if close then false else s.active
      reading := if start then s.ready else s.reading
      count := if start then 0 else if take && s.count.toNat < 193 then s.count+1 else s.count
      request := if start && !s.ready then 0 else if take && !s.reading then
        BitVec.ofNat 160 (2*s.request.toNat + (BitVec.ofBool i.mosi).toNat) else s.request
      dispatch := requestClose
      capture := s.dispatch
      code := if requestClose then requestCode s else s.code
      sequence := if requestClose then
        (if s.count == 160 then requestField s 128 16 else 0) else s.sequence
      rejected := if s.dispatch then deliver i s && i.status .rejected == 1 else s.rejected
      response := if s.capture then s.capturedResponse i else s.response
      ready := if s.capture then true else if exactRead then false else s.ready }

end Pinwheel.Hardware.Buffered.Serial
