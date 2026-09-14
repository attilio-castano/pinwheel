import Pinwheel.Hardware.Reactive.Primitives

namespace Pinwheel.Hardware.Reactive

def runningValue (s : State) : Bool := s.mode != 0 && s.mode.toNat < 5

def terminalValues (i : Inputs) (s : State) : Samples :=
  Engine.Reactive.capture s.samples (Execution.getCapture (Execution.unpack i.current).terminal) i.incoming

def exitValues (i : Inputs) (s : State) : Samples := if s.mode = 3 then terminalValues i s else s.samples

def entryValues (i : Inputs) (s : State) : Samples := if runningValue s then exitValues i s else Vector.replicate 16 false

def sequentialValue (i : Inputs) (s : State) : Bool := s.mode != 3 || (Execution.unpack i.current).finish == 0

def targetValue (i : Inputs) (s : State) : BitVec 8 :=
  let d := Execution.unpack i.current
  if runningValue s then
    if sequentialValue i s then s.pc - 255
    else if d.finish = 1 then d.yes
    else if (terminalValues i s)[d.sample.toNat] then d.yes else d.no
  else 0

def rangeValue (i : Inputs) (s : State) : Bool :=
  if sequentialValue i s then s.pc.toNat < i.last.toNat else !(i.last.toNat < (targetValue i s).toNat)

def stopValue (mode : BitVec 3) (slots : Samples) (i : Inputs) : State := ⟨mode, 0, 0, 0, i.idle, slots⟩

def enterValue (word : BitVec 64) (address : BitVec 8) (slots : Samples) (i : Inputs) : State :=
  let d := Execution.unpack word
  if Execution.validValue word then
    if d.kind = 4 then stopValue 5 slots i else
      ⟨if d.kind = 0 then 1 else if d.kind = 1 then 2 else if d.kind = 2 then 3 else 4,
       address, d.duration, if d.kind = 3 then d.budget else 0, ⟨d.levels, d.enabled⟩,
       Engine.Reactive.capture slots (Execution.getCapture d.entry) i.incoming⟩
  else stopValue 7 slots i

def entryValue (i : Inputs) (s : State) : State :=
  enterValue i.successor (targetValue i s) (entryValues i s) i

def dispatchValue (i : Inputs) (s : State) : State :=
  if rangeValue i s then entryValue i s else stopValue 7 (exitValues i s) i

def decrementValue (s : State) : State := {s with remaining := s.remaining - 1}

def guardValue (i : Inputs) : Bool := (Execution.getCheck (Execution.unpack i.current).check).ready i.incoming

def readyValue (i : Inputs) : Bool :=
  let check := (Execution.unpack i.current).check
  i.incoming.getLsbD (check.extractLsb' 0 1).toNat == check[1]

def currentKindValue (kind : BitVec 3) (i : Inputs) : Bool :=
  Execution.validValue i.current && (Execution.unpack i.current).kind == kind

def progressValue (i : Inputs) (s : State) : State :=
  {s with remaining := s.remaining - 1, waitLeft := (Execution.unpack i.current).budget}

def retryValue (i : Inputs) (s : State) : State :=
  {s with remaining := (Execution.unpack i.current).duration, waitLeft := s.waitLeft - 1}

def advanceValue (i : Inputs) (s : State) : State :=
  if s.mode = 1 then
    if s.remaining = 0 then dispatchValue i s else decrementValue s
  else if s.mode = 2 then
    if currentKindValue 1 i then
      if readyValue i then dispatchValue i s
      else if s.remaining = 0 then stopValue 6 s.samples i else decrementValue s
    else stopValue 7 s.samples i
  else if s.mode = 3 then
    if currentKindValue 2 i && guardValue i then
      if s.remaining = 0 then dispatchValue i s else decrementValue s
    else stopValue 7 s.samples i
  else if currentKindValue 3 i then
    if guardValue i then
      if s.remaining = 0 then dispatchValue i s else progressValue i s
    else if s.waitLeft = 0 then stopValue 6 s.samples i else retryValue i s
  else stopValue 7 s.samples i

def stepValue (i : Inputs) (s : State) : State :=
  if i.reset then stopValue 0 (Vector.replicate 16 false) i
  else if runningValue s then advanceValue i s
  else if i.start then entryValue i s else s

/-- Two combinational instruction reads from a fixed, fully loaded typed program. -/
def feed (p : Program) (s : State) (reset start : Bool) (incoming : BitVec 2) : Inputs :=
  let base : Inputs := ⟨reset, start, incoming, p.idle, BitVec.ofFin p.last,
    Execution.encode (p.fetch s.pc.toFin), 4⟩
  {base with successor := Execution.encode (p.fetch (targetValue base s).toFin)}

end Pinwheel.Hardware.Reactive
