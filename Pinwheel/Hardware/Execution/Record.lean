import Pinwheel.Engine.FetchProofs

/-! E64 execution records: fixed-width literal instructions for the 256-address/16-sample engine.
This is an internal execution layout, not a replacement for the PWL V0 load-image format. -/
namespace Pinwheel.Hardware.Execution
open Engine.Reactive

abbrev Operation := Instruction 255 15
abbrev Image := Program 255 15

structure Fields where
  kind : BitVec 3 := 0
  levels : BitVec 3 := 0
  enabled : BitVec 3 := 0
  duration : BitVec 8 := 0
  budget : BitVec 8 := 0
  check : BitVec 4 := 0
  entry : BitVec 6 := 0
  terminal : BitVec 6 := 0
  finish : BitVec 2 := 0
  sample : BitVec 4 := 0
  yes : BitVec 8 := 0
  no : BitVec 8 := 0
  deriving DecidableEq, Repr

def packRaw (f : Fields) (reserved : BitVec 1) : BitVec 64 :=
  reserved ++ f.no ++ f.yes ++ f.sample ++ f.finish ++ f.terminal ++ f.entry ++
    f.check ++ f.budget ++ f.duration ++ f.enabled ++ f.levels ++ f.kind

def pack (f : Fields) : BitVec 64 := packRaw f 0

def unpack (w : BitVec 64) : Fields :=
  ⟨w.extractLsb' 0 3, w.extractLsb' 3 3, w.extractLsb' 6 3, w.extractLsb' 9 8,
   w.extractLsb' 17 8, w.extractLsb' 25 4, w.extractLsb' 29 6, w.extractLsb' 35 6,
   w.extractLsb' 41 2, w.extractLsb' 43 4, w.extractLsb' 47 8, w.extractLsb' 55 8⟩

def captureBits : Option (Capture 15) → BitVec 6
  | none => 0
  | some c => (BitVec.ofFin c.destination : BitVec 4) ++ (BitVec.ofFin c.input : BitVec 1) ++ (1#1)

def getCapture (w : BitVec 6) : Option (Capture 15) :=
  if w[0] then some ⟨(w.extractLsb' 1 1).toFin, (w.extractLsb' 2 4).toFin⟩ else none

def checkBits (c : Check) : BitVec 4 := c.value ++ c.mask

def getCheck (w : BitVec 4) : Check := ⟨w.extractLsb' 0 2, w.extractLsb' 2 2⟩

def actionFields (a : Action 15) : Fields :=
  { levels := a.pins.levels, enabled := a.pins.enabled,
    duration := BitVec.ofFin a.durationMinusOne, entry := captureBits a.capture }

def finishFields (f : Finish 255 15) (base : Fields) : Fields :=
  match f with
  | .sequential => base
  | .jump pc => {base with finish := 1, yes := BitVec.ofFin pc}
  | .branch slot yes no =>
    {base with finish := 2, sample := BitVec.ofFin slot, yes := BitVec.ofFin yes, no := BitVec.ofFin no}

def fields : Operation → Fields
  | .action a => actionFields a
  | .wait w =>
    { kind := 1, levels := w.pins.levels, enabled := w.pins.enabled,
      duration := BitVec.ofFin w.budgetMinusOne,
      check := (0#2) ++ BitVec.ofBool w.condition.level ++ (BitVec.ofFin w.condition.input : BitVec 1) }
  | .checked a => finishFields a.finish
    {actionFields a.action with kind := 2, check := checkBits a.guard, terminal := captureBits a.terminalCapture}
  | .qualify q =>
    { kind := 3, levels := q.pins.levels, enabled := q.pins.enabled,
      duration := BitVec.ofFin q.durationMinusOne, budget := BitVec.ofFin q.budgetMinusOne,
      check := checkBits q.condition }
  | .halt => {kind := 4}

def Fields.pins (f : Fields) : Pins := ⟨f.levels, f.enabled⟩
def Fields.action (f : Fields) : Action 15 := ⟨f.pins, f.duration.toFin, getCapture f.entry⟩
def Fields.successor (f : Fields) : Option (Finish 255 15) :=
  if f.finish = 0 then some .sequential
  else if f.finish = 1 then some (.jump f.yes.toFin)
  else if f.finish = 2 then some (.branch f.sample.toFin f.yes.toFin f.no.toFin)
  else none

def Fields.instruction (f : Fields) : Option Operation :=
  if f.kind = 0 then some (.action f.action)
  else if f.kind = 1 then some (.wait ⟨f.pins, ⟨(f.check.extractLsb' 0 1).toFin, f.check[1]⟩, f.duration.toFin⟩)
  else if f.kind = 2 then do
    let finish ← f.successor
    return .checked ⟨f.action, getCheck f.check, getCapture f.terminal, finish⟩
  else if f.kind = 3 then some (.qualify ⟨f.pins, getCheck f.check, f.duration.toFin, f.budget.toFin⟩)
  else if f.kind = 4 then some .halt
  else none

def encode (i : Operation) : BitVec 64 := pack (fields i)

/-- All unused fields must be zero; no invalid opcode, finish tag, or noncanonical capture. -/
def decode (w : BitVec 64) : Option Operation := do
  let i ← (unpack w).instruction
  bif encode i == w then some i else none

end Pinwheel.Hardware.Execution
