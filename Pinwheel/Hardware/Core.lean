import Pinwheel.Hardware.CoreState
import Pinwheel.Hardware.Store

namespace Pinwheel.Hardware.Core

abbrev E := Expr Input Register
abbrev Bank := {w : Nat} → Register w → E w

def hold : Bank := fun r => .reg r

def stopped (reason : BitVec 2) (clear : Bool) : Bank
  | _, .status => .lit reason
  | _, .pc => .lit 0
  | _, .remaining => .lit 0
  | _, .timerActive => .lit 0
  | _, .levels => .reg .idle
  | _, .sample k => if clear then .lit 0 else .reg (.sample k)
  | _, r => .reg r

def cold : Bank
  | _, .word k => .reg (.word k)
  | _, _ => .lit 0

def committed : Bank
  | _, .word k => .input (.word k)
  | _, .idle => .input .idle
  | _, .valid => .lit 1
  | _, .levels => .input .idle
  | _, _ => .lit 0

def enterFields (d : {w : Nat} → Decode.Port w → E w) (address : E 5) (clear : Bool) : Bank
  | _, .status => .mux (.equal (d .kind) (.lit 1)) (.lit 1)
      (.mux (.equal (d .kind) (.lit 2)) (.lit 2) (.lit 3))
  | _, .pc => .mux (.equal (d .kind) (.lit 1)) address (.lit 0)
  | _, .remaining => .mux (.equal (d .kind) (.lit 1)) (d .duration) (.lit 0)
  | _, .timerActive => .mux (.equal (d .kind) (.lit 1)) (.lit 1) (.lit 0)
  | _, .levels => .mux (.equal (d .kind) (.lit 1)) (d .levels) (.reg .idle)
  | _, .sample k => .mux
      (.band (.equal (d .kind) (.lit 1))
        (.band (d .capture) (.equal (d .slot) (.lit (BitVec.ofFin k)))))
      (.input .sample) (if clear then .lit 0 else .reg (.sample k))
  | _, r => .reg r

def entry (address : E 5) (clear : Bool) : Bank :=
  enterFields (Decode.logic (Store.read (fun k => .reg (.word k)) address)) address clear

def timerRegisters : {w : Nat} → Countdown.Register w → E w
  | _, .remaining => .reg .remaining
  | _, .active => .reg .timerActive

def decrement : Bank
  | _, .remaining => (Countdown.circuit.next .remaining).bind (fun _ => .lit 0) timerRegisters
  | _, .timerActive => (Countdown.circuit.next .active).bind (fun _ => .lit 0) timerRegisters
  | _, r => .reg r

def advance : Bank := fun r =>
  .mux (.zero (.reg .remaining))
    (.mux (.equal (.reg .pc) (.lit 31)) (stopped 3 false r)
      (entry (.sub (.reg .pc) (.lit 31)) false r))
    (decrement r)

/-- PC + 1 uses modular subtraction by 31 at width 5, guarded before slot-31 entry. -/
def next : Bank := fun r =>
  .mux (.input .initialize) (cold r)
    (.mux (.input .reset) (stopped 0 true r)
      (.mux (.equal (.reg .status) (.lit 1))
        (.mux (.reg .valid) (advance r) (hold r))
        (.mux (.input .commit) (committed r)
          (.mux (.band (.reg .valid) (.input .start)) (entry (.lit 0) true r) (hold r)))))

def circuit : Circuit Input Register Output where
  next := next
  output
    | .valid => .reg .valid
    | .status => .reg .status
    | .pc => .reg .pc
    | .remaining => .reg .remaining
    | .timerActive => .reg .timerActive
    | .levels => .reg .levels
    | .sample k => .reg (.sample k)
    | .busy => .equal (.reg .status) (.lit 1)
    | .completed => .equal (.reg .status) (.lit 2)
    | .fault => .equal (.reg .status) (.lit 3)

def tick (i : Inputs) (s : State) : State := fromValues (circuit.step i.values s.values)

/-- Executable equations used to state structural correspondence, before engine refinement. -/
def stoppedValue (reason : BitVec 2) (clear : Bool) (s : State) : State :=
  { s with
    status := reason
    pc := 0
    timer := ⟨0, 0⟩
    levels := s.program.idle
    samples := if clear then Vector.replicate 8 false else s.samples }

def coldValue (s : State) : State :=
  { stoppedValue 0 true s with program := {s.program with idle := 0}, valid := false, levels := 0 }

def commitValue (i : Inputs) (s : State) : State :=
  { stoppedValue 0 true s with program := i.image, valid := true, levels := i.image.idle }

def enterValue (d : Decode.Fields) (address : BitVec 5) (clear : Bool) (i : Inputs) (s : State) : State :=
  let slots := if clear then Vector.replicate 8 false else s.samples
  match d.instruction with
  | none => stoppedValue 3 clear s
  | some .halt => stoppedValue 2 clear s
  | some (.action a) =>
    { s with
      status := 1
      pc := address
      timer := ⟨BitVec.ofFin a.durationMinusOne, 1⟩
      levels := a.levels
      samples := Engine.capture slots a.capture i.sample }

def entryValue (address : BitVec 5) (clear : Bool) (i : Inputs) (s : State) : State :=
  enterValue (Decode.value s.program.memory[address.toNat]) address clear i s

def advanceValue (i : Inputs) (s : State) : State :=
  if s.timer.remaining = 0 then
    if s.pc = 31 then stoppedValue 3 false s else entryValue (s.pc - 31) false i s
  else {s with timer := Countdown.tick {} s.timer}

def stepValue (i : Inputs) (s : State) : State :=
  if i.init then coldValue s
  else if i.reset then stoppedValue 0 true s
  else if s.status = 1 then (if s.valid then advanceValue i s else s)
  else if i.commit then commitValue i s
  else if s.valid && i.start then entryValue 0 true i s else s

end Pinwheel.Hardware.Core
