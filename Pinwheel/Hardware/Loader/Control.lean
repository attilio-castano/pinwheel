import Pinwheel.Hardware.Reactive.Emit

namespace Pinwheel.Hardware.Loader

/-- Commands: nop 0, begin 1, push 2, commit 3, abort 4, start 5; 6/7 rejected. -/
structure Inputs where
  init : Bool := false
  reset : Bool := false
  busy : Bool := false
  command : BitVec 3 := 0
  data : BitVec 64 := 0
  deriving Repr

/-- The cursor counts accepted words in the fixed 64+256+2-word upload. -/
structure State where
  active : Bool := false
  valid : Bool := false
  pending : Bool := false
  cursor : BitVec 9 := 0
  deriving DecidableEq, Repr

def enabled (i : Inputs) : Bool := !i.init && !i.reset && !i.busy

def goodWord (cursor : BitVec 9) (data : BitVec 64) : Bool :=
  if cursor.toNat < 64 then Execution.validValue data
  else if cursor.toNat < 321 then data.toNat < 64
  else data.toNat < 256

def push (i : Inputs) (s : State) : Bool :=
  enabled i && i.command == 2 && s.pending && s.cursor.toNat < 322 && goodWord s.cursor i.data

def commit (i : Inputs) (s : State) : Bool :=
  enabled i && i.command == 3 && s.pending && s.cursor == 322

def start (i : Inputs) (s : State) : Bool := enabled i && i.command == 5 && s.valid

def accepted (i : Inputs) (s : State) : Bool :=
  enabled i && (i.command == 0 || i.command == 1 || i.command == 4 || push i s || commit i s || start i s)

def rejected (i : Inputs) (s : State) : Bool :=
  !i.init && !i.reset && i.command != 0 && !accepted i s

def next (i : Inputs) (s : State) : State :=
  if i.init then {} else if i.reset then {s with pending := false, cursor := 0}
  else if i.busy then s
  else if i.command == 1 then {s with pending := true, cursor := 0}
  else if i.command == 4 then {s with pending := false, cursor := 0}
  else if commit i s then ⟨!s.active, true, false, 0⟩
  else if push i s then {s with cursor := s.cursor - 511}
  else s

inductive Input : Nat → Type where
  | init : Input 1 | reset : Input 1 | busy : Input 1 | command : Input 3 | data : Input 64
inductive Register : Nat → Type where
  | active : Register 1 | valid : Register 1 | pending : Register 1 | cursor : Register 9
inductive Output : Nat → Type where
  | push : Output 1 | commit : Output 1 | start : Output 1 | rejected : Output 1
  | state : Register w → Output w

abbrev E := Expr Input Register

def Inputs.values (i : Inputs) : Values Input
  | _, .init => BitVec.ofBool i.init | _, .reset => BitVec.ofBool i.reset
  | _, .busy => BitVec.ofBool i.busy | _, .command => i.command | _, .data => i.data

def State.values (s : State) : Values Register
  | _, .active => BitVec.ofBool s.active | _, .valid => BitVec.ofBool s.valid
  | _, .pending => BitVec.ofBool s.pending | _, .cursor => s.cursor

def orGate (a b : E 1) : E 1 := .inv (.band (.inv a) (.inv b))
def gate : E 1 := .band (.inv (.input .init)) (.band (.inv (.input .reset)) (.inv (.input .busy)))
def command (n : BitVec 3) : E 1 := .equal (.input .command) (.lit n)
def wordGate : E 1 :=
  .mux (.ult (.reg .cursor) (.lit 64)) (Execution.logic (.input .data) .valid)
    (.mux (.ult (.reg .cursor) (.lit 321)) (.ult (.input .data) (.lit 64)) (.ult (.input .data) (.lit 256)))
def pushGate : E 1 := .band gate (.band (command 2) (.band (.reg .pending) (.band (.ult (.reg .cursor) (.lit 322)) wordGate)))
def commitGate : E 1 := .band gate (.band (command 3) (.band (.reg .pending) (.equal (.reg .cursor) (.lit 322))))
def startGate : E 1 := .band gate (.band (command 5) (.reg .valid))
def acceptedGate : E 1 := .band gate (orGate (command 0) (orGate (command 1) (orGate (command 4) (orGate pushGate (orGate commitGate startGate)))))
def rejectedGate : E 1 := .band (.inv (.input .init)) (.band (.inv (.input .reset)) (.band (.inv (command 0)) (.inv acceptedGate)))

def stopped (pendingValue : Bool) (r : Register w) : E w := match r with
  | .pending => .lit (BitVec.ofBool pendingValue) | .cursor => .lit 0
  | .active => .reg .active | .valid => .reg .valid

def committed (r : Register w) : E w := match r with
  | .active => .inv (.reg .active) | .valid => .lit 1 | .pending => .lit 0 | .cursor => .lit 0

def advanced (r : Register w) : E w := match r with
  | .cursor => .sub (.reg .cursor) (.lit 511)
  | .active => .reg .active | .valid => .reg .valid | .pending => .reg .pending

def circuit : Circuit Input Register Output where
  next := fun r => .mux (.input .init) (.lit 0)
    (.mux (.input .reset) (stopped false r) (.mux (.input .busy) (.reg r)
      (.mux (command 1) (stopped true r) (.mux (command 4) (stopped false r)
        (.mux commitGate (committed r) (.mux pushGate (advanced r) (.reg r)))))))
  output := fun o => match o with
    | .push => pushGate | .commit => commitGate | .start => startGate | .rejected => rejectedGate
    | .state r => .reg r

end Pinwheel.Hardware.Loader
