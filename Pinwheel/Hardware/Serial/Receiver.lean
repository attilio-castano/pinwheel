import Pinwheel.Hardware.Feeder
import Pinwheel.Hardware.Loader.Machine

/-! The serial loader: three pins in place of the loader's 67-wire word port.

The host shifts a 72-bit frame — one command byte, then a 64-bit word, most
significant bit first — on `mosi`, one bit per rising `sck`, while `csn` is low.
The receiver sees the pins already sampled into the chip's clock. It detects a
rising clock by comparing each sample with the last, shifts the bit in, latches
the command after the first byte, and on the 72nd bit raises `fire` for exactly
one edge. On that edge the core sees the command and the word; on every other
edge it sees no command. Command 7 is the core's `reset` input; `csn` high
abandons a partial frame.

This file is the receiver as a `Feeder` in front of any netlist with the loader
machine's ports, its reading as functions on records, and the proof that the
two agree. What a well-formed frame delivers is `Serial/Frame.lean`. -/
namespace Pinwheel.Hardware.Serial
open Loader

/-- The pins as the receiver sees them: sampled, in the chip's clock. -/
inductive Input : Nat → Type where
  | init : Input 1 | sck : Input 1 | mosi : Input 1 | csn : Input 1 | incoming : Input 2

structure Inputs where
  init : Bool := false
  sck : Bool := false
  mosi : Bool := false
  csn : Bool := true
  incoming : BitVec 2 := 0
  deriving Repr

inductive Register : Nat → Type where
  | sckPrev : Register 1 | count : Register 7 | shift : Register 64
  | command : Register 3 | fire : Register 1

structure State where
  /-- The clock pin at the previous sample. -/
  sckPrev : Bool := false
  /-- Bits taken in the current frame. -/
  count : BitVec 7 := 0
  shift : BitVec 64 := 0
  command : BitVec 3 := 0
  /-- A frame completed at the previous sample. -/
  fire : Bool := false
  deriving DecidableEq, Repr

def Inputs.values (i : Inputs) : Values Input
  | _, .init => BitVec.ofBool i.init | _, .sck => BitVec.ofBool i.sck
  | _, .mosi => BitVec.ofBool i.mosi | _, .csn => BitVec.ofBool i.csn
  | _, .incoming => i.incoming

def State.values (s : State) : Values Register
  | _, .sckPrev => BitVec.ofBool s.sckPrev | _, .count => s.count | _, .shift => s.shift
  | _, .command => s.command | _, .fire => BitVec.ofBool s.fire

/-! ### As functions -/

/-- A bit is taken at the sample where the clock is first seen high, while selected. -/
def taking (i : Inputs) (s : State) : Bool := !i.init && !i.csn && i.sck && !s.sckPrev

/-- The register with one more bit at the bottom; the top bit falls off. -/
def shiftIn (x : BitVec 64) (b : Bool) : BitVec 64 := x.extractLsb' 0 63 ++ BitVec.ofBool b

def next (i : Inputs) (s : State) : State :=
  { sckPrev := i.sck
    count := if i.init || i.csn then 0
      else if taking i s then (if s.count == 71 then 0 else s.count + 1) else s.count
    shift := if taking i s then shiftIn s.shift i.mosi else s.shift
    command := if taking i s && s.count == 7
      then s.shift.extractLsb' 0 2 ++ BitVec.ofBool i.mosi else s.command
    fire := taking i s && s.count == 71 }

/-- What the core sees: the command and the word on the edge after a frame
completes, no command otherwise. -/
def feed (i : Inputs) (s : State) : Machine.Inputs :=
  { init := i.init
    reset := s.fire && s.command == 7
    command := if s.fire && s.command != 7 then s.command else 0
    data := s.shift
    incoming := i.incoming }

/-! ### As a circuit -/

abbrev E := Expr Input Register

def takingExpr : E 1 :=
  .band (.inv (.input .init)) (.band (.inv (.input .csn)) (.band (.input .sck) (.inv (.reg .sckPrev))))

def stop : E 1 := .band (.reg .fire) (.equal (.reg .command) (.lit 7))

def receiver : Feeder Input Register Machine.Input where
  input := fun p => match p with
    | .init => .input .init
    | .reset => stop
    | .command => .mux (.band (.reg .fire) (.inv (.equal (.reg .command) (.lit 7)))) (.reg .command) (.lit 0)
    | .data => .reg .shift
    | .incoming => .input .incoming
  next := fun r => match r with
    | .sckPrev => .input .sck
    | .count => .mux (Execution.bor (.input .init) (.input .csn)) (.lit 0)
        (.mux takingExpr (.mux (.equal (.reg .count) (.lit 71)) (.lit 0) (.sub (.reg .count) (.lit 127)))
          (.reg .count))
    | .shift => .mux takingExpr
        (.concat (.slice 0 63 (by decide) (.reg .shift : E 64)) (.input .mosi : E 1)) (.reg .shift)
    | .command => .mux (.band takingExpr (.equal (.reg .count) (.lit 7)))
        (.concat (.slice 0 2 (by decide) (.reg .shift : E 64)) (.input .mosi : E 1)) (.reg .command)
    | .fire => .band takingExpr (.equal (.reg .count) (.lit 71))

private theorem mux_bool (c : Bool) (t f : BitVec w) :
    (if BitVec.ofBool c = 1 then t else f) = if c then t else f := by
  cases c <;> rfl

private theorem and_bool (a b : Bool) : BitVec.ofBool a &&& BitVec.ofBool b = BitVec.ofBool (a && b) := by
  cases a <;> cases b <;> rfl

private theorem not_bool (a : Bool) : ~~~BitVec.ofBool a = BitVec.ofBool (!a) := by
  cases a <;> rfl

private theorem increment (x : BitVec 7) : x - 127 = x + 1 := by bv_omega

theorem taking_correct (i : Inputs) (s : State) :
    takingExpr.eval i.values s.values = BitVec.ofBool (taking i s) := by
  simp only [takingExpr, Expr.eval, Inputs.values, State.values, taking, not_bool, and_bool, Bool.and_assoc]

/-- The circuit is the functions, register by register and port by port. -/
def model : Feeder.Model receiver Inputs State Machine.Inputs where
  outer := Inputs.values
  state := State.values
  inner := Machine.Inputs.values
  feed := feed
  step := next
  feed_correct := fun i s _ p => by
    cases p with
    | init => rfl
    | reset =>
      simp only [receiver, stop, Expr.eval, State.values, and_bool]
      rfl
    | command =>
      simp only [receiver, Expr.eval, State.values, not_bool, and_bool, mux_bool]
      rfl
    | data => rfl
    | incoming => rfl
  step_correct := fun i s _ r => by
    cases r with
    | sckPrev => rfl
    | count =>
      simp only [receiver, Execution.bor, Expr.eval, taking_correct, State.values, Inputs.values,
        not_bool, and_bool, mux_bool, increment, Bool.not_and, Bool.not_not]
      rfl
    | shift =>
      simp only [receiver, Expr.eval, taking_correct, State.values, Inputs.values, mux_bool]
      rfl
    | command =>
      simp only [receiver, Expr.eval, taking_correct, State.values, Inputs.values, and_bool, mux_bool]
      rfl
    | fire =>
      simp only [receiver, Expr.eval, taking_correct, State.values, and_bool]
      rfl

/-! ### What the inner netlist never sees -/

/-- The host's three pins reach the core only through the receiver's registers:
the command, the word and `reset` are register outputs. -/
def hostPins : Launch Input
  | _, .sck => some 0 | _, .mosi => some 0 | _, .csn => some 0
  | _, .init => none | _, .incoming => none

theorem host_pins_registered (pick : Pick) (cost : Cost) {w : Nat} (p : Machine.Input w) :
    (receiver.input p).arrival pick cost hostPins (fun _ => none) = none := by
  cases p <;> rfl

/-- No combinational path from the host's pins to anything behind the receiver. -/
theorem no_path_from_host (pick : Pick) (cost : Cost) (n : Netlist R Machine.Output Machine.Input)
    (r : R w) : (receiver.wrap n).arrivalNext pick cost hostPins (fun _ => none) (.inner r) = none :=
  Feeder.wrap_shields pick cost receiver n hostPins (fun p => host_pins_registered pick cost p) r

end Pinwheel.Hardware.Serial
