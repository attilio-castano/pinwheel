import Pinwheel.Hardware.Circuit

namespace Pinwheel.Hardware

/-- A fresh combinational wire extends only the input environment, never state. -/
inductive WithWire (Input : Nat → Type) (width : Nat) : Nat → Type where
  | input : Input w → WithWire Input width w
  | wire : WithWire Input width width

def WithWire.values (i : Values I) (value : BitVec width) : Values (WithWire I width)
  | _, .input p => i p
  | _, .wire => value

/-- Typed sequential let bindings make shared combinational logic explicit.
Only `finish` updates registers; every wire reads the same pre-edge state.
The type excludes forward references and combinational cycles. -/
inductive Netlist (Register Output : Nat → Type) : (Nat → Type) → Type 1 where
  | finish : Circuit I Register Output → Netlist Register Output I
  | letWire : Expr I Register w → Netlist Register Output (WithWire I w) → Netlist Register Output I

def Netlist.step (n : Netlist R O I) (i : Values I) (s : Values R) : Values R :=
  match n with
  | .finish c => c.step i s
  | .letWire e body => body.step (WithWire.values i (e.eval i s)) s

def Netlist.observe (n : Netlist R O I) (i : Values I) (s : Values R) : Values O :=
  match n with
  | .finish c => c.observe i s
  | .letWire e body => body.observe (WithWire.values i (e.eval i s)) s

end Pinwheel.Hardware
