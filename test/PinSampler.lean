import Pinwheel.Hardware.PinSampler

open Pinwheel.Hardware Pinwheel.Hardware.Loader

private def ensure (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private inductive Toy : Nat → Type where
  | seen : Toy 2

/-- One shared wire, one registered output and one combinational output. -/
private def toy : Netlist Toy Machine.Output Machine.Input :=
  .letWire (.input .incoming : Expr Machine.Input Toy 2) (.finish {
    next := fun r => match r with
      | .seen => .input .wire
    output := fun {w} (o : Machine.Output w) => match w, o with
      | _, .core .readA => Expr.concat (.lit (0 : BitVec 6)) (Expr.reg Toy.seen)
      | _, .core .readB => Expr.concat (.lit (0 : BitVec 6))
          (Expr.input (WithWire.input Machine.Input.incoming))
      | _, _ => .lit 0 })

private def toyState (v : BitVec 2) : Values Toy
  | _, .seen => v

/-- A wrong wrapper: the engine reads the first stage, one edge too early. -/
private def oneStage : Netlist (Extended Toy PinSampler.Stage) Machine.Output Machine.Input :=
  toy.extend (fun {w} (p : Machine.Input w) => match w, p with
      | _, .incoming => .reg (.extra .first)
      | _, .init => .input .init | _, .reset => .input .reset
      | _, .command => .input .command | _, .data => .input .data)
    PinSampler.stage

private def reads (trace : List (Values Machine.Output × Values Machine.Output)) :
    List ((Nat × Nat) × (Nat × Nat)) :=
  trace.map fun e => (((e.1 (.core .readA)).toNat, (e.2 (.core .readA)).toNat),
    ((e.1 (.core .readB)).toNat, (e.2 (.core .readB)).toNat))

def main : IO Unit := do
  let pins : List Machine.Inputs := [3, 0, 1, 2].map fun v => { incoming := v }
  let start : Values (Extended Toy PinSampler.Stage) :=
    Extended.values (toyState 0) (PinSampler.stageValues ⟨1, 2⟩)
  let wrapped := reads ((PinSampler.component (PinSampler.netlist toy)).trace start pins)
  -- Power-up contents 2 then 1 drain first; pin value 3 is consumed on the third edge.
  ensure (wrapped.map (·.1) == [(0, 2), (2, 1), (1, 3), (3, 0)])
    "registered output must follow the pins two edges late"
  -- After each edge the second stage already holds its next value.
  ensure (wrapped.map (·.2) == [(2, 1), (1, 3), (3, 0), (0, 1)])
    "combinational output must see the advanced pipeline after the edge"
  let inner := reads ((PinSampler.component toy).pairTrace (toyState 0) (PinSampler.delayed ⟨1, 2⟩ pins))
  ensure (wrapped == inner) "wrapped trace must equal the inner pair trace on the delayed history"
  let held := reads ((PinSampler.component toy).trace (toyState 0) ((PinSampler.delayed ⟨1, 2⟩ pins).map (·.1)))
  ensure (held.map (·.1) == wrapped.map (·.1) && held != wrapped)
    "an input held across the edge must differ only in combinational post-edge observations"
  let early := reads ((PinSampler.component oneStage).trace start pins)
  ensure (early != wrapped) "one-stage pipeline mutation escaped"
  IO.println "Pin sampler: two-edge latency, post-edge combinational view, pair-trace equality and one-stage mutation passed."
