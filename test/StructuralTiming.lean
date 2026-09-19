import Pinwheel.Hardware.PinSampler

open Pinwheel.Hardware Pinwheel.Hardware.Loader

private def ensure (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private inductive Toy : Nat → Type where
  | seen : Toy 2
  | held : Toy 2

/-- `seen` follows the pins through one shared wire; `held` recirculates behind a
two-operation enable that reads only a host port. -/
private def toy : Netlist Toy Machine.Output Machine.Input :=
  .letWire (Expr.inv (Expr.input Machine.Input.incoming) : Expr Machine.Input Toy 2) (.finish {
    next := fun {w} (r : Toy w) => match w, r with
      | _, .seen => Expr.input WithWire.wire
      | _, .held => Expr.mux (Expr.inv (Expr.zero (Expr.input (WithWire.input Machine.Input.command))))
          (Expr.reg Toy.seen) (Expr.reg Toy.held)
    output := fun {w} (_ : Machine.Output w) => .lit 0 })

private def pins : Launch Machine.Input := PinSampler.pinLaunch
private def command : Launch Machine.Input
  | _, .command => some 0
  | _, _ => none
private def nothing : Launch Toy := fun _ => none
private def onlyHeld : Launch Toy
  | _, .held => some 0
  | _, .seen => none

/-- A wrong wrapper that leaves the pin wired straight into the inner logic. -/
private def bypass : Netlist (Extended Toy PinSampler.Stage) Machine.Output Machine.Input :=
  toy.extend (fun {w} (p : Machine.Input w) => Expr.input p) PinSampler.stage

def main : IO Unit := do
  -- Levels count operations on the path, through the shared wire.
  ensure (toy.arrivalNext max Cost.unit pins nothing .seen == some 1) "inverter before the wire is one level"
  ensure (toy.arrivalNext max Cost.unit pins nothing .held == none) "held must not see the pins"
  -- Latest and earliest differ on a recirculating register: enable 3 levels, hold path 1.
  ensure (toy.arrivalNext max Cost.unit command nothing .held == some 3) "enable cone depth"
  ensure (toy.arrivalNext max Cost.unit command onlyHeld .held == some 3
      && toy.arrivalNext min Cost.unit command onlyHeld .held == some 1) "latest versus earliest arrival"
  -- Wiring is free and a multiplexer costs two levels in the gate estimate.
  ensure (toy.arrivalNext max Cost.gates command nothing .held == some (1 + 1 + 2)) "gate-level estimate"
  -- The single-pass evaluator agrees with the definition.
  ensure (toy.withArrivals max Cost.unit command nothing
      (fun c leaves => (c.next Toy.held).arrival max Cost.unit leaves nothing) == some 3) "shared wire evaluation"
  -- Behind the pipeline the pin reaches the first stage only; a bypass is visible.
  let wrapped := PinSampler.netlist toy
  let quiet : Launch (Extended Toy PinSampler.Stage) := fun _ => none
  ensure (wrapped.arrivalNext max Cost.unit pins quiet (.inner .seen) == none
      && wrapped.arrivalNext max Cost.unit pins quiet (.extra .first) == some 0
      && wrapped.arrivalNext max Cost.unit pins quiet (.extra .second) == none) "pins must stop at the first stage"
  ensure (bypass.arrivalNext max Cost.unit pins quiet (.inner .seen) == some 1) "bypass mutation escaped"
  -- Launching from the second stage reproduces the inner depth: the wrapper law.
  let second : Launch (Extended Toy PinSampler.Stage)
    | _, .extra .second => some 0
    | _, _ => none
  ensure (wrapped.arrivalNext max Cost.unit (fun _ => none) second (.inner .seen) ==
      toy.arrivalNext max Cost.unit pins nothing .seen) "wrapper timing law"
  IO.println "Structural timing: levels through shared wires, latest/earliest, gate estimate, pin isolation and bypass mutation passed."
