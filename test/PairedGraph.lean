import Pinwheel.Hardware.Storage.PairedController

open Pinwheel.Hardware
open Pinwheel.Hardware.Storage.PairedController

private def check (nodes : List (Computation × E 64)) (expected : Option String) : IO Unit := do
  let result := construct (I := Input) (.input) (fun _ => .lit 0) [] nodes
  match result, expected with
  | .ok _, none => pure ()
  | .error actual, some wanted =>
    unless actual == wanted do
      throw (IO.userError s!"Expected {wanted}, got {actual}")
  | .ok _, some wanted => throw (IO.userError s!"Accepted invalid graph: {wanted}")
  | .error actual, none => throw (IO.userError s!"Rejected complete graph: {actual}")

def main : IO Unit := do
  check bindings none
  check (bindings ++ bindings.take 1) (some "Duplicate paired computation")
  check bindings.reverse (some "Forward or missing paired computation")
  check (bindings.drop 1) (some "Forward or missing paired computation")
  check (bindings.take (bindings.length - 1)) (some "Unbound paired body computation")
  IO.println "Passed complete paired graph and four invalid-binding controls."
