import Pinwheel.Hardware.Stream.Properties
import Pinwheel.Hardware.Stream.Export

open Pinwheel.Hardware Pinwheel.Hardware.Stream

def graph (m : Map wi wa) (n : Map wi wb) (leftExtra rightExtra : Nat) : Design wi (wa + wb) :=
  .parallel (.pipeline m leftExtra) (.pipeline n rightExtra)

example (m : Map wi wa) (n : Map wi wb) (l r : Nat) :
    Bounded (graph m n l r).flatten (min (l + 1) (r + 1)) :=
  bounded_parallel _ _ (bounded_pipeline m l) (bounded_pipeline n r)

example (m : Map wi wa) (n : Map wi wb) (l r : Nat) : Stable (graph m n l r).flatten.machine :=
  stable_parallel _ _ _ (stable_pipeline m l) (stable_pipeline n r)

example (m : Map wi wa) (n : Map wi wb) (l r : Nat) (inputs : List (Input (BitVec wi))) :
    let c := (graph m n l r).flatten
    let actual := runHistory c.simulator (c.encode c.initial) {} inputs
    let model := runHistory c.machine.component c.initial {} inputs
    actual.2.inputs.map c.function = actual.2.outputs ++ c.contract.pending model.1 :=
  (graph m n l r).flatten.simulator_transactions inputs

def main : IO Unit := do
  let d := graph (Map.identity 8) (Map.identity 8) 0 3
  let rtl ← IO.ofExcept (d.flatten.rtl "branch_smoke")
  unless rtl.contains "hw.module @branch_smoke" do throw (IO.userError "Graph emission failed")
  IO.println "Graph: arbitrary branch maps/depths inherit capacity, stalls and transaction proofs."
