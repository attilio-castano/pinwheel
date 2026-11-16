import Pinwheel.Hardware.Stream.Export
import Pinwheel.Hardware.Stream.Timing

open Pinwheel.Hardware Pinwheel.Hardware.Stream

private def number (s : String) : IO Nat :=
  match s.toNat? with
  | some n => pure n
  | none => throw (IO.userError s!"Expected a nonnegative integer, got {s}")

/-- Materialize each register once per edge. Keeping a chain of unevaluated
valuation functions would repeatedly reevaluate the entire preceding history. -/
private def snapshot (d : Interface R) (s : Values R) : IO (Values R) := do
  let values ← d.ports.mapM (fun p => pure (s p.2).toNat)
  return fun {w} p => BitVec.ofNat w values[(d.position p).val]!

private def simulate (c : Certified wi wo) (file output : System.FilePath) : IO Nat := do
  let lines := (← IO.FS.readFile file).splitOn "\n"
  let mut hardware : Values c.Register := fun {w} _ => BitVec.ofNat w 0x55aa
  let mut model := c.initial
  let mut history : History (BitVec wi) (BitVec wo) := {}
  let mut rows : Array String := #[]
  let mut cycle := 0
  for line in lines do
    if line.isEmpty then continue
    let [rst, valid, ready, data] := line.splitOn ","
      | throw (IO.userError "Expected reset,valid,ready,data")
    let r ← number rst
    let v ← number valid
    let d ← number ready
    let x ← number data
    unless r ≤ 1 && v ≤ 1 && d ≤ 1 && x < 2^wi do
      throw (IO.userError "Stimulus exceeds the declared port widths")
    if cycle == 0 && r != 1 then throw (IO.userError "First edge must initialize the circuit")
    let i : Input (BitVec wi) := ⟨r == 1, if v == 1 then some (BitVec.ofNat wi x) else none, d == 1⟩
    let before : Values (Out wo) := c.circuit.observe (inputValues i) hardware
    let expected := c.machine.component.observe i model
    let differences := (outputPorts wo).interface.differences cycle "stream" .before before (outputValues expected)
    if let some err := differences[0]? then throw (IO.userError err.describe)
    history := history.advance i expected
    hardware ← snapshot c.registers (c.circuit.step (inputValues i) hardware)
    model := c.machine.step i model
    let stateDifferences := c.registers.differences cycle "state" .after hardware (c.encode model)
    if let some err := stateDifferences[0]? then throw (IO.userError err.describe)
    let after : Values (Out wo) := c.circuit.observe (inputValues i) hardware
    let expectedAfter := c.machine.component.observe i model
    let afterDifferences := (outputPorts wo).interface.differences cycle "stream" .after after (outputValues expectedAfter)
    if let some err := afterDifferences[0]? then throw (IO.userError err.describe)
    unless history.inputs.map c.function == history.outputs ++ c.contract.pending model do
      throw (IO.userError s!"Transaction accounting failed at edge {cycle}")
    rows := rows.push (String.intercalate "," ([cycle, (before inReady).toNat,
      (before outValid).toNat, (before outData).toNat,
      (after inReady).toNat, (after outValid).toNat, (after outData).toNat].map toString))
    cycle := cycle + 1
  IO.FS.writeFile output (String.intercalate "\n" rows.toList ++ "\n")
  pure cycle

def main (args : List String) : IO Unit := do
  let w :: d :: l :: path :: remaining := args
    | throw (IO.userError "Usage: stream_example WIDTH DEPTH STAGES DIRECTORY [stimulus.csv]")
  let width ← number w
  let depth ← number d
  let stages ← number l
  unless width > 0 && stages > 0 do throw (IO.userError "Width and stages must be positive")
  if hd : depth > 0 then
    let design := adderDesign width depth (stages - 1) hd
    let directory : System.FilePath := path
    exportDesign design directory
    match remaining with
    | [] => pure ()
    | [stimulus] =>
      let count ← simulate design.flatten stimulus (directory / "lean.csv")
      IO.println s!"Stream {width}/{depth}/{stages}: {count} edges, structural state and transaction model agree."
    | _ => throw (IO.userError "Unexpected arguments")
  else throw (IO.userError "FIFO depth must be positive")
