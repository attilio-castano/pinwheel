import Pinwheel.Hardware.Timebase.Tx

open Lean Pinwheel.Hardware

private def checkedInput (d : Interface P) (row : Array Nat) : Except String (Values P) := do
  unless row.size == d.size do throw "Wrong input vector length"
  for (n, ⟨width, port⟩) in row.zip d.ports do
    unless n < 2 ^ width do throw s!"Input {d.label port} exceeds {width} bits"
  return fun port => BitVec.ofNat _ (row[d.position port]!)

def main (args : List String) : IO Unit := do
  let [directory] := args | throw (IO.userError "Usage: FractionalTxEmit OUTDIR")
  let out : System.FilePath := directory
  let m := Timebase.Tx.module 4
  let emitted ← IO.ofExcept m.emit
  IO.FS.writeFile (out / "fractional_tx.mlir") emitted.mlir
  IO.FS.writeFile (out / "interface.json") (emitted.descriptor.pretty ++ "\n")
  let data ← IO.FS.readFile (out / "traffic.json")
  let rows : Array (Array Nat) ← IO.ofExcept (Json.parse data >>= fromJson?)
  let traffic ← rows.mapM (fun row => IO.ofExcept (checkedInput m.inputs row))
  let observe (i : Values m.Input) (s : Values m.Register) :=
    toJson (m.outputs.ports.map fun ⟨_, port⟩ => (m.circuit.observe i s port).toNat)
  let mut state : Values m.Register := fun {w} _ => BitVec.ofNat w (2 ^ w - 1)
  let mut trace := #[]
  for i in traffic do
    let before := if trace.isEmpty then Json.null else observe i state
    let registers := m.registers.ports.map fun ⟨_, port⟩ => (m.circuit.step i state port).toNat
    state := fun port => BitVec.ofNat _ (registers[m.registers.position port]!)
    trace := trace.push #[before, observe i state]
  IO.FS.writeFile (out / "lean-trace.json") ((toJson trace).compress ++ "\n")
