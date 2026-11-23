import Pinwheel.Hardware.Uart.FractionalRx

open Lean Pinwheel.Hardware
open Pinwheel.Hardware.Uart.FractionalRx

private def rejectsZeroWidth (result : Except String α) : Bool :=
  match result with
  | .error msg => msg == "Zero-width signal: half_num"
  | .ok _ => false

#guard rejectsZeroWidth (hierarchy 0).layout
#guard rejectsZeroWidth (hierarchy 0).emit

private def checkedInput (d : Interface P) (row : Array Nat) : Except String (Values P) := do
  unless row.size == d.size do throw "Wrong input vector length"
  for (n, ⟨width, port⟩) in row.zip d.ports do
    unless n < 2 ^ width do throw s!"Input {d.label port} exceeds {width} bits"
  return fun port => BitVec.ofNat _ (row[d.position port]!)

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "Usage: FractionalUartRxEmit OUTDIR")
  let out : System.FilePath := path
  let design := hierarchy 6
  let emitted ← IO.ofExcept design.emit
  emitted.write out
  let m := design.flat
  let json ← IO.FS.readFile (out / "traffic.json")
  let rows : Array (Array Nat) ← IO.ofExcept (Json.parse json >>= fromJson?)
  let traffic ← rows.mapM fun row => IO.ofExcept (checkedInput m.inputs row)
  let observe (i : Values m.Input) (s : Values m.Register) :=
    toJson (m.outputs.ports.map fun ⟨_, port⟩ => (m.circuit.observe i s port).toNat)
  let mut state : Values m.Register := fun {b} _ => BitVec.ofNat b (2 ^ b - 1)
  let mut trace := #[]
  for i in traffic do
    let before := if trace.isEmpty then Json.null else observe i state
    let registers := m.registers.ports.map fun ⟨_, port⟩ => (m.circuit.step i state port).toNat
    state := fun port => BitVec.ofNat _ (registers[m.registers.position port]!)
    trace := trace.push #[before, observe i state]
  IO.FS.writeFile (out / "lean-trace.json") ((toJson trace).compress ++ "\n")
