import LaneClient

open Lean Pinwheel.Hardware

namespace LaneClient

private def checkedInput (d : Interface P) (row : Array Nat) : Except String (Values P) := do
  unless row.size == d.size do throw "Wrong input vector length"
  for (n, ⟨width, port⟩) in row.zip d.ports do
    unless n < 2 ^ width do throw s!"Input {d.label port} exceeds {width} bits"
  return fun port => BitVec.ofNat _ (row[d.position port]!)

def emitAndSimulate (count width extra : Nat) (circular : Bool) (dir : System.FilePath) : IO Unit := do
  let fifo := selectFifo width circular
  let module := design count width extra circular
  let dut := module.circuit
  let ins := module.inputs
  let outs := module.outputs
  let regs := module.registers
  let emitted ← IO.ofExcept module.emit
  IO.FS.writeFile (dir / "lanes.mlir") emitted.mlir
  IO.FS.writeFile (dir / "interface.json") (emitted.descriptor.pretty ++ "\n")
  let data ← IO.FS.readFile (dir / "traffic.json")
  let rows : Array (Array Nat) ← IO.ofExcept (Json.parse data >>= fromJson?)
  let traffic ← rows.mapM (fun row => IO.ofExcept (checkedInput ins row))
  -- Start from one dirty binary state. The kernel theorem covers every one.
  let row (o : Values (Output count width)) := outs.ports.map fun ⟨_, p⟩ => (o p).toNat
  let mut state : Values (Register count fifo extra) := fun {w} _ => BitVec.ofNat w (2 ^ w - 1)
  let mut observations := #[]
  for i in traffic do
    let before := if observations.isEmpty then Json.null else toJson (row (dut.observe i state))
    -- Materialize the complete snapshot so reading a register cannot rerun earlier edges.
    let snapshot := regs.ports.map fun ⟨_, p⟩ => (dut.step i state p).toNat
    state := fun p => BitVec.ofNat _ (snapshot[regs.position p]!)
    observations := observations.push #[before, toJson (row (dut.observe i state))]
  IO.FS.writeFile (dir / "lean-trace.json") ((toJson observations).compress ++ "\n")

end LaneClient

def main (args : List String) : IO Unit := do
  let [count, width, extra, backend, dir] := args
    | throw (IO.userError "Usage: EmitAndSimulate COUNT WIDTH EXTRA (shift|circular) OUTDIR")
  let some n := count.toNat? | throw (IO.userError "Invalid lane count")
  let some w := width.toNat? | throw (IO.userError "Invalid payload width")
  let some e := extra.toNat? | throw (IO.userError "Invalid extra stage count")
  unless n > 0 && w > 0 && (backend == "shift" || backend == "circular") do
    throw (IO.userError "Expected positive count and width and a known FIFO backend")
  LaneClient.emitAndSimulate n w e (backend == "circular") dir
