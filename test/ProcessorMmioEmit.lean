import Pinwheel.Hardware.Processor.MmioCircuit
import Pinwheel.Hardware.Emit
import Lean.Data.Json

open Lean Pinwheel.Hardware Pinwheel.Hardware.Processor

namespace ProcessorMmioEmit

private def portsJson (d : Interface P) : Json :=
  toJson (d.ports.map fun ⟨w, p⟩ => Json.mkObj
    [("index", toJson (d.position p).val), ("name", toJson (d.label p)), ("width", toJson w)])

def emit (out : String) : IO Unit := do
  let ii := MmioInterface.inputs
  let oi := MmioInterface.outputs
  let ri := MmioCircuit.registers
  let registerName := fun {b} (r : MmioCircuit.Register b) => "r_" ++ ri.label r
  IO.FS.createDirAll out
  IO.FS.writeFile (out ++ "/mmio.mlir") (← IO.ofExcept
    (Emit.moduleText "processor_mmio" MmioCircuit.circuit
      ii.ports ri.ports oi.ports ii.label ri.label oi.label))
  let regs := toJson (ri.ports.map fun ⟨b, r⟩ => Json.mkObj
    [("index", toJson (ri.position r).val), ("name", toJson (registerName r)),
     ("reference", toJson (registerName r)), ("width", toJson b)])
  let roles := Json.mkObj ((ii.ports.map fun ⟨_, p⟩ => (ii.label p, toJson (ii.label p))).toList ++
    (oi.ports.map fun ⟨_, p⟩ => (oi.label p, toJson (oi.label p))).toList)
  let registerRoles := Json.mkObj (ri.ports.map fun ⟨_, r⟩ =>
    (ri.label r, toJson (registerName r))).toList
  let descriptor := Json.mkObj
    [("schema", toJson (1 : Nat)), ("module", toJson "processor_mmio"), ("clock", toJson "clk"),
     ("inputs", portsJson ii), ("outputs", portsJson oi), ("registers", regs),
     ("roles", roles), ("register_roles", registerRoles),
     ("response_codes", Json.mkObj [("read", toJson (0 : Nat)), ("stored", toJson (1 : Nat)),
       ("register_hole", toJson (2 : Nat)), ("direction", toJson (3 : Nat)),
       ("tx_busy", toJson (4 : Nat)), ("rx_empty", toJson (5 : Nat))]),
     ("device_codes", Json.mkObj [("gpio", toJson (0 : Nat)), ("timer", toJson (1 : Nat)),
       ("uart", toJson (2 : Nat)), ("invalid", toJson (3 : Nat))]),
     ("startup", toJson "arbitrary eight physical registers; inactive TX/RX bytes retained until capture or reset"),
     ("reset_behavior", toJson "synchronous reset clears every register; all outputs are masked during reset"),
     ("operation_behavior", toJson "always-ready atomic request/response edge with no response backpressure; invalid device faults without CPU effect"),
     ("frontend_boundary", toJson "TX completion, RX arrival and framing error are explicit external events; no serial-wire claim")]
  IO.FS.writeFile (out ++ "/interface.json") (descriptor.pretty ++ "\n")
  IO.println s!"MMIO: {ii.size} inputs, {oi.size} outputs and {ri.size} registers emitted to {out}."

end ProcessorMmioEmit

def main (args : List String) : IO Unit := do
  let [out] := args | throw (IO.userError "Usage: processor_mmio_emit outdir")
  ProcessorMmioEmit.emit out
