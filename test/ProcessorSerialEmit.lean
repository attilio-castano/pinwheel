import Pinwheel.Hardware.Processor.SerialCircuit
import Pinwheel.Hardware.Emit
import Lean.Data.Json

open Lean Pinwheel.Hardware Pinwheel.Hardware.Processor
namespace ProcessorSerialEmit

def timing (n : Nat) : IO Uart.Timing :=
  if h : 4 ≤ n ∧ n % 2 = 0 then pure ⟨n,h.1,h.2⟩
  else throw (IO.userError "Divisor must be even and at least four")
private def portsJson (d : Interface P) : Json :=
  toJson (d.ports.map fun ⟨w,p⟩ => Json.mkObj
    [("index",toJson (d.position p).val),("name",toJson (d.label p)),("width",toJson w)])

def emit (d : Uart.Timing) (out : String) : IO Unit := do
  let ii := SerialInterface.inputs
  let oi := SerialInterface.outputs
  let ri := SerialCircuit.registers d
  let rn := fun {b} (r : SerialCircuit.Register d b) => "r_" ++ ri.label r
  let outputRoles := #["request_ready","response_valid","response_code","response_data","gpio_output",
    "held_tx_active","held_tx_data","tx","tx_ready","tx_complete","rx_valid","rx_data","framing_error"]
  let regRoles := #["gpio","timer","held_tx_active","held_tx_data","held_rx_valid","held_rx_data","overrun","framing",
    "tx_active","tx_count","tx_byte","rx_phase","rx_count","rx_byte"]
  IO.FS.createDirAll out
  IO.FS.writeFile (out ++ "/serial.mlir") (← IO.ofExcept
    (Emit.moduleText "processor_serial" (SerialCircuit.circuit d) ii.ports ri.ports oi.ports ii.label ri.label oi.label))
  let regs := toJson (ri.ports.map fun ⟨b,r⟩ => Json.mkObj
    [("index",toJson (ri.position r).val),("name",toJson (rn r)),("reference",toJson (rn r)),("width",toJson b)])
  let roles := Json.mkObj ((ii.ports.map fun ⟨_,p⟩ => (ii.label p,toJson (ii.label p))).toList ++
    (oi.ports.map fun ⟨_,p⟩ => (outputRoles[(oi.position p).val]!,toJson (oi.label p))).toList)
  let registerRoles := Json.mkObj (ri.ports.map fun ⟨_,r⟩ =>
    (regRoles[(ri.position r).val]!,toJson (rn r))).toList
  let descriptor := Json.mkObj
    [("schema",toJson (1 : Nat)),("module",toJson "processor_serial"),("clock",toJson "clk"),
     ("divisor",toJson d.divisor),("counter_width",toJson (Uart.Structural.width d)),
     ("inputs",portsJson ii),("outputs",portsJson oi),("registers",regs),("roles",roles),("register_roles",registerRoles),
     ("response_codes",Json.mkObj [("read",toJson (0 : Nat)),("stored",toJson (1 : Nat)),("register_hole",toJson (2 : Nat)),
       ("direction",toJson (3 : Nat)),("tx_busy",toJson (4 : Nat)),("rx_empty",toJson (5 : Nat))]),
     ("device_codes",Json.mkObj [("gpio",toJson (0 : Nat)),("timer",toJson (1 : Nat)),("uart",toJson (2 : Nat)),("invalid",toJson (3 : Nat))]),
     ("startup",toJson "arbitrary fourteen physical registers; logical correspondence requires UART bounds and TX ownership until reset"),
     ("reset_behavior",toJson "synchronous reset clears all fourteen registers; TX is high and other outputs zero during reset"),
     ("operation_behavior",toJson "always-ready atomic request/response edge; invalid device faults without CPU effect; accepted TX write bypasses on the same edge"),
     ("frontend_boundary",toJson "RX is already synchronous; exact digital 8N1 timing only, without analog, CDC or baud-tolerance qualification")]
  IO.FS.writeFile (out ++ "/interface.json") (descriptor.pretty ++ "\n")
  IO.println s!"Serial D{d.divisor}: {ii.size} inputs, {oi.size} outputs, {ri.size} registers."
end ProcessorSerialEmit

def main (args : List String) : IO Unit := do
  let [divisor,out] := args | throw (IO.userError "Usage: serial_emit divisor outdir")
  let some n := divisor.toNat? | throw (IO.userError "Invalid divisor")
  ProcessorSerialEmit.emit (← ProcessorSerialEmit.timing n) out
