import Pinwheel.Hardware.Processor.SystemExport
import Pinwheel.Hardware.Emit
import Pinwheel.Hardware.Processor.Examples.ByteProgram
import Lean.Data.Json

open Lean Pinwheel.Hardware Pinwheel.Hardware.Processor ProcessorSystemFirmware

namespace ProcessorSystemEmit

def emit (out : String) : IO Unit := do
  let base ← SystemExport.exportHierarchy layout rom (by decide) (by decide) out "processor_system"
  let ri := SystemCircuit.registers 2
  let oi := SystemCircuit.outputs
  let descriptor := base.mergeObj (Json.mkObj
    [("rom_words",toJson (Array.ofFn fun a : Fin 32 => (rom (BitVec.ofFin a)).toNat)),
      ("rom_word_width",toJson (5 : Nat)),("ram_word_width",toJson (2 : Nat)),
      ("ram_base",toJson (65536 : Nat)),("gpio_base",toJson (1073741824 : Nat)),
      ("timer_base",toJson (1073742080 : Nat)),("uart_base",toJson (1073742336 : Nat)),
      ("rom_behavior",toJson "explicit immutable elaboration-time image; unused words are illegal zero instructions"),
      ("ram_behavior",toJson "four arbitrary 32-bit words and Q; reset preserves RAM and cancels pending work"),
      ("serial_boundary",toJson "byte arrival/completion/error pins are supplied by an external frontend")])
  IO.FS.writeFile (out++"/interface.json") (descriptor.pretty++"\n")
  IO.println s!"Hierarchical processor system: {ri.size} registers and {oi.size} outputs emitted to {out}."

end ProcessorSystemEmit

def main (args : List String) : IO Unit := do
  let [out] := args | throw (IO.userError "Usage: processor_system_emit OUT")
  ProcessorSystemEmit.emit out
