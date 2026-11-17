import Pinwheel.Hardware.Processor.LoadableSystemExport
import Pinwheel.Hardware.Processor.Examples.ByteProgram
import Lean.Data.Json

open Lean Pinwheel.Hardware Pinwheel.Hardware.Processor ProcessorSystemFirmware

def main (args : List String) : IO Unit := do
  let [out] := args | throw (IO.userError "Usage: processor_loadable_system_emit OUT")
  let base ← LoadableSystemExport.exportHierarchy layout rom (by decide) (by decide) out "processor_loadable_system"
  let descriptor := base.mergeObj (Json.mkObj
    [("rom_words",toJson (Array.ofFn fun a : Fin 32 => (rom (BitVec.ofFin a)).toNat)),
      ("rom_word_width",toJson (5 : Nat)),("ram_word_width",toJson (2 : Nat)),
      ("ram_base",toJson (65536 : Nat)),("gpio_base",toJson (1073741824 : Nat)),
      ("timer_base",toJson (1073742080 : Nat)),("uart_base",toJson (1073742336 : Nat)),
      ("rom_behavior",toJson "explicit immutable elaboration-time image; unused words are illegal zero instructions"),
      ("ram_behavior",toJson "four words supplied by clocked loader writes before run; no emitted initialization; Q/metadata arbitrary until captured")])
  IO.FS.writeFile (out++"/interface.json") (descriptor.pretty++"\n")
  IO.println s!"Loadable system: {(LoadableSystem.registers 2).size} registers, {LoadableSystem.outputs.size} outputs, {(LoadableSystem.inputs 2).size} inputs emitted."
