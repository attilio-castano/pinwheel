import Pinwheel.Hardware.Storage.BackendNetlist
import Pinwheel.Hardware.NetlistEmit
import Pinwheel.Hardware.Loader.Emit

namespace Pinwheel.Hardware.Storage.Backend
open Loader

def bankRegisters (b : Bool) : Array (Sigma Register) :=
  Array.ofFn (fun k : Fin 32 => ⟨55, .word b (BitVec.ofFin k)⟩) ++
  Array.ofFn (fun k : Fin 256 => ⟨5, .index b (BitVec.ofFin k)⟩) ++
  #[⟨6, .idle b⟩, ⟨8, .last b⟩]

def registers : Array (Sigma Register) :=
  Loader.registers.map (fun ⟨w, r⟩ => ⟨w, .control r⟩) ++
  Reactive.registers.map (fun ⟨w, r⟩ => ⟨w, .core r⟩) ++
  bankRegisters false ++ bankRegisters true ++ #[⟨64, .current⟩]

def registerLabel : {w : Nat} → Register w → String
  | _, .control r => "loader_" ++ Loader.registerLabel r
  | _, .core r => Reactive.registerLabel r
  | _, .word b k => s!"bank{if b then 1 else 0}_word{k.toNat}"
  | _, .index b k => s!"bank{if b then 1 else 0}_index{k.toNat}"
  | _, .idle b => s!"bank{if b then 1 else 0}_idle"
  | _, .last b => s!"bank{if b then 1 else 0}_last"
  | _, .current => "cached_word"

/-- Only port and register names are adapted here. Every gate is emitted from
the same netlist covered by netlistCompleteRefinement and netlist_initialized_trace. -/
def moduleText : Except String String :=
  Hardware.Netlist.moduleText "pinwheel_atomic_small_dense_cached" netlist
    Machine.inputs registers Machine.outputs Machine.inputLabel registerLabel Machine.outputLabel

end Pinwheel.Hardware.Storage.Backend
