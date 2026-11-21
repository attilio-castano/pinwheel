import Pinwheel.Hardware.Stream.ElasticCircuit

namespace MemoryTransferSupport

open Pinwheel.Hardware

/-- Test transform: invert the input bits, then zero-extend or truncate.
The independent integer oracle implements this without Lean expressions. -/
def transform (wi wo : Nat) : Stream.Map wi wo :=
  ⟨.slice 0 wo (by omega) (.concat (.lit (0 : BitVec wo)) (.inv (.input .data))),
    fun value => ((0 : BitVec wo) ++ ~~~value).extractLsb' 0 wo, fun _ => rfl⟩

end MemoryTransferSupport
