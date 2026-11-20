import Pinwheel.Hardware.Stream.Bundle
import Pinwheel.Hardware.Emit

open Pinwheel.Hardware Pinwheel.Hardware.Stream
set_option backward.isDefEq.respectTransparency false

def packet : Bundle := .pair (.bits "tag" 3) (.pair (.bits "left_value" 8) (.bits "right_value" 17))
def packetInterface := packet.interface (by decide +kernel)

example : packet.width = 28 := rfl
example : packet.unpack (packet.pack (5#3, (127#8, 65537#17))) = (5#3, (127#8, 65537#17)) := packet.unpack_pack _
example : packetInterface.ports.size = 3 := rfl

def packetCircuit : Circuit packet.Port NoRegister packet.Port where
  next := fun r => nomatch r
  output := packet.unpackExpr (packet.packExpr (.input))

example (i : Values packet.Port) (p : packet.Port w) :
    packetCircuit.observe i NoRegister.values p = i p := by
  simp only [packetCircuit, Circuit.observe, Bundle.unpackExpr_eval, Bundle.packExpr_eval,
    Expr.eval, Bundle.unpack_pack, Bundle.values_fromValues]

def main : IO Unit := do
  let text ← IO.ofExcept (Emit.moduleText "named_bundle" packetCircuit packetInterface.ports #[]
    packetInterface.ports (fun p => "in_" ++ packetInterface.label p) (fun p => nomatch p)
    (fun p => "out_" ++ packetInterface.label p))
  unless text.contains "in_tag" && text.contains "out_right_value" do
    throw (IO.userError "Named bundle emission lost a field")
  IO.println "Named bundle: codec, field wiring, simulation bindings and RTL names checked."
