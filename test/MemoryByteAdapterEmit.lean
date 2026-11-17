import Pinwheel.Hardware.Memory.ByteAdapterCircuit
import Pinwheel.Hardware.Emit
import Lean.Data.Json

open Lean Pinwheel.Hardware Pinwheel.Hardware.Memory

namespace MemoryByteAdapterEmit

private def portsJson (d : Interface P) : Json :=
  toJson (d.ports.map fun ⟨w, p⟩ => Json.mkObj
    [("index", toJson (d.position p).val), ("name", toJson (d.label p)), ("width", toJson w)])

def emit (a : Nat) (out : String) : IO Unit := do
  let ii := ByteAdapterInterface.inputs a
  let oi := ByteAdapterInterface.outputs
  let ri := ByteAdapterCircuit.registers a
  let moduleName := s!"byte_adapter_a{a}_w32"
  let registerName := fun {b} (r : ByteAdapterCircuit.Register a b) => "r_" ++ ri.label r
  IO.FS.createDirAll out
  IO.FS.writeFile (out ++ "/byte-adapter.mlir") (← IO.ofExcept
    (Emit.moduleText moduleName (ByteAdapterCircuit.circuit a)
      ii.ports ri.ports oi.ports ii.label ri.label oi.label))
  let regs := toJson (ri.ports.map fun ⟨b, r⟩ => Json.mkObj
    [("index", toJson (ri.position r).val), ("name", toJson (registerName r)),
     ("reference", toJson (registerName r)), ("width", toJson b)])
  let roles := Json.mkObj
    [("reset", toJson (ii.label ByteAdapterInterface.reset)),
     ("request_valid", toJson (ii.label ByteAdapterInterface.requestValid)),
     ("write", toJson (ii.label ByteAdapterInterface.write)),
     ("signed", toJson (ii.label ByteAdapterInterface.signed)),
     ("size", toJson (ii.label ByteAdapterInterface.size)),
     ("address", toJson (ii.label ByteAdapterInterface.address)),
     ("offset", toJson (ii.label ByteAdapterInterface.offset)),
     ("data", toJson (ii.label ByteAdapterInterface.data)),
     ("response_ready", toJson (ii.label ByteAdapterInterface.responseReady)),
     ("request_ready", toJson (oi.label ByteAdapterInterface.requestReady)),
     ("response_valid", toJson (oi.label ByteAdapterInterface.responseValid)),
     ("response_code", toJson (oi.label ByteAdapterInterface.responseCode)),
     ("response_data", toJson (oi.label ByteAdapterInterface.responseData))]
  let registerRoles := Json.mkObj
    [("words", toJson (Array.ofFn (fun k : Fin (2^a) =>
        registerName (.left (CommandFlops.word (BitVec.ofFin k)))))),
     ("q", toJson (registerName (.left CommandFlops.q))),
     ("write", toJson (registerName (.right ByteAdapterCircuit.metaWrite))),
     ("signed", toJson (registerName (.right ByteAdapterCircuit.metaSigned))),
     ("size", toJson (registerName (.right ByteAdapterCircuit.metaSize))),
     ("address", toJson (registerName (.right ByteAdapterCircuit.metaAddress))),
     ("offset", toJson (registerName (.right ByteAdapterCircuit.metaOffset))),
     ("data", toJson (registerName (.right ByteAdapterCircuit.metaData))),
     ("pending", toJson (registerName ByteAdapterCircuit.pending))]
  let descriptor := Json.mkObj
    [("schema", toJson (1 : Nat)), ("module", toJson moduleName),
     ("address_width", toJson a), ("data_width", toJson (32 : Nat)), ("depth", toJson (2^a)),
     ("clock", toJson "clk"), ("inputs", portsJson ii), ("outputs", portsJson oi),
     ("registers", regs), ("roles", roles), ("register_roles", registerRoles),
     ("response_codes", Json.mkObj [("read", toJson (0 : Nat)), ("stored", toJson (1 : Nat)),
       ("reserved_size", toJson (2 : Nat)), ("misaligned", toJson (3 : Nat))]),
     ("startup", toJson "arbitrary words, Q, six retained metadata fields and pending; no power-up initialization"),
     ("reset_behavior", toJson "suppresses both handshakes and clears pending only; preserves words, Q and all request metadata"),
     ("commit_behavior", toJson "valid store changes memory only on response acceptance; faulting requests issue no memory command")]
  IO.FS.writeFile (out ++ "/interface.json") (descriptor.pretty ++ "\n")
  IO.println s!"Byte adapter {2^a}x32: {ri.size} registers emitted to {out}."

end MemoryByteAdapterEmit

def main (args : List String) : IO Unit := do
  let [a, out] := args | throw (IO.userError "Usage: memory_byte_adapter_emit ADDRESS_WIDTH outdir")
  let some a := a.toNat? | throw (IO.userError "Invalid address width")
  unless a > 0 do throw (IO.userError "HDL export requires a positive address width")
  MemoryByteAdapterEmit.emit a out
