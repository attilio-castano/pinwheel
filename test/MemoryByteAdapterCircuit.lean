import Lean
import Pinwheel.Hardware.Memory.ByteAdapterCircuitProofs

open Lean Elab Command Pinwheel.Hardware Pinwheel.Hardware.Memory
namespace MemoryByteAdapterCircuitTests

def snapshot (d : Interface P) (v : Values P) : Array Nat :=
  d.ports.map fun ⟨_, p⟩ => (v p).toNat

def values (d : Interface P) (bank : Array Nat) : Values P :=
  fun {w} p => BitVec.ofNat w bank[(d.position p).val]!

/-- Independent port/register decoding uses the documented positional schema,
not the circuit view, input decoder, output encoder, or expression helpers. -/
def request (a wr sg sz addr off data : Nat) : ByteAdapterModel.Request a :=
  if wr = 1 then .store (BitVec.ofNat 2 sz) (BitVec.ofNat a addr) (BitVec.ofNat 2 off) (BitVec.ofNat 32 data)
  else .read (sg = 1) (BitVec.ofNat 2 sz) (BitVec.ofNat a addr) (BitVec.ofNat 2 off)

def input (a : Nat) (pins : Array Nat) : ByteAdapterModel.Input a :=
  ⟨pins[0]! = 1, if pins[1]! = 1 then some (request a pins[2]! pins[3]! pins[4]! pins[5]! pins[6]! pins[7]!) else none,
    pins[8]! = 1⟩

def model (a : Nat) (bank : Array Nat) : ByteAdapterModel.State a :=
  let d := 2^a
  ⟨⟨fun address => BitVec.ofNat 32 bank[address.toNat]!, BitVec.ofNat 32 bank[d]!⟩,
    if bank[d+7]! = 1 then some (request a bank[d+1]! bank[d+2]! bank[d+3]! bank[d+4]! bank[d+5]! bank[d+6]!) else none⟩

def output (o : ByteAdapterModel.Output) : Array Nat :=
  let code := match o.offered with
    | none | some (.read _) => 0
    | some .stored => 1
    | some (.fault .reservedSize) => 2
    | some (.fault .misaligned) => 3
  let data := match o.offered with | some (.read value) => value.toNat | _ => 0
  #[if o.ready then 1 else 0, if o.offered.isSome then 1 else 0, code, data]

def memorySnapshot (s : ByteAdapterModel.State a) : Array Nat :=
  (Array.ofFn fun k : Fin (2^a) => (s.memory.contents (BitVec.ofFin k)).toNat).push s.memory.q.toNat

def freeze (s : ByteAdapterModel.State a) : ByteAdapterModel.State a :=
  let bank := memorySnapshot s
  ⟨⟨fun address => BitVec.ofNat 32 bank[address.toNat]!, BitVec.ofNat 32 bank[2^a]!⟩, s.pending⟩

def expectedBank (pins bank : Array Nat) (next : ByteAdapterModel.State a) : Array Nat :=
  let d := 2^a
  let latched := pins[0]! = 0 && bank[d+7]! = 0 && pins[1]! = 1
  let metadata := if latched then #[pins[2]!, pins[3]!, pins[4]!, pins[5]!, pins[6]!, pins[7]!]
    else #[bank[d+1]!, bank[d+2]!, bank[d+3]!, bank[d+4]!, bank[d+5]!, bank[d+6]!]
  memorySnapshot next ++ metadata ++ #[if next.pending.isSome then 1 else 0]

def check (pins bank : Array Nat) (reference : ByteAdapterModel.State a) : IO (Array Nat × ByteAdapterModel.State a) := do
  let ii := ByteAdapterInterface.inputs a
  let ri := ByteAdapterCircuit.registers a
  let oi := ByteAdapterInterface.outputs
  let c := ByteAdapterCircuit.circuit a
  let i : Values (ByteAdapterInterface.Input a) := values ii pins
  let raw : Values (ByteAdapterCircuit.Register a) := values ri bank
  let decoded := ByteAdapterCircuit.view raw
  unless memorySnapshot decoded = memorySnapshot reference && decoded.pending = reference.pending do
    throw (IO.userError "Current raw view disagrees with independent model decoding/history")
  unless snapshot oi (c.observe i raw) = output ((ByteAdapterModel.component a).observe (input a pins) reference) do
    throw (IO.userError "Complete pre-output mismatch")
  let next := ByteAdapterModel.step (input a pins) reference
  let nextBank := snapshot ri (c.step i raw)
  unless nextBank = expectedBank pins bank next do
    throw (IO.userError s!"Complete next-register mismatch: expected {expectedBank pins bank next}, got {nextBank}")
  unless snapshot oi (c.observe i (values ri nextBank)) = output ((ByteAdapterModel.component a).observe (input a pins) next) do
    throw (IO.userError "Complete post-output mismatch")
  return (nextBank, freeze next)

def rawBank (a flags seed : Nat) : Array Nat :=
  (Array.ofFn fun k : Fin (2^a) => (seed*1664525 + k.val*0x10204081 + 0x80ff7f01) % 2^32) ++
    #[(seed*1103515245+12345)%2^32, (flags/2)%2, (flags/4)%2, (flags/8)%4,
      (seed/17)%(2^a), (flags/32)%4, (seed*291+0xf0e1d2c3)%2^32, flags%2]

def rawInput (a flags seed : Nat) : Array Nat :=
  #[flags%2, (flags/2)%2, (flags/4)%2, (flags/8)%2, (seed/13)%4,
    (seed/19)%(2^a), (seed/31)%4, (seed*43+0x800000ff)%2^32, (flags/16)%2]

def campaign (a : Nat) : IO Nat := do
  unless (ByteAdapterInterface.inputs a).size = 9 && ByteAdapterInterface.outputs.size = 4 &&
      (ByteAdapterCircuit.registers a).size = 2^a+8 do throw (IO.userError "Incomplete typed descriptor counts")
  let mut edges := 0
  -- Exhaust every metadata control combination and input handshake combination;
  -- words, Q, operand, addresses and inactive fields are independently varied.
  for stored in [:128] do
    for flags in [:32] do
      let seed := stored*211+flags*97+41
      let bank := rawBank a stored seed
      let _ ← check (rawInput a flags (seed*37+11)) bank (model a bank)
      edges := edges+1
  let mut bank := rawBank a 127 0x62797465
  let mut reference := model a bank
  let mut seed : Nat := 0x12345678
  for cycle in [:1500] do
    seed := (1664525*seed+1013904223)%2^32
    let pins := rawInput a ((seed/1024)%32) seed
    let pins := if cycle = 0 || cycle%137 = 0 then pins.set! 0 1 else pins.set! 0 0
    let result ← check pins bank reference
    bank := result.1
    reference := result.2
    edges := edges+1
  return edges

def wrongCode : Circuit (ByteAdapterInterface.Input 1) (ByteAdapterCircuit.Register 1) ByteAdapterInterface.Output :=
  { ByteAdapterCircuit.circuit 1 with output := fun {b} o => match b, o with
    | _, .at ⟨2, _⟩ => .mux ByteAdapterCircuit.responseValidExpr (.lit 1) (.lit 0)
    | _, o => (ByteAdapterCircuit.circuit 1).output o }

def clearInactiveData : Circuit (ByteAdapterInterface.Input 1) (ByteAdapterCircuit.Register 1) ByteAdapterInterface.Output :=
  { ByteAdapterCircuit.circuit 1 with next := fun {b} r => match b, r with
    | _, .right (.at ⟨5, _⟩) => .lit 0
    | _, r => (ByteAdapterCircuit.circuit 1).next r }

def repeatPending : Circuit (ByteAdapterInterface.Input 1) (ByteAdapterCircuit.Register 1) ByteAdapterInterface.Output :=
  { ByteAdapterCircuit.circuit 1 with next := fun {b} r => match b, r with
    | _, .right (.at ⟨6, _⟩) => .mux (.input ByteAdapterInterface.reset) (.lit 0)
        (.mux (.reg ByteAdapterCircuit.pending) (.lit 1) (.input ByteAdapterInterface.requestValid))
    | _, r => (ByteAdapterCircuit.circuit 1).next r }

def mutationControls : IO Nat := do
  let ri := ByteAdapterCircuit.registers 1
  let ii := ByteAdapterInterface.inputs 1
  let oi := ByteAdapterInterface.outputs
  let raw : Values (ByteAdapterCircuit.Register 1) := values ri (rawBank 1 127 123)
  let inputs : Values (ByteAdapterInterface.Input 1) := values ii #[0, 1, 1, 0, 0, 0, 0, 255, 1]
  unless snapshot oi (wrongCode.observe inputs raw) ≠ snapshot oi ((ByteAdapterCircuit.circuit 1).observe inputs raw) do
    throw (IO.userError "Response-code mutation escaped")
  unless snapshot ri (clearInactiveData.step inputs raw) ≠ snapshot ri ((ByteAdapterCircuit.circuit 1).step inputs raw) do
    throw (IO.userError "Inactive metadata clearing mutation escaped raw-register check")
  unless snapshot ri (repeatPending.step inputs raw) ≠ snapshot ri ((ByteAdapterCircuit.circuit 1).step inputs raw) do
    throw (IO.userError "Repeated acknowledgement mutation escaped")
  return 3

end MemoryByteAdapterCircuitTests

elab "#audit_byte_adapter_circuit" : command => do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "Pinwheel.Hardware.Memory.ByteAdapterInterface." ||
        name.toString.startsWith "Pinwheel.Hardware.Memory.ByteAdapterCircuit." ||
        name.toString.startsWith "MemoryByteAdapterCircuitTests." then
      count := count+1
      let axioms ← collectAxioms name
      let bad := axioms.filter fun a => a != ``propext && a != ``Classical.choice && a != ``Quot.sound
      unless bad.isEmpty do throwError "Unapproved byte circuit axioms in {name}: {bad}"
  if count < 30 then throwError "Incomplete byte circuit audit"
  logInfo m!"Byte circuit audit: {count} declarations, standard axioms only."

#audit_byte_adapter_circuit

def main : IO Unit := do
  let mut edges := 0
  for a in [0, 1, 2, 3] do edges := edges + (← MemoryByteAdapterCircuitTests.campaign a)
  let mutations ← MemoryByteAdapterCircuitTests.mutationControls
  IO.println s!"Byte adapter circuit: {edges} raw-state/trace edges with every register and pre/post output, including retained metadata; {mutations} structural mutation controls rejected."
