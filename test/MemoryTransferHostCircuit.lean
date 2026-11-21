import Lean
import Pinwheel.Hardware.Memory.TransferHostCircuitProofs

open Lean Elab Command
open Pinwheel.Hardware Pinwheel.Hardware.Memory

namespace MemoryTransferHostCircuitTests

def values (d : Interface P) (bank : Array Nat) : Values P :=
  fun {w} p => BitVec.ofNat w bank[(d.position p).val]!

def snapshot (d : Interface P) (v : Values P) : Array Nat :=
  d.ports.map (fun ⟨_, p⟩ => (v p).toNat)

def transform (wi wo : Nat) : Stream.Map wi wo :=
  ⟨.slice 0 wo (by omega) (.concat (.lit (0 : BitVec wo)) (.inv (.input .data))),
    fun value => ((0 : BitVec wo) ++ ~~~value).extractLsb' 0 wo, fun _ => rfl⟩

def initial (a wi wo : Nat) : TransferModel.State a wi wo :=
  TransferModel.initialState
    ⟨fun address => BitVec.ofNat wi (17*address.toNat+11), BitVec.ofNat wi 123⟩
    ⟨fun address => BitVec.ofNat wo (23*address.toNat+5), BitVec.ofNat wo 199⟩

def materializeMemory (a w : Nat) (s : Sram.State a w) : Sram.State a w :=
  let array := (Array.range (2^a)).map (fun n => s.contents (BitVec.ofNat a n))
  ⟨fun address => array[address.toNat]!, s.q⟩

def materialize (a wi wo : Nat) (s : TransferModel.State a wi wo) : TransferModel.State a wi wo :=
  { s with
    source := { s.source with memory := materializeMemory a wi s.source.memory }
    destination := { s.destination with memory := materializeMemory a wo s.destination.memory } }

def quiet : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1]

def traffic (a wi wo : Nat) : Array (Array Nat) := Id.run do
  let depth := 2^a
  let mut rows := #[quiet.set! 0 1]
  for address in [0:depth] do
    rows := rows.push #[0, 0, 0, 0, 0, 1, 1, address, (17*address+13)%2^wi, 1,
      1, 1, address, (29*address+7)%2^wo, 1]
  let noisy := #[0, 1, depth-1, depth-1, 2*depth-1, 1, 1, 0, 2^wi-1, 0, 1, 1, 0, 2^wo-1, 0]
  rows := rows.push (((noisy.set! 2 0).set! 3 0).set! 4 depth)
  for _ in [0:2*depth] do rows := rows.push noisy
  for address in [0:depth] do
    rows := rows.push #[0, 0, 0, 0, 0, 1, 0, address, 0, 1, 1, 0, address, 0, 1]
  rows := rows.push quiet
  rows := rows.push #[0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 1]
  let waiting := (((noisy.set! 2 0).set! 3 0).set! 4 1)
  rows := rows.push waiting |>.push (waiting.set! 9 1) |>.push ((waiting.set! 9 1).set! 14 1)
  rows := rows.push waiting |>.push noisy |>.push noisy |>.push quiet
  let mut seed := 49157
  for _ in [0:512] do
    seed := (1664525*seed+1013904223)%4294967296
    rows := rows.push #[if seed%37 == 0 then 1 else 0, if seed%5 == 0 then 1 else 0,
      (seed/3)%depth, (seed/7)%depth, (seed/11)%(2*depth),
      (seed/13)%2, (seed/17)%2, (seed/19)%depth, (seed/23)%2^wi, (seed/29)%2,
      (seed/31)%2, (seed/41)%2, (seed/43)%depth, (seed/47)%2^wo, (seed/53)%2]
  rows := rows.push (quiet.set! 0 1) |>.push quiet
  return rows

def replay (a wi wo : Nat) : IO Nat := do
  let m := transform wi wo
  let c := TransferHostCircuit.circuit (a := a) m
  let ri := TransferHostCircuit.registers a wi wo
  let ii := TransferHostInterface.inputs a wi wo
  let oi := TransferHostInterface.outputs wi wo
  let mut logical := initial a wi wo
  let mut bank := snapshot ri (TransferHostCircuit.encode logical)
  let mut count := 0
  for row in traffic a wi wo do
    let input : Values (TransferHostInterface.Input a wi wo) := values ii row
    let physical : Values (TransferHostCircuit.Register a wi wo) := values ri bank
    unless snapshot oi (c.observe input physical) == snapshot oi ((TransferHostInterface.spec m).observe input logical) do
      throw (IO.userError s!"a={a} {wi}->{wo} edge {count}: pre-edge host output mismatch")
    bank := snapshot ri (c.step input physical)
    logical := materialize a wi wo ((TransferHostInterface.spec m).step input logical)
    unless bank == snapshot ri (TransferHostCircuit.encode logical) do
      throw (IO.userError s!"a={a} {wi}->{wo} edge {count}: complete controller/memory/pending state mismatch")
    unless snapshot oi (c.observe input (values ri bank)) == snapshot oi ((TransferHostInterface.spec m).observe input logical) do
      throw (IO.userError s!"a={a} {wi}->{wo} edge {count}: post-edge host output mismatch")
    count := count+1
  return count

def rawRecovery (a wi wo : Nat) : IO Nat := do
  let m := transform wi wo
  let c := TransferHostCircuit.circuit (a := a) m
  let ri := TransferHostCircuit.registers a wi wo
  let oi := TransferHostInterface.outputs wi wo
  let ii := TransferHostInterface.inputs a wi wo
  let raw : Values (TransferHostCircuit.Register a wi wo) := fun {b} _ => BitVec.ofNat b (2^b-1)
  let mut count := 0
  for reset in [0, 1] do
    let row := #[reset, 1, 0, 0, 1, 1, 1, 0, 0, 1, 1, 1, 0, 0, 1]
    let input : Values (TransferHostInterface.Input a wi wo) := values ii row
    unless (snapshot oi (c.observe input raw)).all (· == 0) do
      throw (IO.userError "raw reset/reserved phase leaked a host transaction or status")
    let expected : TransferModel.State a wi wo :=
      { TransferHostCircuit.resetState raw with
        control := { TransferModel.initialControl a with error := reset == 0 } }
    unless snapshot ri (c.step input raw) == snapshot ri (TransferHostCircuit.encode expected) do
      throw (IO.userError "raw reset/reserved-phase recovery changed memory/Q or failed to cancel pending work")
    count := count+1
  return count

end MemoryTransferHostCircuitTests

elab "#audit_transfer_host_circuit" : command => do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "Pinwheel.Hardware.Memory.TransferHost" ||
        name.toString.startsWith "_private.Pinwheel.Hardware.Memory.TransferHost" then
      count := count+1
      let axioms ← collectAxioms name
      let bad := axioms.filter fun a => a != ``propext && a != ``Classical.choice && a != ``Quot.sound
      unless bad.isEmpty do throwError "Unapproved axioms in {name}: {bad}"
  if count == 0 then throwError "Empty host hardware audit"
  logInfo m!"Transfer host circuit audit: {count} declarations, standard axioms only."

#audit_transfer_host_circuit

def main : IO Unit := do
  let mut edges := 0
  let mut recoveries := 0
  for (a, wi, wo) in [(0, 0, 0), (1, 1, 1), (2, 8, 8), (3, 8, 4), (2, 4, 17)] do
    edges := edges + (← MemoryTransferHostCircuitTests.replay a wi wo)
    recoveries := recoveries + (← MemoryTransferHostCircuitTests.rawRecovery a wi wo)
  IO.println s!"Transfer host circuit: {edges} complete-state/pre/post-output model replay edges; {recoveries} arbitrary raw reset/reserved-phase recoveries passed."
