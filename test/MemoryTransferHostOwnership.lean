import Lean
import Pinwheel.Hardware.Memory.TransferHostOwnershipCandidate

open Pinwheel.Hardware
open Pinwheel.Hardware.Memory
open Pinwheel.Hardware.Memory.TransferHostInterface

namespace MemoryTransferHostOwnershipTests

def transform (wi wo : Nat) : Stream.Map wi wo :=
  ⟨.slice 0 wo (by omega) (.concat (.lit (0 : BitVec wo)) (.inv (.input .data))),
    fun value => ((0 : BitVec wo) ++ ~~~value).extractLsb' 0 wo, fun _ => rfl⟩

def rawState (a wi wo phase sp dp seed : Nat) : Values (TransferHostCircuit.Register a wi wo)
  | _, .left .phase => BitVec.ofNat 2 phase
  | _, .left .sourceBase => BitVec.ofNat a (seed+3)
  | _, .left .destinationBase => BitVec.ofNat a (seed+5)
  | _, .left .length => BitVec.ofNat (a+1) (seed+1)
  | _, .left .index => BitVec.ofNat (a+1) (seed+7)
  | _, .left .done => BitVec.ofNat 1 seed
  | _, .left .error => BitVec.ofNat 1 (seed/2)
  | _, .right (.left (.left (.left (.word address)))) => BitVec.ofNat wi (seed+address.toNat*19)
  | _, .right (.left (.left (.right .q))) => BitVec.ofNat wi (seed+73)
  | _, .right (.left (.right .valid)) => BitVec.ofNat 1 sp
  | _, .right (.right (.left (.left (.word address)))) => BitVec.ofNat wo (seed+address.toNat*41)
  | _, .right (.right (.left (.right .q))) => BitVec.ofNat wo (seed+151)
  | _, .right (.right (.right .valid)) => BitVec.ofNat 1 dp

def rawInput (a wi wo bits : Nat) : Values (Input a wi wo)
  | _, .at ⟨0, _⟩ => BitVec.ofNat 1 bits
  | _, .at ⟨1, _⟩ => BitVec.ofNat 1 (bits/2)
  | _, .at ⟨2, _⟩ => BitVec.ofNat a (bits/3)
  | _, .at ⟨3, _⟩ => BitVec.ofNat a (bits/5)
  | _, .at ⟨4, _⟩ => BitVec.ofNat (a+1) (bits/7)
  | _, .at ⟨5, _⟩ => BitVec.ofNat 1 (bits/4)
  | _, .at ⟨6, _⟩ => BitVec.ofNat 1 (bits/8)
  | _, .at ⟨7, _⟩ => BitVec.ofNat a (bits*3)
  | _, .at ⟨8, _⟩ => BitVec.ofNat wi (bits*43+19)
  | _, .at ⟨9, _⟩ => BitVec.ofNat 1 (bits/16)
  | _, .at ⟨10, _⟩ => BitVec.ofNat 1 (bits/32)
  | _, .at ⟨11, _⟩ => BitVec.ofNat 1 (bits/64)
  | _, .at ⟨12, _⟩ => BitVec.ofNat a (bits*7)
  | _, .at ⟨13, _⟩ => BitVec.ofNat wo (bits*23+83)
  | _, .at ⟨14, _⟩ => BitVec.ofNat 1 (bits/128)
  | _, .at ⟨k+15, h⟩ => False.elim (by change k+15 < 15 at h; omega)

def snapshot (d : Interface P) (v : Values P) : Array Nat :=
  d.ports.map fun ⟨_, p⟩ => (v p).toNat

def configuration (a wi wo : Nat) : IO Nat := do
  let original := TransferHostCircuit.circuit (a := a) (transform wi wo)
  let candidate := TransferHostOwnershipCandidate.circuit (a := a) (transform wi wo)
  let ri := TransferHostCircuit.registers a wi wo
  let oi := outputs wi wo
  let mut count := 0
  for phase in [0:4] do
    for sourcePending in [0:2] do
      for destinationPending in [0:2] do
        for flags in [0:256] do
          let s : Values (TransferHostCircuit.Register a wi wo) :=
            rawState a wi wo phase sourcePending destinationPending (flags*13+11)
          let i : Values (Input a wi wo) := rawInput a wi wo flags
          unless snapshot ri (candidate.step i s) == snapshot ri (original.step i s) &&
              snapshot oi (candidate.observe i s) == snapshot oi (original.observe i s) do
            throw (IO.userError s!"ownership mismatch a{a}/{wi}/{wo} phase{phase} pending{sourcePending}/{destinationPending} flags{flags}")
          count := count+1
  return count

end MemoryTransferHostOwnershipTests

open Lean Elab Command

elab "#audit_transfer_host_ownership" : command => do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "Pinwheel.Hardware.Memory.TransferHostOwnershipCandidate." ||
        name.toString.startsWith "_private.Pinwheel.Hardware.Memory.TransferHostOwnershipCandidate." then
      count := count+1
      let axioms ← collectAxioms name
      let bad := axioms.filter fun a => a != ``propext && a != ``Classical.choice && a != ``Quot.sound
      unless bad.isEmpty do throwError "Unapproved ownership axioms in {name}: {bad}"
  if count == 0 then throwError "Empty ownership proof audit"
  logInfo m!"Host ownership audit: {count} declarations, standard axioms only."

#audit_transfer_host_ownership

def main : IO Unit := do
  let mut count := 0
  for (a, wi, wo) in [(0, 0, 0), (1, 1, 1), (2, 8, 8), (3, 8, 4), (2, 4, 17)] do
    count := count + (← MemoryTransferHostOwnershipTests.configuration a wi wo)
  IO.println s!"Host ownership: {count} raw phase/pending/handshake combinations; every state register and output agrees, including malformed control and zero widths."
