import Pinwheel.Hardware.Buffered.SharedBranchProofs
import Lean

open Pinwheel.Hardware Pinwheel.Hardware.Buffered.SharedBranches

open Lean Elab Command in
elab "#audit_buffered_shared_branches" : command => do
  let env ← getEnv
  let mut count : Nat := 0
  let mut proofs : Nat := 0
  for (name, info) in env.constants.toList do
    if name.toString.startsWith "Pinwheel.Hardware.Buffered.SharedBranches." then
      count := count + 1
      if info.isTheorem then proofs := proofs + 1
      let axioms ← collectAxioms name
      let unexpected := axioms.filter fun ax =>
        ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound
      unless unexpected.isEmpty do
        throwError "Unapproved shared-branch circuit axioms: {unexpected}"
  logInfo m!"Buffered shared branches: {count} declarations, {proofs} local theorems; standard axioms only."

#audit_buffered_shared_branches

private structure Command where
  coldInit : Bool := false
  command : Nat := 0
  address : Nat := 0
  word : Nat := 0
  control : Nat := 0
  branch : Nat := 0
  count : Nat := 2
  virtualSpan : Nat := 2
  expectedGeneration : Nat := 1
  expectedTransfer : Nat := 1
  rawInputs : Nat := 0

private def Command.values (c : Command) : Values Input
  | _, .initialize => BitVec.ofBool c.coldInit
  | _, .command => BitVec.ofNat 3 c.command
  | _, .address => BitVec.ofNat 6 c.address
  | _, .word => BitVec.ofNat 64 c.word
  | _, .control => BitVec.ofNat 24 c.control
  | _, .branch => BitVec.ofNat 56 c.branch
  | _, .count => BitVec.ofNat 7 c.count
  | _, .virtualSpan => BitVec.ofNat 11 c.virtualSpan
  | _, .expectedGeneration => BitVec.ofNat 16 c.expectedGeneration
  | _, .expectedTransfer => BitVec.ofNat 16 c.expectedTransfer
  | _, .rawInputs => BitVec.ofNat 2 c.rawInputs
  | _, _ => 0

private structure Snapshot where
  bank : Array Nat

private def Snapshot.values (s : Snapshot) : Values Register := fun {w} r =>
  BitVec.ofNat w (s.bank[registerIndex r]?.getD 0)

private def snapshot (s : Values Register) : Snapshot :=
  ⟨registers.map fun ⟨_,r⟩ => (s r).toNat⟩

private def tick (s : Snapshot) (c : Command := {}) : Snapshot :=
  snapshot (circuit.step c.values s.values)

private def out (s : Snapshot) (o : Output w) (c : Command := {}) : Nat :=
  (circuit.observe c.values s.values o).toNat

private def check (b : Bool) (label : String) : IO Unit :=
  unless b do throw (IO.userError ("Shared-branch circuit failure: " ++ label))

private def loadRows (s : Snapshot) : Snapshot :=
  tick (tick s {command:=1, address:=0, word:=0}) {command:=1, address:=1, word:=3}

private def loadTable (s : Snapshot) : Snapshot :=
  (List.range 16).foldl (fun s k => tick s {command:=6, address:=k}) s

def main : IO Unit := do
  let zero := snapshot (fun _ => 0)
  let cold := tick zero {coldInit:=true}
  check (registers.size == 116) "register enumeration"
  check ((registers.map fun ⟨w,_⟩ => w).foldl (· + ·) 0 == 7183) "allocated state"
  let rows := loadRows cold
  check (rows.values (.core .written) == 3 && rows.values .branchWritten == 0) "row-first coverage"
  check (out rows .rejected {command:=2} == 1) "missing dictionary rejects commit"
  let filled := loadTable rows
  check (filled.values .branchWritten == 65535 && filled.values (.core .written) == 3) "joint coverage"
  let committed := tick filled {command:=2}
  check (out committed .valid == 1 && out committed .generation == 1) "commit"
  let active := tick committed {command:=3}
  check (out active .busy == 1 && out active .phase == 1) "same-edge START entry"
  check (out active .rejected {command:=6, address:=0, branch:=3} == 1) "active dictionary write rejected"
  let heldWrite := tick active {command:=6, address:=0, branch:=3}
  check (heldWrite.values (.branch 0) == 0 && out heldWrite .retained == 1) "rejected command permits ordinary halt edge"
  check (out heldWrite .rejected {command:=6} == 1) "retained dictionary write rejected"
  let released := tick heldWrite {command:=4}
  check (out released .retained == 0) "release"
  let tableFirst := tick released {command:=6, address:=5, branch:=99}
  check (tableFirst.values .branchWritten == 32 && tableFirst.values (.core .written) == 0) "table-first clears both prior masks"
  check (out tableFirst .valid == 0 && out tableFirst .pending == 1) "table-first invalidates generation"
  let invalidRow := tick tableFirst {command:=1, address:=0, branch:=16}
  check (out tableFirst .rejected {command:=1, address:=0, branch:=16} == 1) "row reference upper bits rejected"
  check (invalidRow.values .branchWritten == 32 && invalidRow.values (.core .written) == 0) "invalid row preserves masks"
  let invalidTable := tick invalidRow {command:=6, address:=16}
  check (out invalidRow .rejected {command:=6, address:=16} == 1) "table upper address rejected"
  check (invalidTable.values .branchWritten == 32 && invalidTable.values (.core .written) == 0) "invalid table preserves masks"
  let reset := tick invalidTable {command:=7}
  check (reset.values .branchWritten == 0 && reset.values (.core .written) == 0 && out reset .pending == 0) "warm reset clears pending masks"
  let tableBeforeRows := loadRows (loadTable reset)
  check (tableBeforeRows.values .branchWritten == 65535 && tableBeforeRows.values (.core .written) == 3) "table-before-row generation"
  check (out (tick tableBeforeRows {command:=2}) .valid == 1) "table-before-row commits"
  let malformed := tick reset {command:=6, address:=0, branch:=2^55}
  check (malformed.values (.branch 0) == BitVec.ofNat 56 (2^55)) "full descriptor reserved bits retained"
  IO.println "Buffered shared branches: coverage, range, ownership, same-edge START, and descriptor preservation passed."
