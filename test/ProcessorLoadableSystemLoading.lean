import Lean
import Pinwheel.Hardware.Processor.LoadableSystemProofs

open Lean Elab Pinwheel.Hardware Pinwheel.Hardware.Processor

namespace ProcessorLoadableSystemLoadingTests
open LoadableSystem Memory

/-- Independent integer bank oracle: controller/device/fetch registers reset;
only an admitted fullword write changes RAM; Q and inactive metadata retain. -/
def expected (row : Array Nat) (old : Values (Register aw)) :
    {b : Nat} → Register aw b → Nat
  | _, .left _ => 0
  | _, .right (.left (.left (.left (.word k)))) =>
      if row[0]! == 0 && row[6]! == 1 && row[7]! == 1 && row[8]! % 2^aw == k.toNat
      then row[9]! % 2^32 else (old (word k)).toNat
  | _, .right (.left (.left (.right .q))) => (old q).toNat
  | _, .right (.left (.right (.at k))) =>
      if k.val == 6 then 0 else (old (SystemCircuit.ram (.right (.at k)))).toNat
  | _, .right (.right _) => 0

def pins (row : Array Nat) : Values (Input aw) := fun {b} p =>
  BitVec.ofNat b row[((inputs aw).position p).val]!

def row (reset mode valid address data : Nat) : Array Nat :=
  #[reset, 0xdeadbeef, 1, 1, 0xa5, 1, mode, valid, address, data]

def image (k : Nat) : Nat := (0x89abcdef + k * 0x1020304) % 2^32

def check (a : Nat) (fits : a ≤ 30) (seed : Nat) : IO Nat := do
  let some layout := AddressMap.check (romWidth := 0) (ramWidth := a)
      ⟨0x10000, 0x40000000, 0x40000100, 0x40000200⟩
    | throw (IO.userError "Invalid fixture layout")
  let rom : BitVec 0 → BitVec 32 := fun _ => 0x00100073
  let bank := registers a
  let mut raw : Values (Register a) := fun {b} r =>
    BitVec.ofNat b (if seed == 0 then 2^b-1 else
      0x31415927 + seed * 0x13579 + (bank.position r).val * 0x10203)
  let oldQ := raw q
  let mut traffic := [row 1 0 1 0 0, row 1 1 1 (2^a-1) 0xffffffff,
    row 0 1 0 0 0x12345678]
  for k in (List.range (2^a)).reverse do
    traffic := traffic ++ [row 0 1 1 k (image k), row 0 1 0 k 0xdeadbeef]
  -- Repeated accepted writes and reset-valid edges must preserve the image.
  traffic := traffic ++ [row 0 1 1 0 (image 0), row 1 1 1 0 0, row 0 1 0 0 0]
  for cycle in [:traffic.length] do
    let r := traffic[cycle]!
    let i : Values (Input a) := pins r
    let out := outputSnapshot layout rom (by decide) fits i raw
    unless (out.values (.right (.at ⟨0,by decide⟩))).toNat ==
        (r[6]! == 1 && r[0]! == 0).toNat do
      throw (IO.userError s!"a{a}/seed{seed}/cycle{cycle}: admission output mismatch")
    unless out.values (.right (.at ⟨1,by decide⟩)) == 0 do
      throw (IO.userError "Loader/reset unexpectedly reports running")
    let next := nextSnapshot layout rom (by decide) fits i raw
    for ⟨_,p⟩ in bank.ports do
      unless (next.values p).toNat == expected r raw p do
        throw (IO.userError s!"a{a}/seed{seed}/cycle{cycle}/{bank.label p}: raw register mismatch")
    raw := next.values
  for k in [:2^a] do
    unless (raw (word (BitVec.ofNat a k))).toNat == image k do
      throw (IO.userError "Complete image differs from supplied fullword values")
  unless raw q == oldQ do throw (IO.userError "Loading changed old Q")
  let logical := SystemCircuit.view raw
  unless logical.core.arch.pc == 0 && logical.fetch.isNone && logical.ram.pending.isNone &&
      logical.mmio == MmioModel.initial do
    throw (IO.userError "Final view is not quiescent")
  return traffic.length

theorem artifact_loaded_final_memory (layout : AddressMap.Layout rw aw) (rom : SystemModel.Rom rw)
    (romFits : rw ≤ 30) (ramFits : aw ≤ 30)
    (rtl : Timed.Component (Values (Input aw)) (Values (Register aw)) (Values Output))
    (artifact : Artifact.Correspondence (circuit layout rom romFits ramFits) rtl)
    (raw : Values (Register aw)) (loading traffic : List (Values (Input aw)))
    (modeHeld : ∀ i ∈ loading, i mode = 1) (image : BitVec aw → BitVec 32)
    (values : ImageWrites image loading) (coverage : Covers loading)
    (modeOff : ∀ i ∈ traffic, i mode = 0) :
    (SystemCircuit.view (rtl.run (rtl.run raw loading) traffic)).ram.memory =
      ((SystemModel.component layout rom).run (SystemModel.initial image (raw q))
        (traffic.map (fun i => SystemCircuit.decode (systemPins i)))).ram.memory := by
  rw [artifact_run_after_loading layout rom romFits ramFits rtl artifact raw loading traffic modeHeld image values coverage modeOff]

elab "#audit_loading" : command => do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "Pinwheel.Hardware.Processor.LoadableSystem." ||
        name.toString.startsWith "_private.Pinwheel.Hardware.Processor.LoadableSystem" ||
        name.toString.startsWith "ProcessorLoadableSystemLoadingTests." then
      let axioms ← collectAxioms name
      let bad := axioms.filter fun a => a != ``propext && a != ``Classical.choice && a != ``Quot.sound
      unless bad.isEmpty do throwError "Nonstandard loading axiom in {name}: {bad}"
      count := count+1
  if count < 200 then throwError "Incomplete loading audit"
  logInfo m!"Loadable system audit: {count} declarations, standard axioms only."

#audit_loading

def main : IO Unit := do
  let mut edges := 0
  for seed in [:3] do
    edges := edges + (← check 0 (by decide) seed)
    edges := edges + (← check 1 (by decide) seed)
    edges := edges + (← check 3 (by decide) seed)
  IO.println s!"Loadable system loading: {edges} independent all-register edges; RAM widths 0/1/3, three arbitrary startup patterns, reset/idle/repeated writes/full images."

end ProcessorLoadableSystemLoadingTests

def main := ProcessorLoadableSystemLoadingTests.main
