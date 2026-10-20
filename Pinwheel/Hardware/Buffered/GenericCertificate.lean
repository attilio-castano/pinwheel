import Pinwheel.Hardware.Buffered.GenericLayout

/-! A representation certificate contains only finite image, encoding and
layout conditions. It contains no execution-step, trace or pin agreement. -/
namespace Pinwheel.Hardware.Buffered.GenericCertificate
open Pinwheel.Hardware Pinwheel.Program GenericLayout

def checkInput : Values Reactive.Input
  | _, .command => 3
  | _, _ => 0

def checkState (word : BitVec 64) (branch : BitVec 56) : Values Reactive.Register
  | _, .word _ => branch ++ (0 : BitVec 24) ++ word
  | _, .valid => 1
  | _, _ => 0

/-- The actual combinational word validator, evaluated at a fixed static
witness that presents the supplied word. No clock step is involved. -/
def WordCanonical (word : BitVec 64) : Prop :=
  Reactive.canonical.eval checkInput (checkState word 0) = 1

def BranchCanonical (word : BitVec 64) (branch : BitVec 56) : Prop :=
  Reactive.branchCanonical.eval checkInput (checkState word branch) = 1

def controlValid (control : BitVec 24) (q : Coordinates) : Bool :=
  let depth := control.extractLsb' 0 2
  let outerStart := control.extractLsb' 2 6
  let innerStart := control.extractLsb' 11 6
  let common := control.extractLsb' 22 2 == 0 &&
    decide (outerStart.toNat ≤ (q.row.extractLsb' 0 6).toNat) &&
    decide (q.outer.toNat ≤ (control.extractLsb' 8 3).toNat)
  if depth == 0 then control == 0 && q.outer == 0 && q.inner == 0
  else if depth == 1 then common && control.extractLsb' 11 9 == 0 && !control[21] && q.inner == 0
  else if depth == 2 then common &&
    decide (innerStart.toNat ≤ (q.row.extractLsb' 0 6).toNat) &&
    decide (outerStart.toNat ≤ innerStart.toNat) &&
    decide (q.inner.toNat ≤ (control.extractLsb' 17 3).toNat) && (!control[20] || control[21])
  else false

def nextNormalizes (pc : Program.Buffered.PC) (word : BitVec 64) (branch : BitVec 56) : Bool :=
  !(word.extractLsb' 0 3 == 6 && branch.extractLsb' 0 2 == 2 && pc.val == 1023 &&
    (branch[6] || branch[30]))

structure Layout (p : Program.Buffered.Program) where
  count : Fin 65
  positive : 0 < count.val
  words : BitVec 6 → BitVec 144
  map : Program.Buffered.PC → Coordinates
  initial : map 0 = ⟨0, 0, 0⟩
  endpoints : ∀ pc, (map pc).row.toNat ≤ 64 ∧
    ((map pc).row = 64 → (map pc).outer = 0 ∧ (map pc).inner = 0)
  rowBound : ∀ pc, pc.val < p.code.span → (map pc).row.toNat < count.val
  sourceRecord : ∀ pc, pc.val < p.code.span →
    ∃ i, p.fetch pc = some i ∧
      words ((map pc).row.setWidth 6) =
        GenericLayout.record map ((words ((map pc).row.setWidth 6)).extractLsb' 64 24) i
  canonical : ∀ pc, pc.val < p.code.span →
    WordCanonical ((words ((map pc).row.setWidth 6)).extractLsb' 0 64)
  branchCanonical : ∀ pc, pc.val < p.code.span →
    BranchCanonical ((words ((map pc).row.setWidth 6)).extractLsb' 0 64)
      ((words ((map pc).row.setWidth 6)).extractLsb' 88 56)
  controlCanonical : ∀ pc, pc.val < p.code.span →
    controlValid ((words ((map pc).row.setWidth 6)).extractLsb' 64 24) (map pc) = true
  normalizes : ∀ pc, pc.val < p.code.span →
    nextNormalizes pc ((words ((map pc).row.setWidth 6)).extractLsb' 0 64)
      ((words ((map pc).row.setWidth 6)).extractLsb' 88 56) = true
  successor : ∀ pc (within : pc.val + 1 < p.code.span),
    GenericLayout.sequential ((words ((map pc).row.setWidth 6)).extractLsb' 64 22) (map pc) =
      map ⟨pc.val + 1, by have := p.fits; omega⟩

end Pinwheel.Hardware.Buffered.GenericCertificate
