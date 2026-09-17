import Pinwheel.Hardware.Storage.EnabledBackend
import Pinwheel.Hardware.Storage.BackendEmit

open Pinwheel.Hardware Pinwheel.Hardware.Loader Pinwheel.Hardware.Storage
open Backend

private def ensure (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private inductive ToyIn : Nat → Type where
  | load : ToyIn 1
  | value : ToyIn 6
private inductive ToyReg : Nat → Type where
  | low : ToyReg 5

private def inputs (load : BitVec 1) (value : BitVec 6) : Values ToyIn
  | _, .load => load
  | _, .value => value
private def state (low : BitVec 5) : Values ToyReg
  | _, .low => low

/-- A five-bit register holding the low field of a six-bit logical value. -/
private def narrow : Expr ToyIn ToyReg 5 :=
  Expr.slice 0 5 (by decide) (Expr.mux (Expr.input ToyIn.load) (Expr.input ToyIn.value)
    (Expr.concat (Expr.lit (0#1)) (Expr.reg ToyReg.low)))

def main : IO Unit := do
  -- The shape reader pushes the slice into the data and keeps the enable.
  let some view := narrow.updateShape | throw (IO.userError "slice-mux shape not recognized")
  for (load, value, old) in [(1, 45, 7), (0, 45, 7), (1, 63, 0), (0, 0, 31)] do
    let i : Values ToyIn := inputs (BitVec.ofNat 1 load) (BitVec.ofNat 6 value)
    let s : Values ToyReg := state (BitVec.ofNat 5 old)
    let expected := if load == 1 then BitVec.ofNat 5 (value % 32) else BitVec.ofNat 5 old
    ensure (narrow.eval i s == expected) "narrow register reference"
    ensure ((if view.enable.eval i s == 1 then view.data.eval i s else s ToyReg.low) == expected)
      "certified view must describe the same update"
    ensure ((view.next ToyReg.low).eval i s == expected) "recirculating encoding of the view"
  -- A multiplexer that does not hold the register must not be mistaken for an update by policy.
  let storing := Backend.registers.filter fun ⟨_, r⟩ => Enabled.stores r
  ensure (storing.size == 581 && storing.foldl (fun n q => n + q.1) (0 : Nat) == 6172) "storing registers and bits"
  for body in [BankSelect.body, CacheEnable.body] do
    ensure (storing.all fun ⟨_, r⟩ => (Enabled.update body r).isSome) "every storing register has a view"
    ensure (Backend.registers.all fun ⟨_, r⟩ => Enabled.stores r || (Enabled.update body r).isNone)
      "control and core registers must not be viewed as plain updates"
  let count (p : Enabled.Policy) :=
    let gated := Backend.registers.filter fun ⟨_, r⟩ => p.gates r
    (gated.size, gated.foldl (fun n q => n + q.1) (0 : Nat))
  ensure (count .none == (0, 0) && count .dictionary == (66, 3536) && count .storage == (580, 6108))
    "gating plans"
  ensure ([Enabled.Policy.none, .dictionary, .storage].all fun p => !p.gates Register.current)
    "the cached word must never be gated"
  IO.println "Enables: slice-mux view, storing registers, certified views of both bodies, and gating plans passed."
