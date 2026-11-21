import Lean
import Pinwheel.Hardware.Arbitration.RoundRobinMasked
import Pinwheel.Hardware.Emit

open Pinwheel.Hardware Pinwheel.Hardware.Arbitration
open RoundRobinCircuit
open Lean Elab Command

elab "#audit_round_robin_masked" : command => do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "Pinwheel.Hardware.Arbitration.RoundRobinMasked." then
      count := count + 1
      let axioms ← collectAxioms name
      let bad := axioms.filter fun a => a != ``propext && a != ``Classical.choice && a != ``Quot.sound
      unless bad.isEmpty do throwError "Unapproved axioms in {name}: {bad}"
  if count == 0 then throwError "Empty masked round-robin proof audit"
  logInfo m!"Masked round-robin audit: {count} declarations, standard axioms only."

#audit_round_robin_masked

example (cursor request : Fin (n+1) → Expr I R 1) (value : Fin (n+1) → Expr I R w)
    (fallback : Expr I R w) (position : Fin (n+1)) (i : Values I) (s : Values R)
    (hc : ∀ j, (cursor j).eval i s = BitVec.ofBool (j == position)) :
    (RoundRobinMasked.selection cursor request value fallback).eval i s =
      match RoundRobin.grant position (fun j => (request j).eval i s == 1) with
      | none => fallback.eval i s
      | some winner => (value winner).eval i s :=
  RoundRobinMasked.raw_selection_eval cursor request value fallback position i s hc

example (inputs : Values (Inputs n)) (cursor : Fin (n+1))
    (h : CursorEncoding inputs cursor) (p : Outputs n w) :
    (RoundRobinMasked.circuit n).observe inputs NoRegister.values p =
      (RoundRobinCircuit.circuit n).observe inputs NoRegister.values p :=
  RoundRobinMasked.observe_eq_rotated inputs cursor h p

private def portsJson (ps : Array (Sigma P)) (label : {w : Nat} → P w → String) : Json :=
  toJson (ps.map fun ⟨w, p⟩ => Json.mkObj [("name", toJson (label p)), ("width", toJson w)])

private def emit (out : String) (extra : Nat) : IO Unit := do
  let count := extra + 1
  let moduleName := s!"round_robin_masked_{count}"
  let ii := inputInterface extra
  let oi := outputInterface extra
  let text ← IO.ofExcept (Emit.moduleText moduleName (RoundRobinMasked.circuit extra)
    ii.ports #[] oi.ports ii.label (fun r => nomatch r) oi.label)
  IO.FS.writeFile (out ++ s!"/rr_{count}.mlir") text
  let descriptor := Json.mkObj
    [("schema", toJson (1 : Nat)), ("module", toJson moduleName), ("request_count", toJson count),
     ("inputs", portsJson ii.ports ii.label), ("outputs", portsJson oi.ports oi.label),
     ("registers", toJson (#[] : Array Json)),
     ("requests", toJson ((List.finRange count).map fun k => ii.label (requestPort k))),
     ("cursor", toJson ((List.finRange count).map fun k => ii.label (cursorPort k))),
     ("grants", toJson ((List.finRange count).map fun k => oi.label (grantPort k))),
     ("any_grant", toJson (oi.label anyPort)), ("cursor_encoding", toJson "one_hot"),
     ("latency_cycles", toJson (0 : Nat)), ("algorithm", toJson "two_pass_masked_priority")]
  IO.FS.writeFile (out ++ s!"/rr_{count}.json") (descriptor.pretty ++ "\n")

def main (args : List String) : IO Unit := do
  let mut selections := 0
  for extra in [0, 1, 2, 3, 4, 7] do
    let count := extra + 1
    for mask in [:2^count] do
      for cursor in List.finRange count do
        let request : Fin (extra+1) → Bool := fun i => (mask / 2^i.val) % 2 == 1
        let expected := (List.range count).findSome? fun offset =>
          let index := (cursor.val + offset) % count
          if (mask / 2^index) % 2 == 1 then some index else none
        let observed := (RoundRobinMasked.circuit extra).observe (inputValues cursor request) NoRegister.values
        for k in List.finRange count do
          unless observed (grantPort k) == BitVec.ofBool (expected == some k.val) do
            throw (IO.userError s!"Masked grant mismatch: N={count}, cursor={cursor.val}, mask={mask}, grant={k.val}")
        unless observed anyPort == BitVec.ofBool expected.isSome do
          throw (IO.userError s!"Masked any-grant mismatch: N={count}, cursor={cursor.val}, mask={mask}")
        -- Exercise the reusable value mux independently of the grant wrapper,
        -- including a nonzero fallback when there are no requesters.
        let value : Nat → BitVec 17 := fun k => BitVec.ofNat 17 ((mask+3)*k+17)
        let wire : Expr (Inputs extra) NoRegister 17 := RoundRobinMasked.selection
          (fun k => .input (cursorPort k)) (fun k => .input (requestPort k))
          (fun k => .lit (value k.val)) (.lit 131071)
        let expectedValue := expected.map value |>.getD 131071
        unless wire.eval (inputValues cursor request) NoRegister.values == expectedValue do
          throw (IO.userError s!"Masked value mismatch: N={count}, cursor={cursor.val}, mask={mask}")
        selections := selections + 1
  if let some out := args.head? then
    IO.FS.createDirAll out
    for extra in [0, 1, 2, 4, 7] do emit out extra
    IO.println s!"Emitted masked selector MLIR and descriptors to {out}."
  IO.println s!"Masked round-robin: {selections} exhaustive selections and 17-bit values passed."
