import Lean
import Pinwheel.Hardware.Arbitration.RoundRobinCircuit
import Pinwheel.Hardware.Emit

open Pinwheel.Hardware Pinwheel.Hardware.Arbitration
open RoundRobinCircuit
open Lean Elab Command

elab "#audit_round_robin_circuit" : command => do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "Pinwheel.Hardware.Arbitration.RoundRobinCircuit." then
      count := count + 1
      let axioms ← collectAxioms name
      let bad := axioms.filter fun a => a != ``propext && a != ``Classical.choice && a != ``Quot.sound
      unless bad.isEmpty do throwError "Unapproved axioms in {name}: {bad}"
  if count == 0 then throwError "Empty structural round-robin proof audit"
  logInfo m!"Structural round-robin audit: {count} declarations, standard axioms only."

#audit_round_robin_circuit

-- The smallest supported selector still has genuine one-bit request, cursor,
-- grant and anyGrant ports; no zero-width index encoding is needed.
example : (inputInterface 0).ports.size = 2 := rfl
example : (outputInterface 0).ports.size = 2 := rfl
example : (circuit 0).observe (inputValues 0 (fun _ => true)) NoRegister.values (grantPort 0) = 1 := rfl
example : (circuit 0).observe (inputValues 0 (fun _ => false)) NoRegister.values anyPort = 0 := rfl

example (n : Nat) (inputs : Values (Inputs n)) (cursor : Fin (n + 1))
    (legal : CursorEncoding inputs cursor) (p : Outputs n w) :
    (circuit n).observe inputs NoRegister.values p =
      outputValues (RoundRobin.grant cursor (fun k => inputs (requestPort k) == 1)) p :=
  raw_output_eq inputs cursor legal p

private def portsJson (ps : Array (Sigma P)) (label : {w : Nat} → P w → String) : Lean.Json :=
  Lean.toJson (ps.map fun ⟨w, p⟩ => Lean.Json.mkObj
    [("name", Lean.toJson (label p)), ("width", Lean.toJson w)])

private def emit (out : String) (extra : Nat) : IO Unit := do
  let count := extra + 1
  let moduleName := s!"round_robin_{count}"
  let ii := inputInterface extra
  let oi := outputInterface extra
  let text ← IO.ofExcept (Emit.moduleText moduleName (circuit extra) ii.ports #[] oi.ports
    ii.label (fun r => nomatch r) oi.label)
  IO.FS.writeFile (out ++ s!"/rr_{count}.mlir") text
  let descriptor := Lean.Json.mkObj
    [("schema", Lean.toJson (1 : Nat)), ("module", Lean.toJson moduleName),
     ("request_count", Lean.toJson count),
     ("inputs", portsJson ii.ports ii.label),
     ("registers", Lean.toJson (#[] : Array Lean.Json)),
     ("outputs", portsJson oi.ports oi.label),
     ("requests", Lean.toJson ((List.finRange count).map fun k => ii.label (requestPort k))),
     ("cursor", Lean.toJson ((List.finRange count).map fun k => ii.label (cursorPort k))),
     ("grants", Lean.toJson ((List.finRange count).map fun k => oi.label (grantPort k))),
     ("any_grant", Lean.toJson (oi.label anyPort)),
     ("cursor_encoding", Lean.toJson "one_hot"),
     ("latency_cycles", Lean.toJson (0 : Nat))]
  IO.FS.writeFile (out ++ s!"/rr_{count}.json") (descriptor.pretty ++ "\n")

def main (args : List String) : IO Unit := do
  let mut selections := 0
  for extra in [0, 1, 2, 3, 4, 7] do
    let count := extra + 1
    for mask in [:2^count] do
      for cursor in List.finRange count do
        let request : Fin (extra + 1) → Bool := fun i => (mask / 2^i.val) % 2 == 1
        -- Modulo scan is independent of both the bounded-subtraction logical
        -- selector and the structural priority mux implementation.
        let expected := (List.range count).findSome? fun offset =>
          let index := (cursor.val + offset) % count
          if (mask / 2^index) % 2 == 1 then some index else none
        let observed := (circuit extra).observe (inputValues cursor request) NoRegister.values
        for k in List.finRange count do
          unless observed (grantPort k) == BitVec.ofBool (expected == some k.val) do
            throw (IO.userError s!"Grant mismatch: N={count}, cursor={cursor.val}, mask={mask}, grant={k.val}")
        unless observed anyPort == BitVec.ofBool expected.isSome do
          throw (IO.userError s!"Any-grant mismatch: N={count}, cursor={cursor.val}, mask={mask}")
        selections := selections + 1
  if let some out := args.head? then
    IO.FS.createDirAll out
    for extra in [0, 1, 2, 4, 7] do emit out extra
    IO.println s!"Emitted MLIR and interface descriptors for N=1,2,3,5,8 to {out}."
  IO.println s!"Structural round-robin: {selections} exhaustive selections passed."
