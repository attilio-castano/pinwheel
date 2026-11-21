import Lean
import Pinwheel.Hardware.Arbitration.OneHotSelect
import Pinwheel.Hardware.Emit

open Lean Elab Command Pinwheel.Hardware Pinwheel.Hardware.Arbitration

elab "#audit_one_hot_select" : command => do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "Pinwheel.Hardware.Arbitration.OneHotSelect." then
      count := count + 1
      let axioms ← collectAxioms name
      let bad := axioms.filter fun a => a != ``propext && a != ``Classical.choice && a != ``Quot.sound
      unless bad.isEmpty do throwError "Unapproved axioms in {name}: {bad}"
  if count == 0 then throwError "Empty shared selector audit"
  logInfo m!"Shared selector audit: {count} declarations, standard axioms only."

#audit_one_hot_select

namespace OneHotSelectTests

inductive Input (n w : Nat) : Nat → Type where
  | request : Fin (n+1) → Input n w 1
  | cursor : Fin (n+1) → Input n w 1
  | value : Fin (n+1) → Input n w w
  | fallback : Input n w w

inductive Output (n w : Nat) : Nat → Type where
  | grant : Fin (n+1) → Output n w 1
  | any : Output n w 1
  | payload : Output n w w
  | nextCursor : Fin (n+1) → Output n w 1

def inputs (n w : Nat) : Array (Sigma (Input n w)) :=
  (Array.ofFn fun k => ⟨1, .request k⟩) ++ (Array.ofFn fun k => ⟨1, .cursor k⟩) ++
  (Array.ofFn fun k => ⟨w, .value k⟩) ++ #[⟨w, .fallback⟩]

def outputs (n w : Nat) : Array (Sigma (Output n w)) :=
  (Array.ofFn fun k => ⟨1, .grant k⟩) ++ #[⟨1, .any⟩, ⟨w, .payload⟩] ++
  (Array.ofFn fun k => ⟨1, .nextCursor k⟩)

def inputLabel : Input n w b → String
  | .request k => s!"request_{k.val}"
  | .cursor k => s!"cursor_{k.val}"
  | .value k => s!"value_{k.val}"
  | .fallback => "fallback"

def outputLabel : Output n w b → String
  | .grant k => s!"grant_{k.val}"
  | .any => "any_grant"
  | .payload => "payload"
  | .nextCursor k => s!"next_{k.val}"

def choose (shared : Bool) (value : Fin (n+1) → Expr (Input n w) NoRegister b)
    (fallback : Expr (Input n w) NoRegister b) : Expr (Input n w) NoRegister b :=
  if shared then OneHotSelect.selection (fun k => .input (.cursor k)) (fun k => .input (.request k)) value fallback
  else RoundRobinMasked.selection (fun k => .input (.cursor k)) (fun k => .input (.request k)) value fallback

def circuit (shared : Bool) (n w : Nat) : Circuit (Input n w) NoRegister (Output n w) where
  next := fun r => nomatch r
  output := fun {b} p => match b, p with
    | _, .grant k => if shared then OneHotSelect.winner (fun j => .input (.cursor j)) (fun j => .input (.request j)) k
        else choose false (fun j => .lit (BitVec.ofBool (j == k))) (.lit 0)
    | _, .any => if shared then OneHotSelect.anyWinner (fun j => .input (.cursor j)) (fun j => .input (.request j))
        else choose false (fun _ => .lit 1) (.lit 0)
    | _, .payload => choose shared (fun k => .input (.value k)) (.input .fallback)
    | _, .nextCursor k => choose shared (fun j => .lit (BitVec.ofBool (k == RoundRobin.next j))) (.input (.cursor k))

def values (cursor : Fin (n+1)) (request : Fin (n+1) → Bool) (value : Fin (n+1) → BitVec w)
    (fallback : BitVec w) : Values (Input n w)
  | _, .request k => BitVec.ofBool (request k)
  | _, .cursor k => BitVec.ofBool (k == cursor)
  | _, .value k => value k
  | _, .fallback => fallback

private def portsJson (ports : Array (Sigma P)) (label : {b : Nat} → P b → String) : Json :=
  toJson (ports.map fun ⟨b, p⟩ => Json.mkObj [("name", toJson (label p)), ("width", toJson b)])

def emit (out : String) (shared : Bool) (n w : Nat) : IO Unit := do
  let mode := if shared then "shared" else "masked"
  let name := s!"select_{mode}_{n+1}_w{w}"
  let text ← IO.ofExcept (Emit.moduleText name (circuit shared n w) (inputs n w) #[] (outputs n w)
    inputLabel (fun r => nomatch r) outputLabel)
  IO.FS.writeFile (out ++ s!"/{name}.mlir") text
  IO.FS.writeFile (out ++ s!"/{name}.json") ((Json.mkObj
    [("schema", toJson (1 : Nat)), ("module", toJson name), ("request_count", toJson (n+1)),
     ("width", toJson w), ("mode", toJson mode), ("inputs", portsJson (inputs n w) inputLabel),
     ("outputs", portsJson (outputs n w) outputLabel), ("registers", toJson (#[] : Array Json)),
     ("requests", toJson (Array.ofFn (fun k : Fin (n+1) => inputLabel (Input.request (w := w) k)))),
     ("cursor", toJson (Array.ofFn (fun k : Fin (n+1) => inputLabel (Input.cursor (w := w) k)))),
     ("values", toJson (Array.ofFn (fun k : Fin (n+1) => inputLabel (Input.value (w := w) k)))),
     ("grants", toJson (Array.ofFn (fun k : Fin (n+1) => outputLabel (Output.grant (w := w) k)))),
     ("next_cursor", toJson (Array.ofFn (fun k : Fin (n+1) => outputLabel (Output.nextCursor (w := w) k)))),
     ("fallback", toJson "fallback"), ("any_grant", toJson "any_grant"), ("payload", toJson "payload")]).pretty ++ "\n")

def exercise (n w : Nat) : IO Nat := do
  let mut cases := 0
  for mask in [:2^(n+1)] do
    for cursor in List.finRange (n+1) do
      let request : Fin (n+1) → Bool := fun k => (mask / 2^k.val) % 2 == 1
      let expected := (List.range (n+1)).findSome? fun offset =>
        let index := (cursor.val + offset) % (n+1)
        if (mask / 2^index) % 2 == 1 then some index else none
      let payload : Nat → BitVec w := fun k => BitVec.ofNat w ((mask+17)*(k+3)+cursor.val*5)
      let fallback := BitVec.ofNat w (131071-mask*3+cursor.val)
      let input : Values (Input n w) := values cursor request (fun k => payload k.val) fallback
      for shared in [false, true] do
        let observed : Values (Output n w) := (circuit shared n w).observe input NoRegister.values
        unless observed .payload == (expected.map payload).getD fallback &&
            observed .any == BitVec.ofBool expected.isSome do
          throw (IO.userError s!"Shared selector payload/any mismatch n={n+1},w={w},mask={mask},cursor={cursor.val}")
        let next := (expected.map fun k => (k+1) % (n+1)).getD cursor.val
        for k in List.finRange (n+1) do
          unless observed (.grant k) == BitVec.ofBool (expected == some k.val) &&
              observed (.nextCursor k) == BitVec.ofBool (k.val == next) do
            throw (IO.userError s!"Shared selector grant/cursor mismatch n={n+1},w={w},mask={mask},cursor={cursor.val}")
      cases := cases + 1
  pure cases

end OneHotSelectTests

def main (args : List String) : IO Unit := do
  let mut cases := 0
  for n in [0, 1, 2, 4, 7] do
    for w in [1, 8, 17] do
      cases := cases + (← OneHotSelectTests.exercise n w)
      if let some out := args.head? then
        IO.FS.createDirAll out
        for shared in [false, true] do OneHotSelectTests.emit out shared n w
  IO.println s!"Shared selector: {cases} exhaustive cursor/request cases with payload/fallback and next-cursor checks in both forms."
