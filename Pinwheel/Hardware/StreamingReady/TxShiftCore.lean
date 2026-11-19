import Pinwheel.Hardware.StreamingReady.Core

/-! The depth-two Ready core with fixed TX slot addresses. The register
interface omits the two TX ring pointers. All other datapath expressions
are instantiated from the existing circuit. -/
namespace Pinwheel.Hardware.StreamingReady.TxShiftCore
open Pinwheel.Hardware

abbrev retained : Core.Register 1 w → Prop
  | .txHead | .txTail => False
  | _ => True

instance (r : Core.Register 1 w) : Decidable (retained r) := by
  cases r <;> (first | exact isTrue trivial | exact isFalse id)

abbrev Register (w : Nat) := {r : Core.Register 1 w // retained r}
abbrev E := Expr Core.Input Register

/-- Interpret an old register leaf in the fixed-slot layout. The sampled
head is slot zero. TX slot writes are replaced separately below. -/
def registerExpr (r : Core.Register 1 w) : E w :=
  if h : retained r then .reg ⟨r, h⟩ else .lit 0

def lift (x : Core.E 1 w) : E w := x.bind Expr.input registerExpr

def put : E 1 := lift Core.pushing
def take : E 1 := lift Core.loadingTX
def clear : E 1 := lift Core.clearedRuntime

def slotUpdate (slot : BitVec 1 → Core.Register 1 w) (input : Core.Input w)
    (resetValue : BitVec w) (index : BitVec 1)
    (valid : ∀ k, retained (slot k)) : E w :=
  let written := fun k =>
    .mux (.band put (.equal (.slice 0 1 (by decide) (.reg ⟨.txCount, trivial⟩)) (.lit k)))
      (.input input) (.reg ⟨slot k, valid k⟩)
  .mux clear (.lit resetValue) (.mux take (written (index + 1)) (written index))

def next : {w : Nat} → Register w → E w
  | _, ⟨.txWord k, _⟩ => slotUpdate .txWord .txData 0 k (fun _ => trivial)
  | _, ⟨.txBits k, _⟩ => slotUpdate .txBits .txBits 32 k (fun _ => trivial)
  | _, r => lift (Core.next r.val)

def circuit : Circuit Core.Input Register Core.Output := ⟨next, fun o => lift (Core.output o)⟩

def encode (s : Values (Core.Register 1)) : Values Register
  | _, ⟨.txWord k, _⟩ => s (.txWord (s .txHead + k))
  | _, ⟨.txBits k, _⟩ => s (.txBits (s .txHead + k))
  | _, r => s r.val

end Pinwheel.Hardware.StreamingReady.TxShiftCore
