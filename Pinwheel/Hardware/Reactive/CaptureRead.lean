import Pinwheel.Hardware.Reactive.FetchChoice

namespace Pinwheel.Hardware.Reactive

/-- Read-after-capture forwarding. The old sample read and the capture-address
comparison run independently; the newly captured bit is selected at the end. -/
def captureRead (bits : E 6) (slots : Slots) (address : E 4) : E 1 :=
  .mux (.band (.slice 0 1 (by decide) bits)
      (.equal (.slice 2 4 (by decide) bits) address))
    (inputBit (.slice 1 1 (by decide) bits))
    (Execution.readTree 4 (fun k => slots k.toFin) address)

/-- The identity holds for arbitrary inputs and register bits, including
disabled captures, arbitrary old samples, and same-edge read-after-write. -/
theorem captureRead_correct (bits : E 6) (slots : Slots) (address : E 4)
    (i : Values Input) (s : Values Register) :
    (captureRead bits slots address).eval i s =
      (Execution.readTree 4 (fun k => captureSlots bits slots k.toFin) address).eval i s := by
  simp only [captureRead, Execution.readTree_correct, captureSlots, Expr.eval]
  rfl
  done

/-- An alternative expression for the existing branch decision. This is not
selected by the production scheduler or by the retained SRAM chip emitter. -/
def Fetch.forwardedBranchExpr : E 1 :=
  captureRead (current .terminal) oldSlots (current .sample)

theorem Fetch.forwardedBranchExpr_eq (i : Values Input) (s : Values Register) :
    forwardedBranchExpr.eval i s = branchExpr.eval i s := by
  exact captureRead_correct (current .terminal) oldSlots (current .sample) i s
  done

end Pinwheel.Hardware.Reactive
