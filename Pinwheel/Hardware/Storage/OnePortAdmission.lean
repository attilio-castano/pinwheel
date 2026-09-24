import Pinwheel.Hardware.Storage.OnePortBackend
import Pinwheel.Hardware.Storage.AdmissionNetlist

/-! An emitted admission gate for the existing one-port experimental contract.
This makes unsupported uploads observable; it does not change compiler timing. -/
namespace Pinwheel.Hardware.Storage.Backend.OnePort
open Loader

def admissionGate : Expr Machine.Input Register 1 :=
  .inv (.band (.equal (.slice 0 3 (by decide) (.input .data)) (.lit 2))
    (.band (.equal (.slice 41 2 (by decide) (.input .data)) (.lit 2))
      (.zero (.slice 9 8 (by decide) (.input .data)))))

theorem admissionGate_correct (i : Machine.Inputs) (s : Values Register) :
    admissionGate.eval i.values s = BitVec.ofBool (SinglePort.Ready i.data) := by
  simp only [admissionGate, SinglePort.Ready, Execution.unpack, Expr.eval, Machine.Inputs.values]
  simp [BitVec.ofBool_and_ofBool, BitVec.not_ofBool, Bool.and_assoc]
  rfl

def admittedNetlist := Admission.netlist admissionGate netlist

theorem admitted_component : (admittedNetlist.componentOf Machine.Inputs.values) =
    component.precompose (Admission.admit SinglePort.Ready) :=
  Admission.component_correct admissionGate SinglePort.Ready netlist admissionGate_correct

def admittedRefinement : Timed.Refinement (admittedNetlist.componentOf Machine.Inputs.values)
    (referenceComponent.precompose (Admission.admit SinglePort.Ready)) := by
  simpa only [admitted_component] using admitted

end Pinwheel.Hardware.Storage.Backend.OnePort
