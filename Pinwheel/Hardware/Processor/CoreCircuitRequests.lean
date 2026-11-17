import Pinwheel.Hardware.Processor.CoreCircuitDatapath

namespace Pinwheel.Hardware.Processor.CoreCircuit

set_option backward.isDefEq.respectTransparency false

/-- Fetch/data offers and response readiness depend on reset and held state.
Service and response inputs cannot introduce a combinational feedback path. -/
theorem request_outputs (i j : Values CoreInterface.Input) (s : Values Register)
    (reset_eq : i CoreInterface.reset = j CoreInterface.reset) (o : CoreInterface.Output b)
    (request : (CoreInterface.outputs.position o).val < 11) :
    circuit.observe i s o = circuit.observe j s o := by
  match o with
  | .at ⟨0,_⟩ | .at ⟨1,_⟩ | .at ⟨2,_⟩ | .at ⟨3,_⟩ | .at ⟨4,_⟩ | .at ⟨5,_⟩ |
    .at ⟨6,_⟩ | .at ⟨7,_⟩ | .at ⟨8,_⟩ | .at ⟨9,_⟩ | .at ⟨10,_⟩ =>
      simp only [Circuit.observe,circuit,active,both,inPhase,pcAligned,gated,dataOffer,dataWaiting,
        isStore,Expr.eval,execution_eval,reset_eq] <;> rfl
  | .at ⟨k+11,_⟩ => exact False.elim (by change k+11 < 11 at request; omega)

end Pinwheel.Hardware.Processor.CoreCircuit
