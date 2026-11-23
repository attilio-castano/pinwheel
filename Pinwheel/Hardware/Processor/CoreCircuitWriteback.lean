import Pinwheel.Hardware.Processor.CoreCircuitDatapath

namespace Pinwheel.Hardware.Processor.CoreCircuit

theorem immediate_destination (state : RV32I.Semantics.State) (value : BitVec 32)
    (context : RV32I.Semantics.Context) (after : RV32I.Semantics.State)
    (h : RV32I.Semantics.step state value = .retired context after) :
    CoreInterface.writeDestination context.instruction = RV32I.DecodeCircuit.instructionRd context.instruction := by
  have hw := RV32I.Semantics.step_word state value
  rw [h] at hw
  change context.word = value at hw
  have hd : RV32I.decode value = some context.instruction := hw ▸ context.decoded
  cases hi : context.instruction <;> try rfl
  unfold RV32I.Semantics.step at h
  split at h
  · cases h
  · rename_i ins hins
    have he : ins = context.instruction := Option.some.inj (hins.symm.trans hd)
    simp only [he,hi,RV32I.Semantics.executeContext] at h
    cases h

end Pinwheel.Hardware.Processor.CoreCircuit
