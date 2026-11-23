import Lean
import Pinwheel.Hardware.Processor.SystemCircuitEvents

open Lean Elab Command Pinwheel.Hardware Pinwheel.Hardware.Processor

namespace ProcessorSystemCertifiedTests

/-- Downstream artifact use: reset any raw image, then run arbitrary traffic.
The whole final RAM image is transported to the connected model, starting with
exactly the pre-reset words and Q. No zero initialization or loader premise. -/
theorem artifact_final_memory (layout : AddressMap.Layout rw aw) (rom : SystemModel.Rom rw)
    (romFits : rw ≤ 30) (ramFits : aw ≤ 30)
    (rtl : Timed.Component (Values SystemCircuit.Input) (Values (SystemCircuit.Register aw))
      (Values SystemCircuit.Output))
    (artifact : Artifact.Correspondence (SystemCircuit.circuit layout rom romFits ramFits) rtl)
    (resetPins : Values SystemCircuit.Input) (raw : Values (SystemCircuit.Register aw))
    (resetHigh : resetPins SystemCircuit.reset = 1) (traffic : List (Values SystemCircuit.Input)) :
    (SystemCircuit.view (rtl.run (rtl.step resetPins raw) traffic)).ram.memory =
      ((SystemModel.component layout rom).run
        (SystemModel.initial (SystemCircuit.view raw).ram.memory.contents
          (SystemCircuit.view raw).ram.memory.q) (traffic.map SystemCircuit.decode)).ram.memory := by
  rw [SystemCircuit.artifact_run_after_reset layout rom romFits ramFits artifact resetPins raw resetHigh,
    SystemCircuit.spec_run]
  rfl

/-- RAM acknowledgements extracted from actual hardware are sufficient to
reconstruct the entire post-reset run's final memory, including canceled stores. -/
theorem reset_ram_replay (layout : AddressMap.Layout rw aw) (rom : SystemModel.Rom rw)
    (romFits : rw ≤ 30) (ramFits : aw ≤ 30)
    (resetPins : Values SystemCircuit.Input) (raw : Values (SystemCircuit.Register aw))
    (resetHigh : resetPins SystemCircuit.reset = 1) (traffic : List (Values SystemCircuit.Input)) :
    let c := SystemCircuit.circuit layout rom romFits ramFits
    Memory.ByteAdapterEffects.replay (SystemCircuit.view raw).ram.memory.contents
      (c.component.eventTrace (SystemCircuit.ramEvents layout ramFits) (c.step resetPins raw) traffic) =
      some (SystemCircuit.view (c.component.run (c.step resetPins raw) traffic)).ram.memory.contents := by
  have result := SystemCircuit.ram_trace_replay layout rom romFits ramFits
    ((SystemCircuit.circuit layout rom romFits ramFits).step resetPins raw)
    (SystemCircuit.reset_valid layout rom romFits ramFits resetPins raw resetHigh) traffic
  rw [SystemCircuit.reset_view layout rom romFits ramFits resetPins raw resetHigh] at result
  exact result

elab "#audit_system_certified" : command => do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let text := name.toString
    if text.startsWith "Pinwheel.Hardware.Processor.SystemCircuit." ||
        text.startsWith "Pinwheel.Hardware.Processor.SystemModelEncoding." ||
        text.startsWith "Pinwheel.Hardware.Processor.AddressMap.Hit." ||
        text.startsWith "_private.Pinwheel.Hardware.Processor.System" ||
        text.startsWith "ProcessorSystemCertifiedTests." then
      count := count + 1
      let axioms ← collectAxioms name
      let bad := axioms.filter fun a => a != ``propext && a != ``Classical.choice && a != ``Quot.sound
      unless bad.isEmpty do throwError "Unapproved system certificate axiom {name}: {bad}"
  if count < 100 then throwError "Incomplete system certificate audit"
  logInfo m!"Connected system certificate: {count} declarations, standard axioms only."

#audit_system_certified
end ProcessorSystemCertifiedTests
