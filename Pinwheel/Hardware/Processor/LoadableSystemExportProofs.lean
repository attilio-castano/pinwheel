import Pinwheel.Hardware.Processor.LoadableSystemExport

namespace Pinwheel.Hardware.Processor.LoadableSystemExport

set_option backward.isDefEq.respectTransparency false

def systemValues (i : Values (BusInput aw)) : Values SystemInterface.Input :=
  LoadableSystem.systemPins (fun p => i (.left p))

def projectedValues (i : Values (BusInput aw)) : Values SystemExport.BusInput :=
  SystemExport.busValues (systemValues i) (fun p => i (.right (.left p)))
    (fun p => i (.right (.right (.left (.left p)))))
    (fun p => i (.right (.right (.right p))))

theorem network_agrees (i : Values (BusInput aw)) (s : Values SystemInterface.Fetch) :
    SystemExport.Agrees busNetwork SystemExport.busNetwork i s (projectedValues i) s where
  pins := by
    intro b p
    match p with
    | .at ⟨0,_⟩ =>
      change (WordOps.wordOr _ _).eval i s = _
      exact WordOps.wordOr_eval _ _ i s
    | .at ⟨k+1,_⟩ => rfl
  requests _ _ := rfl
  ram _ := rfl
  mmio _ := rfl
  fetch _ := rfl

theorem bus_fetch_eq (layout : AddressMap.Layout rw aw) (rom : BitVec rw → BitVec 32)
    (romFits : rw ≤ 30) (ramFits : aw ≤ 30) (i : Values (BusInput aw))
    (s : Values SystemInterface.Fetch) (p : SystemInterface.Fetch b) :
    (busCircuit layout rom romFits ramFits).step i s p =
      (SystemExport.busCircuit layout rom romFits ramFits).step (projectedValues i) s p :=
  SystemExport.fetch_next_congr (network_agrees i s) layout rom romFits p

theorem bus_core_eq (layout : AddressMap.Layout rw aw) (rom : BitVec rw → BitVec 32)
    (romFits : rw ≤ 30) (ramFits : aw ≤ 30) (i : Values (BusInput aw))
    (s : Values SystemInterface.Fetch) (p : CoreInterface.Input b) :
    (busCircuit layout rom romFits ramFits).observe i s (.left p) =
      (SystemExport.busCircuit layout rom romFits ramFits).observe (projectedValues i) s (.left p) :=
  SystemExport.core_input_congr (network_agrees i s) layout rom romFits p

theorem bus_mmio_eq (layout : AddressMap.Layout rw aw) (rom : BitVec rw → BitVec 32)
    (romFits : rw ≤ 30) (ramFits : aw ≤ 30) (i : Values (BusInput aw))
    (s : Values SystemInterface.Fetch) (p : MmioInterface.Input b) :
    (busCircuit layout rom romFits ramFits).observe i s (.right (.right (.left p))) =
      (SystemExport.busCircuit layout rom romFits ramFits).observe (projectedValues i) s (.right (.right p)) :=
  SystemExport.mmio_input_congr (network_agrees i s) layout p

theorem bus_loader_eq (layout : AddressMap.Layout rw aw) (rom : BitVec rw → BitVec 32)
    (romFits : rw ≤ 30) (ramFits : aw ≤ 30) (i : Values (BusInput aw))
    (s : Values SystemInterface.Fetch) (p : Memory.ByteAdapterLoader.Input aw b) :
    (busCircuit layout rom romFits ramFits).observe i s (.right (.left p)) =
      LoadableSystem.loaderPins (fun q => i (.left q))
        (fun q => (SystemExport.busCircuit layout rom romFits ramFits).observe
          (projectedValues i) s (.right (.left q))) p := by
  match b,p with
  | _, .left (.at ⟨0,_⟩) => rfl
  | _, .left (.at ⟨k+1,h⟩) =>
    exact SystemExport.ram_input_congr (network_agrees i s) layout ramFits (.at ⟨k+1,h⟩)
  | _, .right _ => rfl

/-- The loader recomputes effective reset internally; overriding only its
external-reset pin therefore gives exactly the canonical adapter input. -/
theorem loader_adapter_pins (i : Values (LoadableSystem.Input aw))
    (rp : Values (Memory.ByteAdapterInterface.Input aw))
    (reset_eq : rp Memory.ByteAdapterInterface.reset = i LoadableSystem.reset ||| i LoadableSystem.mode) :
    @Eq (Values (Memory.ByteAdapterInterface.Input aw))
      (Memory.ByteAdapterLoader.pins (LoadableSystem.loaderPins i rp)) rp := by
  funext b p
  match p with
  | .at ⟨0,_⟩ =>
    change (WordOps.wordOr _ _).eval _ _ = _
    rw [WordOps.wordOr_eval]
    exact reset_eq.symm
  | .at ⟨1,_⟩ | .at ⟨2,_⟩ | .at ⟨3,_⟩ | .at ⟨4,_⟩ | .at ⟨5,_⟩ |
    .at ⟨6,_⟩ | .at ⟨7,_⟩ | .at ⟨8,_⟩ => rfl
  | .at ⟨k+9,h⟩ => change k+9 < 9 at h; omega

variable (layout : AddressMap.Layout rw aw) (rom : BitVec rw → BitVec 32)
  (romFits : rw ≤ 30) (ramFits : aw ≤ 30)

def actualValues (i : Values (LoadableSystem.Input aw)) (s : Values (LoadableSystem.Register aw)) : Values (BusInput aw) :=
  let stage := SystemExport.stages layout rom romFits ramFits (LoadableSystem.systemPins i) s
  Stream.Joint.values i (Stream.Joint.values
    (CoreCircuit.circuit.observe stage.coreInput.values (fun p => s (SystemCircuit.core p)))
    (Stream.Joint.values
      ((Memory.ByteAdapterLoader.circuit aw).observe (LoadableSystem.loaderPins i stage.ramInput.values)
        (fun p => s (SystemCircuit.ram p))) stage.mmioOutput.values))

theorem stage_ram_reset (i : Values (LoadableSystem.Input aw)) (s : Values (LoadableSystem.Register aw)) :
    (SystemExport.stages layout rom romFits ramFits (LoadableSystem.systemPins i) s).ramInput.values
      Memory.ByteAdapterInterface.reset = i LoadableSystem.reset ||| i LoadableSystem.mode := by
  rw [SystemExport.stage_ram_input]
  rfl

theorem projected_actual (i : Values (LoadableSystem.Input aw)) (s : Values (LoadableSystem.Register aw)) :
    @Eq (Values SystemExport.BusInput) (projectedValues (actualValues layout rom romFits ramFits i s))
      (SystemExport.actualValues layout rom romFits ramFits (LoadableSystem.systemPins i) s) := by
  funext b p
  cases p with
  | left p => rfl
  | right p => cases p with
    | left p => rfl
    | right p => cases p with
      | left p =>
        change (Memory.ByteAdapterLoader.circuit aw).observe _ _ (.left p) = _
        simp only [Circuit.observe,Memory.ByteAdapterLoader.circuit,Expr.eval_bind,Memory.ByteAdapterLoader.adapter_eval]
        rw [loader_adapter_pins i _ (stage_ram_reset layout rom romFits ramFits i s)]
        rfl
      | right p => rfl

/-- Every functional bus output agrees with the original staged system and
the loader's explicit reset/ownership pins, using actual leaf feedback. -/
theorem actual_bus_output (i : Values (LoadableSystem.Input aw)) (s : Values (LoadableSystem.Register aw))
    (p : BusOutput aw b) :
    (busCircuit layout rom romFits ramFits).observe (actualValues layout rom romFits ramFits i s)
      (SystemExport.fetchState s) p =
      (let stage := SystemExport.stages layout rom romFits ramFits (LoadableSystem.systemPins i) s
       match p with
       | .left p => stage.coreInput.values p
       | .right (.left p) => LoadableSystem.loaderPins i stage.ramInput.values p
       | .right (.right (.left p)) => stage.mmioInput.values p
       | .right (.right (.right p)) =>
           (LoadableSystem.outputSnapshot layout rom romFits ramFits i s).values (.right p)) := by
  cases p with
  | left p =>
    rw [bus_core_eq,projected_actual,SystemExport.actual_bus_output]
  | right p => cases p with
    | left p =>
      rw [bus_loader_eq,projected_actual]
      simp only [SystemExport.actual_bus_output]
      rfl
    | right p => cases p with
      | left p => rw [bus_mmio_eq,projected_actual,SystemExport.actual_bus_output]
      | right p =>
        match b,p with
        | _, .at ⟨0,_⟩ | _, .at ⟨1,_⟩ =>
          simp only [Circuit.observe,busCircuit,status,Expr.eval,actualValues,Stream.Joint.values,
            LoadableSystem.outputSnapshot,SystemExport.snapshot_values]
        | _, .at ⟨k+2,h⟩ => change k+2 < 2 at h; omega

theorem actual_bus_step (i : Values (LoadableSystem.Input aw)) (s : Values (LoadableSystem.Register aw))
    (p : SystemInterface.Fetch b) :
    (busCircuit layout rom romFits ramFits).step (actualValues layout rom romFits ramFits i s)
      (SystemExport.fetchState s) p =
      (SystemExport.stages layout rom romFits ramFits (LoadableSystem.systemPins i) s).fetchNext.values p := by
  rw [bus_fetch_eq,projected_actual,SystemExport.actual_bus_step]

end Pinwheel.Hardware.Processor.LoadableSystemExport
