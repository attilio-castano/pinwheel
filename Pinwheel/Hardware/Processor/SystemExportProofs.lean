import Pinwheel.Hardware.Processor.SystemExport
import Pinwheel.Hardware.RunRefinement

namespace Pinwheel.Hardware.Processor.SystemExport

open SystemWiring
set_option backward.isDefEq.respectTransparency false

/-- Bus semantics depends on core request endpoints 0..10, never on retirement
or fault outputs that can depend on the response supplied by this same bus. -/
structure Agrees (a : Network I R) (b : Network J S)
    (ai : Values I) (ar : Values R) (bi : Values J) (br : Values S) : Prop where
  pins : ∀ {w} (p : SystemInterface.Input w), (a.pins p).eval ai ar = (b.pins p).eval bi br
  requests : ∀ {w} (p : CoreInterface.Output w), (CoreInterface.outputs.position p).val < 11 →
    (a.coreOutputs p).eval ai ar = (b.coreOutputs p).eval bi br
  ram : ∀ {w} (p : Memory.ByteAdapterInterface.Output w), (a.ramOutputs p).eval ai ar = (b.ramOutputs p).eval bi br
  mmio : ∀ {w} (p : MmioInterface.Output w), (a.mmioOutputs p).eval ai ar = (b.mmioOutputs p).eval bi br
  fetch : ∀ {w} (p : SystemInterface.Fetch w), (a.fetchValues p).eval ai ar = (b.fetchValues p).eval bi br

variable {a : Network I R} {b : Network J S} {ai : Values I} {ar : Values R} {bi : Values J} {br : Values S}
  (h : Agrees a b ai ar bi br)
  (layout : AddressMap.Layout rw aw) (rom : BitVec rw → BitVec 32)
  (romFits : rw ≤ 30) (ramFits : aw ≤ 30)

include h

theorem route_congr : (route a layout).eval ai ar = (route b layout).eval bi br := by
  simp only [route, AddressDecode.runtime_eval, Expr.eval]
  simp (disch := decide) only [h.requests]

theorem region_congr (code : BitVec 3) : (region a layout code).eval ai ar = (region b layout code).eval bi br := by
  simp only [region, Expr.eval, route_congr h layout]

theorem peripheral_congr : (peripheral a layout).eval ai ar = (peripheral b layout).eval bi br := by
  simp only [peripheral, either, WordOps.wordOr_eval, region_congr h layout]

theorem ram_input_congr (p : Memory.ByteAdapterInterface.Input aw w) :
    (SystemWiring.ramInput a layout ramFits p).eval ai ar = (SystemWiring.ramInput b layout ramFits p).eval bi br := by
  match p with
  | .at ⟨0,_⟩ | .at ⟨1,_⟩ | .at ⟨2,_⟩ | .at ⟨3,_⟩ | .at ⟨4,_⟩ |
    .at ⟨5,_⟩ | .at ⟨6,_⟩ | .at ⟨7,_⟩ | .at ⟨8,_⟩ =>
    simp only [SystemWiring.ramInput, both, localAddress, Expr.eval, region_congr h layout, h.pins] <;>
    (dsimp; try simp (disch := decide) only [h.requests])
  | .at ⟨k+9,h⟩ => change k+9 < 9 at h; omega

theorem mmio_input_congr (p : MmioInterface.Input w) :
    (SystemWiring.mmioInput a layout p).eval ai ar = (SystemWiring.mmioInput b layout p).eval bi br := by
  match p with
  | .at ⟨0,_⟩ | .at ⟨1,_⟩ | .at ⟨2,_⟩ | .at ⟨3,_⟩ | .at ⟨4,_⟩ | .at ⟨5,_⟩ |
    .at ⟨6,_⟩ | .at ⟨7,_⟩ | .at ⟨8,_⟩ | .at ⟨9,_⟩ | .at ⟨10,_⟩ =>
    simp only [SystemWiring.mmioInput, both, peripheralBase, Expr.eval, region_congr h layout,
      peripheral_congr h layout, h.pins] <;>
    (dsimp; try simp (disch := decide) only [h.requests])
  | .at ⟨k+11,h⟩ => change k+11 < 11 at h; omega

theorem core_input_congr (p : CoreInterface.Input w) :
    (SystemWiring.coreInput a layout rom romFits p).eval ai ar =
      (SystemWiring.coreInput b layout rom romFits p).eval bi br := by
  match p with
  | .at ⟨0,_⟩ | .at ⟨1,_⟩ | .at ⟨2,_⟩ | .at ⟨3,_⟩ | .at ⟨4,_⟩ | .at ⟨5,_⟩ |
    .at ⟨6,_⟩ | .at ⟨7,_⟩ | .at ⟨8,_⟩ | .at ⟨9,_⟩ | .at ⟨10,_⟩ | .at ⟨11,_⟩ =>
    simp only [SystemWiring.coreInput, both, serviceFault, responseFault, romLoad, romData,
      Memory.ByteAdapterCircuit.loadExpr, Memory.ByteAdapterCircuit.selectedByte, Memory.ByteAdapterCircuit.select4,
      Expr.eval, Execution.readTree_correct, h.pins, h.fetch, h.ram, h.mmio,
      region_congr h layout, peripheral_congr h layout] <;>
    (dsimp; try simp (disch := decide) only [h.requests]) <;>
    (congr 1; exact h.requests CoreInterface.dataValid (by decide))
  | .at ⟨k+12,h⟩ => change k+12 < 12 at h; omega

theorem fetch_route_congr : (fetchRoute a layout).eval ai ar = (fetchRoute b layout).eval bi br := by
  simp only [fetchRoute, AddressDecode.result_eval]
  exact congrArg (fun address => AddressDecode.routeCode
    (AddressMap.route layout ⟨.fetch, .word, address⟩)) (h.requests CoreInterface.fetchAddress (by decide))

theorem fetch_next_congr (p : SystemInterface.Fetch w) :
    (SystemWiring.fetchNext a layout rom romFits p).eval ai ar =
      (SystemWiring.fetchNext b layout rom romFits p).eval bi br := by
  match p with
  | .at ⟨0,_⟩ | .at ⟨1,_⟩ | .at ⟨2,_⟩ =>
    simp only [SystemWiring.fetchNext, both, fetch_route_congr h layout, Expr.eval,
      Execution.readTree_correct, h.pins, h.fetch] <;>
    (dsimp; try simp (disch := decide) only [h.requests])
  | .at ⟨k+3,h⟩ => change k+3 < 3 at h; omega

omit h

def firstValues (i : Values SystemInterface.Input) (s : Values (SystemCircuit.Register aw)) : Values BusInput :=
  busValues i (requestValues i (fun r => s (SystemCircuit.core r))).values (fun _ => 0) (fun _ => 0)
def fetchState (s : Values (SystemCircuit.Register aw)) : Values SystemInterface.Fetch :=
  fun r => s (SystemCircuit.fetch r)

theorem request_pin_eval (i : Values SystemInterface.Input) (s : Values (SystemCircuit.Register aw))
    (p : CoreInterface.Input w) : (SystemCircuit.requestInput p).eval i s = requestPins i p := by
  match p with | .at ⟨0,_⟩ | .at ⟨k+1,_⟩ => rfl

theorem request_agrees (i : Values SystemInterface.Input) (s : Values (SystemCircuit.Register aw)) :
    Agrees busNetwork SystemCircuit.requestNetwork (firstValues i s) (fetchState s) i s where
  pins _ := rfl
  requests := by
    intro w p hp
    simp only [busNetwork, SystemCircuit.requestNetwork, firstValues, busValues, Expr.eval,
      Stream.Joint.values, requestValues, snapshot_values, if_pos hp, SystemCircuit.offer,
      Expr.eval_bind, request_pin_eval, Circuit.observe]
  ram _ := rfl
  mmio _ := rfl
  fetch _ := rfl

theorem stage_ram_input (i : Values SystemInterface.Input) (s : Values (SystemCircuit.Register aw))
    (p : Memory.ByteAdapterInterface.Input aw w) :
    (stages layout rom romFits ramFits i s).ramInput.values p = (SystemCircuit.ramInput layout ramFits p).eval i s := by
  simp only [stages, snapshot_values]
  exact ram_input_congr (request_agrees i s) layout ramFits p

theorem stage_mmio_input (i : Values SystemInterface.Input) (s : Values (SystemCircuit.Register aw))
    (p : MmioInterface.Input w) :
    (stages layout rom romFits ramFits i s).mmioInput.values p = (SystemCircuit.mmioInput layout p).eval i s := by
  simp only [stages, snapshot_values]
  exact mmio_input_congr (request_agrees i s) layout p

theorem stage_mmio_output (i : Values SystemInterface.Input) (s : Values (SystemCircuit.Register aw))
    (p : MmioInterface.Output w) :
    (stages layout rom romFits ramFits i s).mmioOutput.values p = (SystemCircuit.mmioOutput layout p).eval i s := by
  change (snapshot _ (MmioCircuit.circuit.observe
    (stages layout rom romFits ramFits i s).mmioInput.values (fun r => s (SystemCircuit.mmio r)))).values p = _
  simp only [snapshot_values, SystemCircuit.mmioOutput, Expr.eval_bind, Circuit.observe]
  have hi := funext fun w => funext fun p => stage_mmio_input layout rom romFits ramFits i s (w := w) p
  rw [hi]
  rfl

def connectedValues (layout : AddressMap.Layout rw aw) (rom : BitVec rw → BitVec 32)
    (romFits : rw ≤ 30) (ramFits : aw ≤ 30)
    (i : Values SystemInterface.Input) (s : Values (SystemCircuit.Register aw)) : Values BusInput :=
  let st := stages layout rom romFits ramFits i s
  busValues i (requestValues i (fun r => s (SystemCircuit.core r))).values
    (snapshot Memory.ByteAdapterInterface.outputs ((Memory.ByteAdapterCircuit.circuit aw).observe
      st.ramInput.values (fun r => s (SystemCircuit.ram r)))).values st.mmioOutput.values

theorem connected_agrees (i : Values SystemInterface.Input) (s : Values (SystemCircuit.Register aw)) :
    Agrees busNetwork (SystemCircuit.network layout ramFits)
      (connectedValues layout rom romFits ramFits i s) (fetchState s) i s where
  pins _ := rfl
  requests p hp := (request_agrees i s).requests p hp
  ram := by
    intro w p
    change (snapshot _ ((Memory.ByteAdapterCircuit.circuit aw).observe
      (stages layout rom romFits ramFits i s).ramInput.values (fun r => s (SystemCircuit.ram r)))).values p =
        (SystemCircuit.ramOutput layout ramFits p).eval i s
    simp only [snapshot_values, SystemCircuit.ramOutput, Expr.eval_bind, Circuit.observe]
    have hi := funext fun w => funext fun p => stage_ram_input layout rom romFits ramFits i s (w := w) p
    rw [hi]
    rfl
  mmio p := stage_mmio_output layout rom romFits ramFits i s p
  fetch _ := rfl

theorem stage_core_input (i : Values SystemInterface.Input) (s : Values (SystemCircuit.Register aw))
    (p : CoreInterface.Input w) :
    (stages layout rom romFits ramFits i s).coreInput.values p =
      (SystemCircuit.coreInput layout rom romFits ramFits p).eval i s := by
  simp only [stages, snapshot_values]
  exact core_input_congr (connected_agrees layout rom romFits ramFits i s) layout rom romFits p

theorem stage_fetch_next (i : Values SystemInterface.Input) (s : Values (SystemCircuit.Register aw))
    (p : SystemInterface.Fetch w) :
    (stages layout rom romFits ramFits i s).fetchNext.values p =
      (SystemCircuit.fetchNext layout rom romFits p).eval i s := by
  simp only [stages, snapshot_values]
  exact fetch_next_congr (request_agrees i s) layout rom romFits p

/-- Exact raw-state equality; staging introduces no logical invariant premise. -/
theorem staged_step (i : Values SystemInterface.Input) (s : Values (SystemCircuit.Register aw))
    (r : SystemCircuit.Register aw w) :
    (staged layout rom romFits ramFits).step i s r =
      (SystemCircuit.circuit layout rom romFits ramFits).step i s r := by
  cases r with
  | left r =>
    simp only [staged, nextSnapshot, snapshot_values, Circuit.step, SystemCircuit.circuit, Expr.eval_bind]
    have hi := funext fun w => funext fun p => stage_core_input layout rom romFits ramFits i s (w := w) p
    rw [hi]
    rfl
  | right r => cases r with
    | left r =>
      simp only [staged, nextSnapshot, snapshot_values, Circuit.step, SystemCircuit.circuit, Expr.eval_bind]
      have hi := funext fun w => funext fun p => stage_ram_input layout rom romFits ramFits i s (w := w) p
      rw [hi]
      rfl
    | right r => cases r with
      | left r =>
        simp only [staged, nextSnapshot, snapshot_values, Circuit.step, SystemCircuit.circuit, Expr.eval_bind]
        have hi := funext fun w => funext fun p => stage_mmio_input layout rom romFits ramFits i s (w := w) p
        rw [hi]
        rfl
      | right r =>
        simp only [staged, nextSnapshot, snapshot_values, Circuit.step, SystemCircuit.circuit]
        exact stage_fetch_next layout rom romFits ramFits i s r

theorem staged_output (i : Values SystemInterface.Input) (s : Values (SystemCircuit.Register aw))
    (o : SystemCircuit.Output w) :
    (staged layout rom romFits ramFits).observe i s o =
      (SystemCircuit.circuit layout rom romFits ramFits).observe i s o := by
  cases o with
  | left o =>
    simp only [staged, outputSnapshot, snapshot_values, Stream.Joint.values, Circuit.observe,
      SystemCircuit.circuit, Expr.eval_bind]
    have hi := funext fun w => funext fun p => stage_core_input layout rom romFits ramFits i s (w := w) p
    rw [hi]
    rfl
  | right o =>
    simp only [staged, outputSnapshot, snapshot_values, Stream.Joint.values, Circuit.observe, SystemCircuit.circuit]
    exact stage_mmio_output layout rom romFits ramFits i s o

theorem stage_core_reset (i : Values SystemInterface.Input) (s : Values (SystemCircuit.Register aw)) :
    (stages layout rom romFits ramFits i s).coreInput.values CoreInterface.reset = i SystemInterface.reset := by
  simp only [stages, snapshot_values, CoreInterface.reset, SystemWiring.coreInput,
    busNetwork, Expr.eval, busValues, Stream.Joint.values]

/-- Values on the actual module interconnections, including the core's full
output port. Only its request subset is consumed by the bus expressions. -/
def actualValues (layout : AddressMap.Layout rw aw) (rom : BitVec rw → BitVec 32)
    (romFits : rw ≤ 30) (ramFits : aw ≤ 30)
    (i : Values SystemInterface.Input) (s : Values (SystemCircuit.Register aw)) : Values BusInput :=
  let st := stages layout rom romFits ramFits i s
  busValues i (CoreCircuit.circuit.observe st.coreInput.values (fun r => s (SystemCircuit.core r)))
    ((Memory.ByteAdapterCircuit.circuit aw).observe st.ramInput.values (fun r => s (SystemCircuit.ram r)))
    st.mmioOutput.values

theorem actual_agrees (i : Values SystemInterface.Input) (s : Values (SystemCircuit.Register aw)) :
    Agrees busNetwork (SystemCircuit.network layout ramFits)
      (actualValues layout rom romFits ramFits i s) (fetchState s) i s where
  pins _ := rfl
  requests := by
    intro w p hp
    change CoreCircuit.circuit.observe (stages layout rom romFits ramFits i s).coreInput.values
      (fun r => s (SystemCircuit.core r)) p = (SystemCircuit.offer p).eval i s
    rw [CoreCircuit.request_outputs _ (requestPins i) _ (stage_core_reset layout rom romFits ramFits i s) p hp]
    have h := (request_agrees i s).requests p hp
    simpa only [busNetwork, firstValues, busValues, Expr.eval, Stream.Joint.values,
      requestValues, snapshot_values, if_pos hp, SystemCircuit.requestNetwork] using h
  ram := by
    intro w p
    have h := (connected_agrees layout rom romFits ramFits i s).ram p
    simpa only [connectedValues, actualValues, busNetwork, busValues, Stream.Joint.values, Expr.eval,
      snapshot_values] using h
  mmio p := stage_mmio_output layout rom romFits ramFits i s p
  fetch _ := rfl

theorem actual_bus_output (i : Values SystemInterface.Input) (s : Values (SystemCircuit.Register aw))
    (p : BusOutput aw w) :
    (busCircuit layout rom romFits ramFits).observe (actualValues layout rom romFits ramFits i s) (fetchState s) p =
      (match p with
        | .left p => (stages layout rom romFits ramFits i s).coreInput.values p
        | .right (.left p) => (stages layout rom romFits ramFits i s).ramInput.values p
        | .right (.right p) => (stages layout rom romFits ramFits i s).mmioInput.values p) := by
  cases p with
  | left p =>
    exact (core_input_congr (actual_agrees layout rom romFits ramFits i s) layout rom romFits p).trans
      (stage_core_input layout rom romFits ramFits i s p).symm
  | right p => cases p with
    | left p =>
      exact (ram_input_congr (actual_agrees layout rom romFits ramFits i s) layout ramFits p).trans
        (stage_ram_input layout rom romFits ramFits i s p).symm
    | right p =>
      exact (mmio_input_congr (actual_agrees layout rom romFits ramFits i s) layout p).trans
        (stage_mmio_input layout rom romFits ramFits i s p).symm

theorem actual_bus_step (i : Values SystemInterface.Input) (s : Values (SystemCircuit.Register aw))
    (p : SystemInterface.Fetch w) :
    (busCircuit layout rom romFits ramFits).step (actualValues layout rom romFits ramFits i s) (fetchState s) p =
      (stages layout rom romFits ramFits i s).fetchNext.values p :=
  (fetch_next_congr (actual_agrees layout rom romFits ramFits i s) layout rom romFits p).trans
    (stage_fetch_next layout rom romFits ramFits i s p).symm

def refinement : Timed.Refinement (staged layout rom romFits ramFits)
    (SystemCircuit.circuit layout rom romFits ramFits).component where
  Rel := Eq
  step := by
    intro i s t h
    subst t
    exact funext fun w => funext fun r => staged_step layout rom romFits ramFits i s (w := w) r
  observe := by
    intro i s t h
    subst t
    exact funext fun w => funext fun o => staged_output layout rom romFits ramFits i s (w := w) o

theorem trace_eq (s : Values (SystemCircuit.Register aw)) (traffic : List (Values SystemInterface.Input)) :
    (staged layout rom romFits ramFits).trace s traffic =
      (SystemCircuit.circuit layout rom romFits ramFits).component.trace s traffic :=
  (refinement layout rom romFits ramFits).trace_eq s s rfl traffic

theorem run_eq (s : Values (SystemCircuit.Register aw)) (traffic : List (Values SystemInterface.Input)) :
    @Eq (Values (SystemCircuit.Register aw)) ((staged layout rom romFits ramFits).run s traffic)
      ((SystemCircuit.circuit layout rom romFits ramFits).component.run s traffic) :=
  (refinement layout rom romFits ramFits).run_related s s rfl traffic

end Pinwheel.Hardware.Processor.SystemExport
