import Pinwheel.Hardware.Processor.LoadableSystemModel
import Pinwheel.Hardware.Processor.LoadableSystemLoading
import Pinwheel.Hardware.Processor.SystemCertified

namespace Pinwheel.Hardware.Processor.LoadableSystem

set_option backward.isDefEq.respectTransparency false

def patchRaw (s : Values (Register aw)) (target : BitVec aw) (value : BitVec 32) : Values (Register aw) :=
  fun {b} r => match b,r with
  | _, .left p => s (.left p)
  | _, .right (.left p) => Memory.ByteAdapterLoader.rawPatch (SystemCircuit.ramValues s) target value p
  | _, .right (.right p) => s (.right (.right p))

theorem view_patch (s : Values (Register aw)) (target : BitVec aw) (value : BitVec 32) :
    SystemCircuit.view (patchRaw s target value) = patchMemory (SystemCircuit.view s) target value := by
  rfl

variable (layout : AddressMap.Layout rw aw) (rom : BitVec rw → BitVec 32)
  (romFits : rw ≤ 30) (ramFits : aw ≤ 30)

theorem resolved_adapter_pins (i : Values (Input aw)) (s : Values (Register aw)) :
    @Eq (Values (Memory.ByteAdapterInterface.Input aw))
      (Memory.ByteAdapterLoader.pins (resolvedLoaderPins layout ramFits i s))
      (SystemCircuit.ramPins layout ramFits (systemPins i) s) := by
  funext b p
  match p with
  | .at ⟨0,_⟩ =>
      exact WordOps.wordOr_eval (.input Memory.ByteAdapterLoader.reset) (.input Memory.ByteAdapterLoader.mode)
        (resolvedLoaderPins layout ramFits i s) (fun _ => 0)
  | .at ⟨1,_⟩ | .at ⟨2,_⟩ | .at ⟨3,_⟩ | .at ⟨4,_⟩ | .at ⟨5,_⟩ |
    .at ⟨6,_⟩ | .at ⟨7,_⟩ | .at ⟨8,_⟩ => exact bind_system_eval _ i s
  | .at ⟨k+9,h⟩ => exact False.elim (by change k+9 < 9 at h; omega)

theorem loader_base_eq (i : Values (Input aw)) (s : Values (Register aw)) :
    @Eq (Values (Memory.ByteAdapterLoader.Register aw))
      (Memory.ByteAdapterLoader.baseStep (resolvedLoaderPins layout ramFits i s) (SystemCircuit.ramValues s))
      (SystemCircuit.ramValues ((SystemCircuit.circuit layout rom romFits ramFits).step (systemPins i) s)) := by
  unfold Memory.ByteAdapterLoader.baseStep
  rw [resolved_adapter_pins layout ramFits i s,SystemCircuit.ram_step]

theorem loader_ram_patch (i : Values (Input aw)) (s : Values (Register aw)) :
    @Eq (Values (Memory.ByteAdapterLoader.Register aw))
      (SystemCircuit.ramValues ((circuit layout rom romFits ramFits).step i s))
      (if Accepted i then
        Memory.ByteAdapterLoader.rawPatch
          (SystemCircuit.ramValues ((SystemCircuit.circuit layout rom romFits ramFits).step (systemPins i) s))
          (i address) (i data)
       else SystemCircuit.ramValues ((SystemCircuit.circuit layout rom romFits ramFits).step (systemPins i) s)) := by
  rw [loader_ram_step,Memory.ByteAdapterLoader.circuit_step]
  simp only [loader_base_eq layout rom romFits ramFits i s]
  rfl

theorem step_patch (i : Values (Input aw)) (s : Values (Register aw)) :
    @Eq (Values (Register aw)) ((circuit layout rom romFits ramFits).step i s)
      (if Accepted i then
        patchRaw ((SystemCircuit.circuit layout rom romFits ramFits).step (systemPins i) s) (i address) (i data)
       else (SystemCircuit.circuit layout rom romFits ramFits).step (systemPins i) s) := by
  funext b r
  cases r with
  | left r =>
      have component := congrFun (congrFun (loader_core_step layout rom romFits ramFits i s) b) r
      split <;> exact component
  | right r => cases r with
    | left r =>
        have component := congrFun (congrFun (loader_ram_patch layout rom romFits ramFits i s) b) r
        split at component
        all_goals simpa only [*,↓reduceIte,patchRaw,SystemCircuit.ramValues,SystemCircuit.ram] using component
    | right r => cases r with
      | left r =>
          have component := congrFun (congrFun (loader_mmio_step layout rom romFits ramFits i s) b) r
          split <;> exact component
      | right r =>
          have component := congrFun (congrFun (loader_fetch_step layout rom romFits ramFits i s) b) r
          split <;> exact component

theorem view_step_patch (i : Values (Input aw)) (s : Values (Register aw)) :
    SystemCircuit.view ((circuit layout rom romFits ramFits).step i s) =
      (if Accepted i then
        patchMemory (SystemCircuit.view ((SystemCircuit.circuit layout rom romFits ramFits).step (systemPins i) s))
          (i address) (i data)
       else SystemCircuit.view ((SystemCircuit.circuit layout rom romFits ramFits).step (systemPins i) s)) := by
  rw [step_patch]
  split <;> simp only [view_patch]

theorem view_step (i : Values (Input aw)) (s : Values (Register aw)) (h : SystemCircuit.Valid layout rom s) :
    SystemCircuit.view ((circuit layout rom romFits ramFits).step i s) =
      (spec layout rom).step i (SystemCircuit.view s) := by
  rw [view_step_patch]
  simp only [spec,SystemCircuit.view_step layout rom romFits ramFits (systemPins i) s h]

theorem preserved (i : Values (Input aw)) (s : Values (Register aw)) (h : SystemCircuit.Valid layout rom s) :
    SystemCircuit.Valid layout rom ((circuit layout rom romFits ramFits).step i s) := by
  rcases BitVec.eq_zero_or_eq_one (i mode) with hm | hm
  · have quiet : ¬Accepted i := by simp [Accepted,hm]
    rw [step_patch]
    simp only [if_neg quiet]
    exact SystemCircuit.preserved layout rom romFits ramFits (systemPins i) s h
  · have held : ∀ j ∈ [@i], j mode = 1 := by
      intro j member
      have same : @j = @i := List.mem_singleton.mp member
      simpa [same] using hm
    have loaded := run_loading_valid layout rom romFits ramFits s [@i] (by simp) held
    simpa only [Timed.Component.run,Circuit.component] using loaded

theorem output_eq (i : Values (Input aw)) (s : Values (Register aw))
    (h : SystemCircuit.Valid layout rom s) (o : Output b) :
    (circuit layout rom romFits ramFits).observe i s o =
      (spec layout rom).observe i (SystemCircuit.view s) o := by
  match b,o with
  | _, .left o =>
      change (((SystemCircuit.circuit layout rom romFits ramFits).output o).bind systemInput Expr.reg).eval i s = _
      rw [bind_system_eval]
      exact SystemCircuit.output_eq layout rom romFits ramFits (systemPins i) s h o
  | _, .right (.at ⟨0,_⟩) | _, .right (.at ⟨1,_⟩) => rfl
  | _, .right (.at ⟨k+2,bound⟩) => exact False.elim (by change k+2 < 2 at bound; omega)

def implementation : DecodedImplementation (circuit layout rom romFits ramFits) (spec layout rom) where
  Valid := SystemCircuit.Valid layout rom
  view := SystemCircuit.view
  preserved := preserved layout rom romFits ramFits
  step_eq := view_step layout rom romFits ramFits
  output_eq i s h {_} o := output_eq layout rom romFits ramFits i s h o

theorem reset_view (i : Values (Input aw)) (s : Values (Register aw)) (hr : i reset = 1) :
    SystemCircuit.view ((circuit layout rom romFits ramFits).step i s) = SystemCircuit.resetState s := by
  rw [step_patch]
  have blocked : ¬Accepted i := by simp [Accepted,hr]
  simp only [if_neg blocked]
  exact SystemCircuit.reset_view layout rom romFits ramFits (systemPins i) s (external_system_reset i hr)

theorem reset_valid (i : Values (Input aw)) (s : Values (Register aw)) (hr : i reset = 1) :
    SystemCircuit.Valid layout rom ((circuit layout rom romFits ramFits).step i s) := by
  rw [step_patch]
  have blocked : ¬Accepted i := by simp [Accepted,hr]
  simp only [if_neg blocked]
  exact SystemCircuit.reset_valid layout rom romFits ramFits (systemPins i) s (external_system_reset i hr)

def resetCertificate : (implementation layout rom romFits ramFits).Reset reset where
  initial := SystemCircuit.resetState
  reset_valid := reset_valid layout rom romFits ramFits
  reset_view := reset_view layout rom romFits ramFits

theorem initial_coverage (state : SystemModel.State aw) (h : SystemModel.Valid layout rom state)
    (ramInactive : Values (Memory.ByteAdapterCircuit.Metadata aw)) (fetchInactive : Values SystemInterface.Fetch) :
    ∃ raw : Values (Register aw), SystemCircuit.Valid layout rom raw ∧ SystemCircuit.view raw = state :=
  SystemCircuit.initial_coverage layout rom state h ramInactive fetchInactive

theorem trace_correct (s : Values (Register aw)) (h : SystemCircuit.Valid layout rom s)
    (traffic : List (Values (Input aw))) :
    (circuit layout rom romFits ramFits).component.trace s traffic =
      (spec layout rom).trace (SystemCircuit.view s) traffic :=
  (implementation layout rom romFits ramFits).trace_eq s h traffic

theorem run_correct (s : Values (Register aw)) (h : SystemCircuit.Valid layout rom s)
    (traffic : List (Values (Input aw))) :
    SystemCircuit.view ((circuit layout rom romFits ramFits).component.run s traffic) =
      (spec layout rom).run (SystemCircuit.view s) traffic :=
  (implementation layout rom romFits ramFits).run_eq s h traffic

theorem run_after_loading (s : Values (Register aw)) (loading traffic : List (Values (Input aw)))
    (modeHeld : ∀ i ∈ loading, i mode = 1) (image : BitVec aw → BitVec 32)
    (values : ImageWrites image loading) (coverage : Covers loading) :
    SystemCircuit.view ((circuit layout rom romFits ramFits).component.run
      ((circuit layout rom romFits ramFits).component.run s loading) traffic) =
      (spec layout rom).run (SystemModel.initial image (s q)) traffic := by
  rw [run_correct layout rom romFits ramFits _
    (run_loading_valid layout rom romFits ramFits s loading (covers_nonempty loading coverage) modeHeld) traffic,
    complete_image layout rom romFits ramFits s loading modeHeld image values coverage]

theorem trace_after_loading (s : Values (Register aw)) (loading traffic : List (Values (Input aw)))
    (modeHeld : ∀ i ∈ loading, i mode = 1) (image : BitVec aw → BitVec 32)
    (values : ImageWrites image loading) (coverage : Covers loading) :
    (circuit layout rom romFits ramFits).component.trace
      ((circuit layout rom romFits ramFits).component.run s loading) traffic =
      (spec layout rom).trace (SystemModel.initial image (s q)) traffic := by
  rw [trace_correct layout rom romFits ramFits _
    (run_loading_valid layout rom romFits ramFits s loading (covers_nonempty loading coverage) modeHeld) traffic,
    complete_image layout rom romFits ramFits s loading modeHeld image values coverage]

theorem spec_run_normal (state : SystemModel.State aw) (traffic : List (Values (Input aw)))
    (modeOff : ∀ i ∈ traffic, i mode = 0) :
    (spec layout rom).run state traffic =
      (SystemModel.component layout rom).run state (traffic.map (fun i => SystemCircuit.decode (systemPins i))) := by
  induction traffic generalizing state with
  | nil => rfl
  | cons i rest ih =>
      have hm := modeOff i (by simp)
      have blocked : ¬Accepted i := by simp [Accepted,hm]
      change (spec layout rom).run ((spec layout rom).step i state) rest =
        (SystemModel.component layout rom).run
          (SystemModel.step layout rom (SystemCircuit.decode (systemPins i)) state)
          (rest.map (fun j => SystemCircuit.decode (systemPins j)))
      have first : (spec layout rom).step i state =
          SystemModel.step layout rom (SystemCircuit.decode (systemPins i)) state := by
        simp only [spec,if_neg blocked,SystemCircuit.spec]
      rw [first]
      exact ih _ (fun j hj => modeOff j (by simp [hj]))

theorem system_run_after_loading (s : Values (Register aw)) (loading traffic : List (Values (Input aw)))
    (modeHeld : ∀ i ∈ loading, i mode = 1) (image : BitVec aw → BitVec 32)
    (values : ImageWrites image loading) (coverage : Covers loading)
    (modeOff : ∀ i ∈ traffic, i mode = 0) :
    SystemCircuit.view ((circuit layout rom romFits ramFits).component.run
      ((circuit layout rom romFits ramFits).component.run s loading) traffic) =
      (SystemModel.component layout rom).run (SystemModel.initial image (s q))
        (traffic.map (fun i => SystemCircuit.decode (systemPins i))) := by
  rw [run_after_loading layout rom romFits ramFits s loading traffic modeHeld image values coverage,
    spec_run_normal layout rom _ traffic modeOff]

theorem artifact_run_after_loading
    (rtl : Timed.Component (Values (Input aw)) (Values (Register aw)) (Values Output))
    (artifact : Artifact.Correspondence (circuit layout rom romFits ramFits) rtl)
    (s : Values (Register aw)) (loading traffic : List (Values (Input aw)))
    (modeHeld : ∀ i ∈ loading, i mode = 1) (image : BitVec aw → BitVec 32)
    (values : ImageWrites image loading) (coverage : Covers loading)
    (modeOff : ∀ i ∈ traffic, i mode = 0) :
    SystemCircuit.view (rtl.run (rtl.run s loading) traffic) =
      (SystemModel.component layout rom).run (SystemModel.initial image (s q))
        (traffic.map (fun i => SystemCircuit.decode (systemPins i))) := by
  have loading_eq : @Eq (Values (Register aw)) (rtl.run s loading)
      ((circuit layout rom romFits ramFits).component.run s loading) :=
    artifact.refinement.run_related s s rfl loading
  have execution_eq := (implementation layout rom romFits ramFits).artifact_run_eq artifact _
    (run_loading_valid layout rom romFits ramFits s loading (covers_nonempty loading coverage) modeHeld) traffic
  dsimp only [implementation] at execution_eq
  rw [loading_eq,execution_eq,
    complete_image layout rom romFits ramFits s loading modeHeld image values coverage,
    spec_run_normal layout rom _ traffic modeOff]

end Pinwheel.Hardware.Processor.LoadableSystem
