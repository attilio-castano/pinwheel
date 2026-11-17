import Pinwheel.Hardware.Processor.LoadableSystemStaged

namespace Pinwheel.Hardware.Processor.LoadableSystem

set_option backward.isDefEq.respectTransparency false

theorem system_input_eval (i : Values (Input aw)) (s : Values (Register aw))
    (p : SystemInterface.Input b) : (systemInput p).eval i s = systemPins i p := by
  match p with
  | .at ⟨0,_⟩ => exact WordOps.wordOr_eval (.input reset) (.input mode) i s
  | .at ⟨1,_⟩ | .at ⟨2,_⟩ | .at ⟨3,_⟩ | .at ⟨4,_⟩ | .at ⟨5,_⟩ => rfl
  | .at ⟨k+6,h⟩ => exact False.elim (by change k+6 < 6 at h; omega)

theorem bind_system_eval (e : Expr SystemInterface.Input (Register aw) b)
    (i : Values (Input aw)) (s : Values (Register aw)) :
    (e.bind systemInput Expr.reg).eval i s = e.eval (systemPins i) s := by
  simp only [Expr.eval_bind,system_input_eval,Expr.eval]

variable (layout : AddressMap.Layout rw aw) (rom : BitVec rw → BitVec 32)
  (romFits : rw ≤ 30) (ramFits : aw ≤ 30)

theorem loader_input_eval (i : Values (Input aw)) (s : Values (Register aw))
    (p : Memory.ByteAdapterLoader.Input aw b) :
    (loaderInput layout ramFits p).eval i s =
      loaderPins i (SystemExport.stages layout rom romFits ramFits (systemPins i) s).ramInput.values p := by
  match b,p with
  | _, .left (.at ⟨0,_⟩) => rfl
  | _, .left (.at ⟨1,h⟩) | _, .left (.at ⟨2,h⟩) | _, .left (.at ⟨3,h⟩) |
    _, .left (.at ⟨4,h⟩) | _, .left (.at ⟨5,h⟩) | _, .left (.at ⟨6,h⟩) |
    _, .left (.at ⟨7,h⟩) | _, .left (.at ⟨8,h⟩) =>
      exact (bind_system_eval _ i s).trans (SystemExport.stage_ram_input layout rom romFits ramFits (systemPins i) s _).symm
  | _, .left (.at ⟨k+9,h⟩) => exact False.elim (by change k+9 < 9 at h; omega)
  | _, .right p => rfl

theorem staged_ram_step (i : Values (Input aw)) (s : Values (Register aw))
    (r : Memory.ByteAdapterLoader.Register aw b) :
    (staged layout rom romFits ramFits).step i s (SystemCircuit.ram r) =
      (circuit layout rom romFits ramFits).step i s (SystemCircuit.ram r) := by
  simp only [staged,nextSnapshot,SystemExport.snapshot_values,Circuit.step,circuit,next,
    SystemCircuit.ram,Expr.eval_bind,Expr.eval]
  congr 1
  funext w p
  simpa only [SystemExport.snapshot_values] using (loader_input_eval layout rom romFits ramFits i s p).symm

theorem staged_step (i : Values (Input aw)) (s : Values (Register aw)) (r : Register aw b) :
    (staged layout rom romFits ramFits).step i s r =
      (circuit layout rom romFits ramFits).step i s r := by
  cases r with
  | left r =>
      simpa only [staged,nextSnapshot,SystemExport.snapshot_values,Circuit.step,circuit,next,bind_system_eval,
        SystemExport.staged,SystemExport.nextSnapshot] using
        (SystemExport.staged_step layout rom romFits ramFits (systemPins i) s (.left r))
  | right r => cases r with
    | left r => exact staged_ram_step layout rom romFits ramFits i s r
    | right r => cases r with
      | left r =>
          simpa only [staged,nextSnapshot,SystemExport.snapshot_values,Circuit.step,circuit,next,bind_system_eval,
            SystemExport.staged,SystemExport.nextSnapshot] using
            (SystemExport.staged_step layout rom romFits ramFits (systemPins i) s (.right (.right (.left r))))
      | right r =>
          simpa only [staged,nextSnapshot,SystemExport.snapshot_values,Circuit.step,circuit,next,bind_system_eval,
            SystemExport.staged,SystemExport.nextSnapshot] using
            (SystemExport.staged_step layout rom romFits ramFits (systemPins i) s (.right (.right (.right r))))

theorem staged_system_output (i : Values (Input aw)) (s : Values (Register aw))
    (o : SystemCircuit.Output b) :
    (staged layout rom romFits ramFits).observe i s (.left o) =
      (circuit layout rom romFits ramFits).observe i s (.left o) := by
  simp only [staged,outputSnapshot,SystemExport.snapshot_values]
  change _ = (((SystemCircuit.circuit layout rom romFits ramFits).output o).bind systemInput Expr.reg).eval i s
  rw [bind_system_eval]
  exact SystemExport.staged_output layout rom romFits ramFits (systemPins i) s o

theorem staged_output (i : Values (Input aw)) (s : Values (Register aw)) (o : Output b) :
    (staged layout rom romFits ramFits).observe i s o =
      (circuit layout rom romFits ramFits).observe i s o := by
  match b,o with
  | _, .left o => exact staged_system_output layout rom romFits ramFits i s o
  | _, .right (.at ⟨0,_⟩) | _, .right (.at ⟨1,_⟩) =>
      simp only [staged,outputSnapshot,SystemExport.snapshot_values,Circuit.observe,circuit,Expr.eval]
  | _, .right (.at ⟨k+2,h⟩) => exact False.elim (by change k+2 < 2 at h; omega)

def refinement : Timed.Refinement (staged layout rom romFits ramFits)
    (circuit layout rom romFits ramFits).component where
  Rel := Eq
  step := by
    intro i s t h
    subst t
    exact funext fun b => funext fun r => staged_step layout rom romFits ramFits i s (b := b) r
  observe := by
    intro i s t h
    subst t
    exact funext fun b => funext fun o => staged_output layout rom romFits ramFits i s (b := b) o

theorem trace_eq (s : Values (Register aw)) (traffic : List (Values (Input aw))) :
    (staged layout rom romFits ramFits).trace s traffic =
      (circuit layout rom romFits ramFits).component.trace s traffic :=
  (refinement layout rom romFits ramFits).trace_eq s s rfl traffic

theorem run_eq (s : Values (Register aw)) (traffic : List (Values (Input aw))) :
    @Eq (Values (Register aw)) ((staged layout rom romFits ramFits).run s traffic)
      ((circuit layout rom romFits ramFits).component.run s traffic) :=
  (refinement layout rom romFits ramFits).run_related s s rfl traffic

end Pinwheel.Hardware.Processor.LoadableSystem
