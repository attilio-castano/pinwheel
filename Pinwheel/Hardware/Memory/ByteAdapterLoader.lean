import Pinwheel.Hardware.Memory.ByteAdapterCircuitProofs
import Pinwheel.Hardware.WordOps

/-! An exclusive full-word loader around the byte adapter. Loading resets the
transaction interface and cancels pending work while preserving words/Q and
retained metadata. Accepted loader writes change one physical RAM word on that
edge. The system must hold its core quiescent throughout loader ownership. -/
namespace Pinwheel.Hardware.Memory.ByteAdapterLoader

set_option backward.isDefEq.respectTransparency false

def loaderPorts (a : Nat) : Stream.Ports where
  size := 4
  widths := fun k => if k.val = 2 then a else if k.val = 3 then 32 else 1
  names := fun k => #["loader_mode","loader_valid","loader_address","loader_data"][k]
  distinct := by decide +kernel
abbrev Loader (a : Nat) := (loaderPorts a).Signal
abbrev Input (a : Nat) := Stream.Joint (ByteAdapterInterface.Input a) (Loader a)
abbrev Register (a : Nat) := ByteAdapterCircuit.Register a
inductive LoaderOutput : Nat → Type where
  | ready : LoaderOutput 1
abbrev Output := Stream.Joint ByteAdapterInterface.Output LoaderOutput

def loaderOutputs : Interface LoaderOutput where
  size := 1
  signal _ := ⟨1,.ready⟩
  position _ := 0
  signal_position r := by cases r; rfl
  label _ := "loader_ready"
  unique := by intros; exact Subsingleton.elim _ _

def inputs (a : Nat) : Interface (Input a) := Stream.Joint.interface (ByteAdapterInterface.inputs a) (loaderPorts a).interface
def outputs : Interface Output := Stream.Joint.interface ByteAdapterInterface.outputs loaderOutputs
def registers (a : Nat) : Interface (Register a) := ByteAdapterCircuit.registers a

def mode : Input a 1 := .right (.at ⟨0,by change 0 < 4; decide⟩)
def valid : Input a 1 := .right (.at ⟨1,by change 1 < 4; decide⟩)
def address : Input a a := .right (.at ⟨2,by change 2 < 4; decide⟩)
def data : Input a 32 := .right (.at ⟨3,by change 3 < 4; decide⟩)
def reset : Input a 1 := .left ByteAdapterInterface.reset

def ready : Expr (Input a) (Register a) 1 := .band (.input mode) (.inv (.input reset))
def accepted : Expr (Input a) (Register a) 1 := .band ready (.input valid)

def adapterInput : {b : Nat} → ByteAdapterInterface.Input a b → Expr (Input a) (Register a) b
  | _, .at ⟨0,_⟩ => WordOps.wordOr (.input reset) (.input mode)
  | _, .at ⟨1,h⟩ => .input (.left (.at ⟨1,h⟩))
  | _, .at ⟨2,h⟩ => .input (.left (.at ⟨2,h⟩))
  | _, .at ⟨3,h⟩ => .input (.left (.at ⟨3,h⟩))
  | _, .at ⟨4,h⟩ => .input (.left (.at ⟨4,h⟩))
  | _, .at ⟨5,h⟩ => .input (.left (.at ⟨5,h⟩))
  | _, .at ⟨6,h⟩ => .input (.left (.at ⟨6,h⟩))
  | _, .at ⟨7,h⟩ => .input (.left (.at ⟨7,h⟩))
  | _, .at ⟨8,h⟩ => .input (.left (.at ⟨8,h⟩))
  | _, .at ⟨k+9,h⟩ => False.elim (by change k+9 < 9 at h; omega)

def pins (i : Values (Input a)) : Values (ByteAdapterInterface.Input a) :=
  fun p => (adapterInput p).eval i (fun _ => 0)

def baseStep (i : Values (Input a)) (s : Values (Register a)) : Values (Register a) :=
  (ByteAdapterCircuit.circuit a).step (pins i) s

def next : {b : Nat} → Register a b → Expr (Input a) (Register a) b
  | _, .left (.left (.word k)) =>
      .mux (.band accepted (.equal (.input address) (.lit k))) (.input data)
        (((ByteAdapterCircuit.circuit a).next (.left (CommandFlops.word k))).bind adapterInput Expr.reg)
  | _, .left (.right .q) => ((ByteAdapterCircuit.circuit a).next (.left CommandFlops.q)).bind adapterInput Expr.reg
  | _, .right r => ((ByteAdapterCircuit.circuit a).next (.right r)).bind adapterInput Expr.reg

def circuit (a : Nat) : Circuit (Input a) (Register a) Output where
  next := next
  output := fun {b} o => match b,o with
    | _, .left o => ((ByteAdapterCircuit.circuit a).output o).bind adapterInput Expr.reg
    | _, .right .ready => ready

def view (s : Values (Register a)) : ByteAdapterModel.State a := ByteAdapterCircuit.view s

/-- The base adapter first cancels ownership under loader mode. The loader then
changes one word, with Q retained. This order also specifies reset priority. -/
def spec (a : Nat) : Timed.Component (Values (Input a)) (ByteAdapterModel.State a) (Values Output) where
  step i s :=
    let base := ByteAdapterModel.step (ByteAdapterInterface.decode (pins i)) s
    if i mode = 1 ∧ i reset = 0 ∧ i valid = 1 then
      {base with memory := {base.memory with contents := fun k => if i address = k then i data else base.memory.contents k}}
    else base
  observe := fun i s {b} o => match b,o with
    | _, .left o => (ByteAdapterInterface.spec a).observe (pins i) s o
    | _, .right .ready => BitVec.ofBool (i mode = 1 && i reset = 0)

theorem adapter_eval (p : ByteAdapterInterface.Input a b) (i : Values (Input a)) (s : Values (Register a)) :
    (adapterInput p).eval i s = pins i p := by
  match p with
  | .at ⟨0,_⟩ | .at ⟨1,_⟩ | .at ⟨2,_⟩ | .at ⟨3,_⟩ | .at ⟨4,_⟩ |
    .at ⟨5,_⟩ | .at ⟨6,_⟩ | .at ⟨7,_⟩ | .at ⟨8,_⟩ => rfl
  | .at ⟨k+9,h⟩ => exact False.elim (by change k+9 < 9 at h; omega)

theorem word_step (i : Values (Input a)) (s : Values (Register a)) (k : BitVec a) :
    (circuit a).step i s (.left (CommandFlops.word k)) =
      if i mode = 1 ∧ i reset = 0 ∧ i valid = 1 ∧ i address = k then i data
      else baseStep i s (.left (CommandFlops.word k)) := by
  simp only [Circuit.step,circuit,CommandFlops.word,next,accepted,ready,Expr.eval,Expr.eval_bind,adapter_eval]
  rcases BitVec.eq_zero_or_eq_one (i mode) with hm | hm
  all_goals rcases BitVec.eq_zero_or_eq_one (i reset) with hr | hr
  all_goals rcases BitVec.eq_zero_or_eq_one (i valid) with hv | hv
  all_goals by_cases ha : i address = k
  all_goals simp [hm,hr,hv,ha,baseStep,Circuit.step]

theorem q_step (i : Values (Input a)) (s : Values (Register a)) :
    (circuit a).step i s (.left CommandFlops.q) = baseStep i s (.left CommandFlops.q) := by
  simp only [Circuit.step,circuit,CommandFlops.q,next,Expr.eval_bind,adapter_eval,baseStep]
  rfl

theorem metadata_step (i : Values (Input a)) (s : Values (Register a)) (r : ByteAdapterCircuit.Metadata a b) :
    (circuit a).step i s (.right r) = baseStep i s (.right r) := by
  simp only [Circuit.step,circuit,next,Expr.eval_bind,adapter_eval,baseStep]
  rfl

def rawPatch (s : Values (Register a)) (target : BitVec a) (value : BitVec 32) : Values (Register a) :=
  fun {b} r => match b,r with
  | _, .left (.left (.word k)) => if target = k then value else s (.left (CommandFlops.word k))
  | _, .left (.right .q) => s (.left CommandFlops.q)
  | _, .right r => s (.right r)

theorem view_patch (s : Values (Register a)) (target : BitVec a) (value : BitVec 32) :
    view (rawPatch s target value) =
      {view s with memory := {(view s).memory with contents := fun k => if target = k then value else (view s).memory.contents k}} := by
  rfl

theorem circuit_step (i : Values (Input a)) (s : Values (Register a)) :
    @Eq (Values (Register a)) ((circuit a).step i s)
      (if i mode = 1 ∧ i reset = 0 ∧ i valid = 1 then rawPatch (baseStep i s) (i address) (i data) else baseStep i s) := by
  funext b r
  match b,r with
  | _, .left (.left (.word k)) =>
      have hw := word_step i s k
      dsimp only [CommandFlops.word] at hw
      rw [hw]
      rcases BitVec.eq_zero_or_eq_one (i mode) with hm | hm
      all_goals rcases BitVec.eq_zero_or_eq_one (i reset) with hr | hr
      all_goals rcases BitVec.eq_zero_or_eq_one (i valid) with hv | hv
      all_goals simp [hm,hr,hv,rawPatch,CommandFlops.word]
  | _, .left (.right .q) =>
      have hq := q_step i s
      dsimp only [CommandFlops.q] at hq
      rw [hq]
      split <;> rfl
  | _, .right r => rw [metadata_step i s r]; split <;> rfl

theorem view_base (i : Values (Input a)) (s : Values (Register a)) :
    view (baseStep i s) = ByteAdapterModel.step (ByteAdapterInterface.decode (pins i)) (view s) :=
  ByteAdapterCircuit.view_step (pins i) s

theorem view_step (i : Values (Input a)) (s : Values (Register a)) :
    view ((circuit a).step i s) = (spec a).step i (view s) := by
  rw [circuit_step]
  rcases BitVec.eq_zero_or_eq_one (i mode) with hm | hm
  all_goals rcases BitVec.eq_zero_or_eq_one (i reset) with hr | hr
  all_goals rcases BitVec.eq_zero_or_eq_one (i valid) with hv | hv
  all_goals simp [hm,hr,hv,view_patch,view_base,spec]

theorem output_eq (i : Values (Input a)) (s : Values (Register a)) (o : Output b) :
    (circuit a).observe i s o = (spec a).observe i (view s) o := by
  match b,o with
  | _, .left o =>
      simp only [Circuit.observe,circuit,Expr.eval_bind,adapter_eval,Expr.eval]
      exact ByteAdapterCircuit.output_eq (pins i) s o
  | _, .right .ready =>
      rcases BitVec.eq_zero_or_eq_one (i mode) with hm | hm
      all_goals rcases BitVec.eq_zero_or_eq_one (i reset) with hr | hr
      all_goals simp [Circuit.observe,circuit,spec,ready,Expr.eval,hm,hr]

theorem mode_resets (i : Values (Input a)) (h : i mode = 1) : pins i ByteAdapterInterface.reset = 1 := by
  rcases BitVec.eq_zero_or_eq_one (i reset) with hr | hr
  all_goals simp [pins,ByteAdapterInterface.reset,adapterInput,WordOps.wordOr_eval,Expr.eval,h,hr]

theorem external_resets (i : Values (Input a)) (h : i reset = 1) : pins i ByteAdapterInterface.reset = 1 := by
  rcases BitVec.eq_zero_or_eq_one (i mode) with hm | hm
  all_goals simp [pins,ByteAdapterInterface.reset,adapterInput,WordOps.wordOr_eval,Expr.eval,h,hm]

theorem reset_view (i : Values (Input a)) (s : Values (Register a)) (h : i reset = 1) :
    view ((circuit a).step i s) = ByteAdapterModel.resetState (view s) := by
  rw [view_step]
  have hp := external_resets i h
  simp only [spec]
  simp [h]
  exact ByteAdapterModel.reset_state _ _ (by simp [ByteAdapterInterface.decode,hp])

def implementation (a : Nat) : DecodedImplementation (circuit a) (spec a) where
  Valid _ := True
  view := view
  preserved _ _ _ := trivial
  step_eq i s _ := view_step i s
  output_eq i s _ {_} o := output_eq i s o

def resetCertificate (a : Nat) : (implementation a).Reset reset where
  initial s := ByteAdapterModel.resetState (view s)
  reset_valid _ _ _ := trivial
  reset_view := reset_view

theorem loader_pending (i : Values (Input a)) (s : Values (Register a)) (h : i mode = 1) :
    (view ((circuit a).step i s)).pending = none := by
  rw [view_step]
  have base := ByteAdapterModel.reset_state (ByteAdapterInterface.decode (pins i)) (view s)
    (by simp [ByteAdapterInterface.decode,mode_resets i h])
  simp only [spec,base]
  split <;> rfl

theorem loader_word (i : Values (Input a)) (s : Values (Register a)) (h : i mode = 1) (k : BitVec a) :
    (circuit a).step i s (.left (CommandFlops.word k)) =
      if i reset = 0 ∧ i valid = 1 ∧ i address = k then i data else s (.left (CommandFlops.word k)) := by
  rw [word_step]
  have base := ByteAdapterCircuit.reset_memory (pins i) s (mode_resets i h) (CommandFlops.word k)
  change baseStep i s (.left (CommandFlops.word k)) = s (.left (CommandFlops.word k)) at base
  simp only [h,true_and,base]

theorem loader_q (i : Values (Input a)) (s : Values (Register a)) (h : i mode = 1) :
    (circuit a).step i s (.left CommandFlops.q) = s (.left CommandFlops.q) := by
  rw [q_step]
  exact ByteAdapterCircuit.reset_memory (pins i) s (mode_resets i h) CommandFlops.q

theorem loader_masks_adapter (i : Values (Input a)) (s : Values (Register a)) (h : i mode = 1)
    (o : ByteAdapterInterface.Output b) : (circuit a).observe i s (.left o) = 0 := by
  have result := ByteAdapterCircuit.reset_outputs (pins i) s (mode_resets i h) o
  simpa only [Circuit.observe,circuit,Expr.eval_bind,adapter_eval,Expr.eval] using result

theorem run_correct (s : Values (Register a)) (traffic : List (Values (Input a))) :
    view ((circuit a).component.run s traffic) = (spec a).run (view s) traffic :=
  (implementation a).run_eq s trivial traffic

end Pinwheel.Hardware.Memory.ByteAdapterLoader
