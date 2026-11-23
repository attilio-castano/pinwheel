import Pinwheel.Hardware.Processor.LoadableSystemStagedProofs
import Pinwheel.Hardware.Processor.SystemCircuitState

/-! Canonical physical loading from arbitrary register bits. Loader ownership
keeps CPU/devices/fetch reset, cancels RAM transactions, and preserves Q and
inactive metadata. A complete accepted-write history establishes the supplied
image before release; no prior-memory initialization is assumed.
-/
namespace Pinwheel.Hardware.Processor.LoadableSystem

open Memory
set_option backward.isDefEq.respectTransparency false

def word (k : BitVec aw) : Register aw 32 := SystemCircuit.ram (.left (CommandFlops.word k))
def q : Register aw 32 := SystemCircuit.ram (.left CommandFlops.q)

variable (layout : AddressMap.Layout rw aw) (rom : BitVec rw → BitVec 32)
  (romFits : rw ≤ 30) (ramFits : aw ≤ 30)

def resolvedLoaderPins (i : Values (Input aw)) (s : Values (Register aw)) :
    Values (ByteAdapterLoader.Input aw) := fun p => (loaderInput layout ramFits p).eval i s

theorem loader_core_step (i : Values (Input aw)) (s : Values (Register aw)) :
    @Eq (Values CoreCircuit.Register)
      (SystemCircuit.coreValues ((circuit layout rom romFits ramFits).step i s))
      (SystemCircuit.coreValues ((SystemCircuit.circuit layout rom romFits ramFits).step (systemPins i) s)) := by
  funext b r
  simp only [SystemCircuit.coreValues, SystemCircuit.core, Circuit.step, circuit, next, bind_system_eval]

theorem loader_mmio_step (i : Values (Input aw)) (s : Values (Register aw)) :
    @Eq (Values MmioCircuit.Register)
      (SystemCircuit.mmioValues ((circuit layout rom romFits ramFits).step i s))
      (SystemCircuit.mmioValues ((SystemCircuit.circuit layout rom romFits ramFits).step (systemPins i) s)) := by
  funext b r
  simp only [SystemCircuit.mmioValues, SystemCircuit.mmio, Circuit.step, circuit, next, bind_system_eval]

theorem loader_ram_step (i : Values (Input aw)) (s : Values (Register aw)) :
    @Eq (Values (ByteAdapterLoader.Register aw))
      (SystemCircuit.ramValues ((circuit layout rom romFits ramFits).step i s))
      ((ByteAdapterLoader.circuit aw).step (resolvedLoaderPins layout ramFits i s) (SystemCircuit.ramValues s)) := by
  funext b r
  simp only [SystemCircuit.ramValues, SystemCircuit.ram, Circuit.step, circuit, next, Expr.eval_bind, Expr.eval]
  rfl

theorem loader_fetch_step (i : Values (Input aw)) (s : Values (Register aw)) :
    @Eq (Values SystemInterface.Fetch)
      (SystemCircuit.fetchValues ((circuit layout rom romFits ramFits).step i s))
      (SystemCircuit.fetchValues ((SystemCircuit.circuit layout rom romFits ramFits).step (systemPins i) s)) := by
  funext b r
  simp only [SystemCircuit.fetchValues, SystemCircuit.fetch, Circuit.step, circuit, next, bind_system_eval]

theorem mode_system_reset (i : Values (Input aw)) (hm : i mode = 1) :
    systemPins i SystemInterface.reset = 1 := by
  change i reset ||| i mode = 1
  rcases BitVec.eq_zero_or_eq_one (i reset) with hr | hr <;> simp [hm, hr]

theorem external_system_reset (i : Values (Input aw)) (hr : i reset = 1) :
    systemPins i SystemInterface.reset = 1 := by
  change i reset ||| i mode = 1
  simp [hr]

theorem loading_core (i : Values (Input aw)) (s : Values (Register aw))
    (hm : i mode = 1) (r : CoreCircuit.Register b) :
    (circuit layout rom romFits ramFits).step i s (SystemCircuit.core r) = 0 := by
  have projection := congrFun (congrFun (loader_core_step layout rom romFits ramFits i s) b) r
  refine projection.trans ?_
  have component := congrFun (congrFun (SystemCircuit.core_step layout rom romFits ramFits (systemPins i) s) b) r
  exact component.trans (CoreCircuit.reset_eq _ _ (mode_system_reset i hm) r)

theorem loading_mmio (i : Values (Input aw)) (s : Values (Register aw))
    (hm : i mode = 1) (r : MmioCircuit.Register b) :
    (circuit layout rom romFits ramFits).step i s (SystemCircuit.mmio r) = 0 := by
  have projection := congrFun (congrFun (loader_mmio_step layout rom romFits ramFits i s) b) r
  refine projection.trans ?_
  have component := congrFun (congrFun (SystemCircuit.mmio_step layout rom romFits ramFits (systemPins i) s) b) r
  exact component.trans (MmioCircuit.reset_eq _ _ (mode_system_reset i hm) r)

theorem loading_word (i : Values (Input aw)) (s : Values (Register aw)) (hm : i mode = 1) (k : BitVec aw) :
    (circuit layout rom romFits ramFits).step i s (word k) =
      if i reset = 0 ∧ i valid = 1 ∧ i address = k then i data else s (word k) := by
  have projection := congrFun (congrFun (loader_ram_step layout rom romFits ramFits i s) 32) (.left (CommandFlops.word k))
  exact projection.trans (ByteAdapterLoader.loader_word _ _ hm k)

theorem loading_q (i : Values (Input aw)) (s : Values (Register aw)) (hm : i mode = 1) :
    (circuit layout rom romFits ramFits).step i s q = s q := by
  have projection := congrFun (congrFun (loader_ram_step layout rom romFits ramFits i s) 32) (.left CommandFlops.q)
  exact projection.trans (ByteAdapterLoader.loader_q _ _ hm)

theorem loading_pending (i : Values (Input aw)) (s : Values (Register aw)) (hm : i mode = 1) :
    (circuit layout rom romFits ramFits).step i s (SystemCircuit.ram ByteAdapterCircuit.pending) = 0 := by
  have projection := congrFun (congrFun (loader_ram_step layout rom romFits ramFits i s) 1) ByteAdapterCircuit.pending
  refine projection.trans ?_
  exact (ByteAdapterLoader.metadata_step _ _ ByteAdapterCircuit.metaPending).trans
    (ByteAdapterCircuit.reset_pending _ _ (ByteAdapterLoader.mode_resets _ hm))

theorem loading_metadata (i : Values (Input aw)) (s : Values (Register aw)) (hm : i mode = 1)
    (r : ByteAdapterCircuit.Metadata aw b) (hk : ((ByteAdapterCircuit.metadataPorts aw).interface.position r).val ≠ 6) :
    (circuit layout rom romFits ramFits).step i s (SystemCircuit.ram (.right r)) = s (SystemCircuit.ram (.right r)) := by
  have projection := congrFun (congrFun (loader_ram_step layout rom romFits ramFits i s) b) (.right r)
  exact projection.trans ((ByteAdapterLoader.metadata_step _ _ r).trans
    (ByteAdapterCircuit.reset_metadata _ _ (ByteAdapterLoader.mode_resets _ hm) r hk))

theorem loading_fetch_valid (i : Values (Input aw)) (s : Values (Register aw)) (hm : i mode = 1) :
    (circuit layout rom romFits ramFits).step i s SystemCircuit.fetchValid = 0 := by
  change (((SystemCircuit.circuit layout rom romFits ramFits).next SystemCircuit.fetchValid).bind systemInput Expr.reg).eval i s = 0
  rw [bind_system_eval]
  simp [SystemCircuit.circuit, SystemCircuit.fetchValid, SystemCircuit.fetch, SystemCircuit.fetchNext,
    SystemWiring.fetchNext, SystemWiring.both, SystemCircuit.requestNetwork, Expr.eval, mode_system_reset i hm]

theorem loading_view (i : Values (Input aw)) (s : Values (Register aw)) (hm : i mode = 1) :
    SystemCircuit.view ((circuit layout rom romFits ramFits).step i s) =
      SystemModel.initial
        (fun k => if i reset = 0 ∧ i valid = 1 ∧ i address = k then i data else s (word k)) (s q) := by
  have hc : @Eq (Values CoreCircuit.Register)
      (SystemCircuit.coreValues ((circuit layout rom romFits ramFits).step i s)) CoreCircuit.zeroValues := by
    funext b r
    exact loading_core layout rom romFits ramFits i s hm r
  have hp : @Eq (Values MmioCircuit.Register)
      (SystemCircuit.mmioValues ((circuit layout rom romFits ramFits).step i s)) (fun _ => 0) := by
    funext b r
    exact loading_mmio layout rom romFits ramFits i s hm r
  simp only [SystemCircuit.view, hc, hp, CoreCircuit.zero_view]
  have hf : SystemCircuit.fetchView ((circuit layout rom romFits ramFits).step i s) = none := by
    simp [SystemCircuit.fetchView, loading_fetch_valid layout rom romFits ramFits i s hm]
  rw [hf]
  change SystemModel.State.mk CoreModel.initial
    ⟨⟨(fun k => (circuit layout rom romFits ramFits).step i s (word k)),
      (circuit layout rom romFits ramFits).step i s q⟩,
      if (circuit layout rom romFits ramFits).step i s (SystemCircuit.ram ByteAdapterCircuit.pending) = 1
      then some _ else none⟩ MmioModel.initial none = _
  simp only [loading_q layout rom romFits ramFits i s hm, loading_pending layout rom romFits ramFits i s hm]
  simp only [show (0 : BitVec 1) ≠ 1 by decide, ↓reduceIte]
  congr 3
  funext k
  exact loading_word layout rom romFits ramFits i s hm k

/-- Every admitted loader word carries the desired image value. Invalid cycles
and external reset may carry arbitrary address/data garbage. -/
def ImageWrites (image : BitVec aw → BitVec 32) (traffic : List (Values (Input aw))) : Prop :=
  ∀ i ∈ traffic, Accepted i → i data = image (i address)

/-- Coverage is by actual accepted writes, not merely by offered addresses. -/
def Covers (traffic : List (Values (Input aw))) : Prop :=
  ∀ k : BitVec aw, ∃ i ∈ traffic, Accepted i ∧ i address = k

theorem run_q (s : Values (Register aw)) (traffic : List (Values (Input aw)))
    (modeHeld : ∀ i ∈ traffic, i mode = 1) :
    ((circuit layout rom romFits ramFits).component.run s traffic) q = s q := by
  induction traffic generalizing s with
  | nil => rfl
  | cons i rest ih =>
    change ((circuit layout rom romFits ramFits).component.run
      ((circuit layout rom romFits ramFits).step i s) rest) q = s q
    rw [ih _ (fun j hj => modeHeld j (by simp [hj]))]
    exact loading_q layout rom romFits ramFits i s (modeHeld i (by simp))

theorem run_word_image (s : Values (Register aw)) (traffic : List (Values (Input aw)))
    (modeHeld : ∀ i ∈ traffic, i mode = 1) (image : BitVec aw → BitVec 32)
    (values : ImageWrites image traffic) (k : BitVec aw) :
    ((circuit layout rom romFits ramFits).component.run s traffic) (word k) =
      if ∃ i ∈ traffic, Accepted i ∧ i address = k then image k else s (word k) := by
  classical
  induction traffic generalizing s with
  | nil => simp [Timed.Component.run]
  | cons i rest ih =>
    have hm := modeHeld i (by simp)
    have hmTail : ∀ j ∈ rest, j mode = 1 := fun j hj => modeHeld j (by simp [hj])
    have hvTail : ImageWrites image rest := fun j hj => values j (by simp [hj])
    change ((circuit layout rom romFits ramFits).component.run
      ((circuit layout rom romFits ramFits).step i s) rest) (word k) = _
    rw [ih _ hmTail hvTail, loading_word layout rom romFits ramFits i s hm k]
    by_cases head : i reset = 0 ∧ i valid = 1 ∧ i address = k
    · have accepted : Accepted i := ⟨hm, head.1, head.2.1⟩
      have hv : i data = image k := (values i (by simp) accepted).trans (congrArg image head.2.2)
      have cover : ∃ j : Values (Input aw), (@j) ∈ (@i) :: rest ∧ Accepted j ∧ j address = k :=
        ⟨@i, List.mem_cons_self, accepted, head.2.2⟩
      simp only [if_pos cover, if_pos head, hv, ite_self]
    · have noHead : ¬(Accepted i ∧ i address = k) := fun h => head ⟨h.1.2.1, h.1.2.2, h.2⟩
      rw [if_neg head]
      simp only [List.mem_cons, exists_eq_or_imp, noHead, false_or]
      done

theorem loading_view_words (i : Values (Input aw)) (s : Values (Register aw)) (hm : i mode = 1) :
    SystemCircuit.view ((circuit layout rom romFits ramFits).step i s) =
      SystemModel.initial (fun k => (circuit layout rom romFits ramFits).step i s (word k)) (s q) := by
  refine (loading_view layout rom romFits ramFits i s hm).trans ?_
  apply congrArg (fun contents => SystemModel.initial contents (s q))
  funext k
  exact (loading_word layout rom romFits ramFits i s hm k).symm

theorem run_loading_view (s : Values (Register aw)) (traffic : List (Values (Input aw)))
    (nonempty : traffic ≠ []) (modeHeld : ∀ i ∈ traffic, i mode = 1) :
    SystemCircuit.view ((circuit layout rom romFits ramFits).component.run s traffic) =
      SystemModel.initial
        (fun k => ((circuit layout rom romFits ramFits).component.run s traffic) (word k)) (s q) := by
  induction traffic generalizing s with
  | nil => exact False.elim (nonempty rfl)
  | cons i rest ih =>
    have hm := modeHeld i (by simp)
    have hmTail : ∀ j ∈ rest, j mode = 1 := fun j hj => modeHeld j (by simp [hj])
    by_cases empty : rest = []
    · subst rest
      exact loading_view_words layout rom romFits ramFits i s hm
    · change SystemCircuit.view ((circuit layout rom romFits ramFits).component.run
        ((circuit layout rom romFits ramFits).step i s) rest) = _
      rw [ih _ empty hmTail, loading_q layout rom romFits ramFits i s hm]
      rfl

theorem covers_nonempty (traffic : List (Values (Input aw))) (coverage : Covers traffic) : traffic ≠ [] := by
  intro empty
  obtain ⟨i, member, _⟩ := coverage 0
  simp [empty] at member

/-- Complete accepted coverage establishes exactly the supplied image before
loader release, from arbitrary RAM contents, Q, metadata and controller bits.
The old Q remains arbitrary; core/MMIO/fetch and pending ownership are reset. -/
theorem complete_image (s : Values (Register aw)) (traffic : List (Values (Input aw)))
    (modeHeld : ∀ i ∈ traffic, i mode = 1) (image : BitVec aw → BitVec 32)
    (values : ImageWrites image traffic) (coverage : Covers traffic) :
    SystemCircuit.view ((circuit layout rom romFits ramFits).component.run s traffic) =
      SystemModel.initial image (s q) := by
  rw [run_loading_view layout rom romFits ramFits s traffic (covers_nonempty traffic coverage) modeHeld]
  apply congrArg (fun contents => SystemModel.initial contents (s q))
  funext k
  rw [run_word_image layout rom romFits ramFits s traffic modeHeld image values k]
  exact if_pos (coverage k)

theorem accepted_word (i : Values (Input aw)) (s : Values (Register aw)) (ha : Accepted i) :
    (circuit layout rom romFits ramFits).step i s (word (i address)) = i data := by
  rw [loading_word layout rom romFits ramFits i s ha.1]
  exact if_pos ⟨ha.2.1, ha.2.2, rfl⟩

theorem accepted_iff_ready (i : Values (Input aw)) (s : Values (Register aw)) :
    Accepted i ↔
      (circuit layout rom romFits ramFits).observe i s (.right (.at ⟨0, by decide⟩)) = 1 ∧ i valid = 1 := by
  rcases BitVec.eq_zero_or_eq_one (i mode) with hm | hm
  all_goals rcases BitVec.eq_zero_or_eq_one (i reset) with hr | hr
  all_goals simp [Accepted, Circuit.observe, circuit, Expr.eval, hm, hr]

theorem external_word (i : Values (Input aw)) (s : Values (Register aw)) (hr : i reset = 1) (k : BitVec aw) :
    (circuit layout rom romFits ramFits).step i s (word k) = s (word k) := by
  have projection := congrFun (congrFun (loader_ram_step layout rom romFits ramFits i s) 32) (.left (CommandFlops.word k))
  refine projection.trans ?_
  rw [ByteAdapterLoader.word_step]
  have base := ByteAdapterCircuit.reset_memory _ (SystemCircuit.ramValues s)
    (ByteAdapterLoader.external_resets (resolvedLoaderPins layout ramFits i s) hr) (CommandFlops.word k)
  have resetEq : resolvedLoaderPins layout ramFits i s ByteAdapterLoader.reset = 1 := hr
  simp only [resetEq, show (1 : BitVec 1) ≠ 0 by decide, false_and, and_false, ↓reduceIte]
  exact base

theorem external_q (i : Values (Input aw)) (s : Values (Register aw)) (hr : i reset = 1) :
    (circuit layout rom romFits ramFits).step i s q = s q := by
  have projection := congrFun (congrFun (loader_ram_step layout rom romFits ramFits i s) 32) (.left CommandFlops.q)
  exact projection.trans ((ByteAdapterLoader.q_step _ _).trans
    (ByteAdapterCircuit.reset_memory _ _ (ByteAdapterLoader.external_resets _ hr) CommandFlops.q))

theorem external_metadata (i : Values (Input aw)) (s : Values (Register aw)) (hr : i reset = 1)
    (r : ByteAdapterCircuit.Metadata aw b) (hk : ((ByteAdapterCircuit.metadataPorts aw).interface.position r).val ≠ 6) :
    (circuit layout rom romFits ramFits).step i s (SystemCircuit.ram (.right r)) = s (SystemCircuit.ram (.right r)) := by
  have projection := congrFun (congrFun (loader_ram_step layout rom romFits ramFits i s) b) (.right r)
  exact projection.trans ((ByteAdapterLoader.metadata_step _ _ r).trans
    (ByteAdapterCircuit.reset_metadata _ _ (ByteAdapterLoader.external_resets _ hr) r hk))

theorem external_pending (i : Values (Input aw)) (s : Values (Register aw)) (hr : i reset = 1) :
    (circuit layout rom romFits ramFits).step i s (SystemCircuit.ram ByteAdapterCircuit.pending) = 0 := by
  have projection := congrFun (congrFun (loader_ram_step layout rom romFits ramFits i s) 1) ByteAdapterCircuit.pending
  exact projection.trans ((ByteAdapterLoader.metadata_step _ _ ByteAdapterCircuit.metaPending).trans
    (ByteAdapterCircuit.reset_pending _ _ (ByteAdapterLoader.external_resets _ hr)))

theorem run_core_zero (s : Values (Register aw)) (traffic : List (Values (Input aw)))
    (nonempty : traffic ≠ []) (modeHeld : ∀ i ∈ traffic, i mode = 1) (r : CoreCircuit.Register b) :
    ((circuit layout rom romFits ramFits).component.run s traffic) (SystemCircuit.core r) = 0 := by
  induction traffic generalizing s with
  | nil => exact False.elim (nonempty rfl)
  | cons i rest ih =>
    by_cases empty : rest = []
    · subst rest
      exact loading_core layout rom romFits ramFits i s (modeHeld i (by simp)) r
    · exact ih _ empty (fun j hj => modeHeld j (by simp [hj]))

theorem run_loading_valid (s : Values (Register aw)) (traffic : List (Values (Input aw)))
    (nonempty : traffic ≠ []) (modeHeld : ∀ i ∈ traffic, i mode = 1) :
    SystemCircuit.Valid layout rom ((circuit layout rom romFits ramFits).component.run s traffic) := by
  constructor
  · have coreZero : @Eq (Values CoreCircuit.Register)
        (SystemCircuit.coreValues ((circuit layout rom romFits ramFits).component.run s traffic)) CoreCircuit.zeroValues := by
      funext b r
      exact run_core_zero layout rom romFits ramFits s traffic nonempty modeHeld r
    rw [coreZero]
    exact CoreCircuit.zero_valid
  · rw [run_loading_view layout rom romFits ramFits s traffic nonempty modeHeld]
    exact SystemModel.initial_valid _ _ _ _

/-- Inactive request metadata is retained across the entire loading history,
including external reset edges. Its contents are irrelevant once pending clears. -/
theorem run_metadata (s : Values (Register aw)) (traffic : List (Values (Input aw)))
    (modeHeld : ∀ i ∈ traffic, i mode = 1)
    (r : ByteAdapterCircuit.Metadata aw b)
    (hk : ((ByteAdapterCircuit.metadataPorts aw).interface.position r).val ≠ 6) :
    ((circuit layout rom romFits ramFits).component.run s traffic) (SystemCircuit.ram (.right r)) =
      s (SystemCircuit.ram (.right r)) := by
  induction traffic generalizing s with
  | nil => rfl
  | cons i rest ih =>
    change ((circuit layout rom romFits ramFits).component.run
      ((circuit layout rom romFits ramFits).step i s) rest) (SystemCircuit.ram (.right r)) = _
    rw [ih _ (fun j hj => modeHeld j (by simp [hj]))]
    exact loading_metadata layout rom romFits ramFits i s (modeHeld i (by simp)) r hk

end Pinwheel.Hardware.Processor.LoadableSystem
