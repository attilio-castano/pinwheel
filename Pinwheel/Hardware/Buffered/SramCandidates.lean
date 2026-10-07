import Pinwheel.Hardware.Buffered.Reactive
import Pinwheel.Hardware.Memory.Sram

/-! Two instruction addresses sufficient at a buffered reactive dispatch.

The pair is computed from the counted runtime state, with either Boolean branch
choice supplied explicitly. It does not predict the synchronized input or the
dispatch edge. A latency-one controller requests the prospective post-edge
state's pair and selects the already available response on the actual edge.

These laws cover addressing and the digital SRAM response contract. They do not
claim refinement of a particular controller, initialization of unwritten words,
or macro/address-path timing. -/
namespace Pinwheel.Hardware.Buffered.SramCandidates
open Pinwheel.Hardware
open Reactive

/-- Counted NEXT without START arbitration. Inner rollover takes precedence. -/
def sequential : E 7 :=
  .mux innerAgain (.concat (.lit (0 : BitVec 1)) (innerStart currentControl))
    (.mux outerAgain (.concat (.lit (0 : BitVec 1)) (outerStart currentControl))
      (increment (.reg .pc)))

/-- A forced branch choice, including the unconditional jump descriptor. -/
def selectedEndpoint (b : Bool) : E 24 :=
  .mux (.equal finish (.lit 1)) (.slice 6 24 (by decide) (.reg .cachedBranch))
    (if b then .slice 6 24 (by decide) (.reg .cachedBranch)
    else .slice 30 24 (by decide) (.reg .cachedBranch))

/-- Absolute CHECKED successor, or counted NEXT for every other case.
Endpoint bit zero is the terminal/halt tag, so it suppresses an absolute jump. -/
def candidate (b : Bool) : E 7 :=
  .mux (both (isPhase 3)
    (both (.inv (.zero finish)) (.inv (.slice 0 1 (by decide) (selectedEndpoint b)))))
    (.slice 11 7 (by decide) (selectedEndpoint b)) sequential

/-- Runtime choice between the two previously requested addresses. -/
def chosen : E 7 := .mux branchBit (candidate true) (candidate false)

private theorem band_one : ∀ a b : BitVec 1, a &&& b = 1 ↔ a = 1 ∧ b = 1 := by
  decide +kernel

private theorem either_one : ∀ a b : BitVec 1,
    ~~~(~~~a &&& ~~~b) = 1 ↔ a = 1 ∨ b = 1 := by
  decide +kernel

private theorem zero_ne_one : (0 : BitVec 1) ≠ 1 := by decide +kernel

private theorem band_zero_left : ∀ a : BitVec 1, 0 &&& a = 0 := by decide +kernel

private theorem band_zero_right : ∀ a : BitVec 1, a &&& 0 = 0 := by decide +kernel

private theorem inv_zero : ~~~(0 : BitVec 1) = 1 := by decide +kernel

private theorem band_ones : (1 : BitVec 1) &&& 1 = 1 := by decide +kernel

private theorem entering_dispatch (i : Values Input) (s : Values Register)
    (he : entering.eval i s = 1) (hs : starting.eval i s = 0) :
    dispatch.eval i s = 1 := by
  simp only [entering, both, either, Expr.eval, band_one, either_one, hs, zero_ne_one,
    false_or] at he
  exact he.2
  done

private theorem dispatch_terminal_phase (i : Values Input) (s : Values Register)
    (hd : dispatch.eval i s = 1) :
    terminalEdge.eval i s = (isPhase 3).eval i s := by
  by_cases hp : s .phase = 3
  all_goals simp only [dispatch, terminalEdge, isPhase, both, either, Expr.eval,
    hp, band_one, either_one, decide_true, decide_false, BitVec.ofBool_true,
    BitVec.ofBool_false, band_zero_left, zero_ne_one] at hd ⊢
  simp only [show (3 : BitVec 3) ≠ 1 from by decide +kernel,
    show (3 : BitVec 3) ≠ 2 from by decide +kernel,
    show (3 : BitVec 3) ≠ 4 from by decide +kernel,
    decide_false, BitVec.ofBool_false, zero_ne_one, false_and, false_or, true_and] at hd ⊢
  exact hd.resolve_right id
  done

theorem actual_entry_pc (i : Values Input) (s : Values Register)
    (he : entering.eval i s = 1) (hs : starting.eval i s = 0) :
    entryPC.eval i s = chosen.eval i s := by
  have ht := dispatch_terminal_phase i s (entering_dispatch i s he hs)
  by_cases hb : branchBit.eval i s = 1
  all_goals simp only [entryPC, sequentialPC, chosen, candidate, selectedEndpoint,
    endpoint, absoluteDispatch, sequential, both, Expr.eval, hs, hb, ht,
    zero_ne_one, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl
  done

/-- Accepted START comes from a free core, so CHECKED absolute dispatch cannot
override its row-zero address. -/
theorem start_entry_pc (i : Values Input) (s : Values Register)
    (hs : starting.eval i s = 1) : entryPC.eval i s = 0 := by
  simp only [entryPC, absoluteDispatch, terminalEdge, starting, free, busy, isPhase,
    sequentialPC, both, Expr.eval] at hs ⊢
  by_cases hp : s .phase = 3 <;> simp_all
  done

/-- Only six cached/counting fields influence the pair. Sampler stages,
scratch, buffers, dictionary contents and every other register may differ. -/
theorem candidate_register_congr (b : Bool) (i j : Values Input)
    (s t : Values Register)
    (hp : s .phase = t .phase) (ha : s .pc = t .pc)
    (hc : s .currentControl = t .currentControl)
    (ho : s .outer = t .outer) (hi : s .inner = t .inner)
    (hb : s .cachedBranch = t .cachedBranch) :
    (candidate b).eval i s = (candidate b).eval j t := by
  cases b <;> simp only [candidate, selectedEndpoint, sequential, isPhase, finish,
    innerAgain, outerAgain, currentControl, controlDepth, innerEnd, innerBound,
    outerEnd, outerBound, innerStart, outerStart, increment, both, Expr.eval,
    Bool.false_eq_true, ↓reduceIte, hp, ha, hc, ho, hi, hb]
  all_goals rfl
  done

/-- The Boolean selection is the same mux consumed by actual dispatch. -/
theorem chosen_candidate (i : Values Input) (s : Values Register) :
    chosen.eval i s =
      (candidate (decide (branchBit.eval i s = 1))).eval i s := by
  by_cases hb : branchBit.eval i s = 1 <;>
    simp only [chosen, Expr.eval, hb, decide_true, decide_false, ↓reduceIte]
  done

/-- A non-CHECKED phase has the same counted successor in both ports. -/
theorem candidate_nonchecked (b : Bool) (i : Values Input) (s : Values Register)
    (hp : s .phase ≠ 3) : (candidate b).eval i s = sequential.eval i s := by
  simp only [candidate, isPhase, both, Expr.eval, hp, decide_false,
    BitVec.ofBool_false]
  simp only [band_zero_left, zero_ne_one, ↓reduceIte]
  done

/-- A NEXT descriptor has the same counted successor even in CHECKED phase. -/
theorem candidate_next (b : Bool) (i : Values Input) (s : Values Register)
    (hf : finish.eval i s = 0) : (candidate b).eval i s = sequential.eval i s := by
  simp [candidate, both, Expr.eval, hf]
  done

/-- Endpoint terminal/halt tags suppress the absolute jump, just as the
reference's `absoluteDispatch` does. The actual core later checks its bounds. -/
theorem candidate_terminal (b : Bool) (i : Values Input) (s : Values Register)
    (ht : ((selectedEndpoint b).eval i s).extractLsb' 0 1 = 1) :
    (candidate b).eval i s = sequential.eval i s := by
  simp [candidate, both, Expr.eval, ht]
  done

/-- A live absolute endpoint restores its physical row directly. -/
theorem candidate_absolute (b : Bool) (i : Values Input) (s : Values Register)
    (hp : s .phase = 3) (hf : finish.eval i s ≠ 0)
    (ht : ((selectedEndpoint b).eval i s).extractLsb' 0 1 = 0) :
    (candidate b).eval i s = ((selectedEndpoint b).eval i s).extractLsb' 11 7 := by
  simp only [candidate, isPhase, both, Expr.eval, hp, hf, ht, decide_true, decide_false,
    BitVec.ofBool_true, BitVec.ofBool_false]
  simp only [inv_zero, band_ones, ↓reduceIte]
  done

/-- The candidate pair never samples command or pin inputs. -/
theorem candidate_input_independent (b : Bool) (i j : Values Input)
    (s : Values Register) : (candidate b).eval i s = (candidate b).eval j s :=
  candidate_register_congr b i j s s rfl rfl rfl rfl rfl rfl

/-- The inner loop restarts before considering an outer restart. -/
theorem sequential_inner (i : Values Input) (s : Values Register)
    (hi : innerAgain.eval i s = 1) :
    sequential.eval i s = (0 : BitVec 1) ++ (innerStart currentControl).eval i s := by
  simp only [sequential, Expr.eval, hi, ↓reduceIte]
  done

/-- After the inner loop exhausts, an outer restart selects its start row. -/
theorem sequential_outer (i : Values Input) (s : Values Register)
    (hi : innerAgain.eval i s = 0) (ho : outerAgain.eval i s = 1) :
    sequential.eval i s = (0 : BitVec 1) ++ (outerStart currentControl).eval i s := by
  simp only [sequential, Expr.eval, hi, ho]
  simp only [zero_ne_one, ↓reduceIte]
  done

/-- Exhausted/nonending counted loops advance the physical row once. -/
theorem sequential_next (i : Values Input) (s : Values Register)
    (hi : innerAgain.eval i s = 0) (ho : outerAgain.eval i s = 0) :
    sequential.eval i s = s .pc - 127 := by
  simp only [sequential, increment, Expr.eval, hi, ho]
  simp only [zero_ne_one, ↓reduceIte]
  rfl
  done

section Availability

/-- Two independent reads; an accepted upload instead occupies both replicas'
single ports with the same full-word write. -/
def readRequest (addresses : Fin 2 → BitVec a) : Memory.Request a w 2 :=
  ⟨⟨false, 0, 0⟩, addresses⟩

/-- A count/tail projection must happen before instruction decoding. `live`
lets the law apply to any bounded resident image, without assuming zero SRAM. -/
def project (live : Bool) (word : BitVec w) : BitVec w := if live then word else 0

def Ready (arrays : Fin 2 → Memory.Sram.State a w) (contents : Memory.Contents a w)
    (live : BitVec a → Bool) (addresses : Fin 2 → BitVec a) : Prop :=
  ∀ port, project (live (addresses port)) (arrays port).q =
    project (live (addresses port)) (contents (addresses port))

/-- The response produced on a read edge is exactly the pre-edge requested
word. Current Q and future requests play no part in this equality. -/
theorem response_edge (arrays : Fin 2 → Memory.Sram.State a w)
    (addresses : Fin 2 → BitVec a) (port : Fin 2) :
    (Memory.Sram.step (readRequest addresses) arrays port).q =
      (arrays port).contents (addresses port) := rfl

/-- Reading prospective post-edge candidates renews availability on that same
edge. Only resident/live words need initialized-bank equality; stale padded
words are hidden by projection. No prior Q availability is assumed here. -/
theorem availability_renewed (arrays : Fin 2 → Memory.Sram.State a w)
    (contents : Memory.Contents a w) (live : BitVec a → Bool)
    (postCandidates : Fin 2 → BitVec a)
    (hbank : ∀ port k, live k = true → (arrays port).contents k = contents k) :
    Ready (Memory.Sram.step (readRequest postCandidates) arrays)
      contents live postCandidates := by
  intro port
  cases hl : live (postCandidates port) <;>
    simp [project, response_edge, hl, hbank port (postCandidates port)]
  done

/-- Candidate reads do not mutate the resident image in either replica. -/
theorem read_preserves_bank (arrays : Fin 2 → Memory.Sram.State a w)
    (addresses : Fin 2 → BitVec a) (port : Fin 2) :
    (Memory.Sram.step (readRequest addresses) arrays port).contents =
      (arrays port).contents :=
  Memory.write_disabled (arrays port).contents (readRequest addresses).write rfl

/-- The same request initializes its addressed word in every replica. Q is
held on this edge, so execution must not need a fresh response during upload. -/
theorem accepted_write_broadcast (arrays : Fin 2 → Memory.Sram.State a w)
    (request : Memory.Request a w 2) (hw : request.write.enable = true)
    (port : Fin 2) :
    (Memory.Sram.step request arrays port).contents request.write.address =
      request.write.data :=
  Memory.Sram.broadcast_write request arrays hw port

/-- Upload writes hold the previous macro response. -/
theorem accepted_write_holds_q (arrays : Fin 2 → Memory.Sram.State a w)
    (request : Memory.Request a w 2) (hw : request.write.enable = true)
    (port : Fin 2) : (Memory.Sram.step request arrays port).q = (arrays port).q := by
  simp [Memory.Sram.step, Memory.Sram.State.step, hw]
  done

/-- Established partial-memory words suffice for availability. Unwritten
physical cells, including disagreement between replicas, remain unconstrained. -/
theorem initialized_availability (arrays : Fin 2 → Memory.Sram.State a w)
    (model : Memory.Sram.Model a w 2) (h : Memory.Sram.Related arrays model)
    (contents : Memory.Contents a w) (live : BitVec a → Bool)
    (postCandidates : Fin 2 → BitVec a)
    (hknown : ∀ k, live k = true → model.contents k = some (contents k)) :
    Ready (Memory.Sram.step (readRequest postCandidates) arrays)
      contents live postCandidates :=
  availability_renewed arrays contents live postCandidates
    (fun port k hl => (h port).1 k (contents k) (hknown k hl))

/-- Starting from unrelated arbitrary arrays/Q, the established-word relation
holds after every finite actual request history, including partial uploads. -/
theorem independent_initial_history (arrays : Fin 2 → Memory.Sram.State a w)
    (requests : List (Memory.Request a w 2)) :
    Memory.Sram.Related
      (requests.foldl (fun arrays request => Memory.Sram.step request arrays) arrays)
      (requests.foldl Memory.Sram.Model.step Memory.Sram.Model.initial) :=
  Memory.Sram.related_run requests arrays Memory.Sram.Model.initial
    (Memory.Sram.related_initial arrays)

end Availability

end Pinwheel.Hardware.Buffered.SramCandidates
