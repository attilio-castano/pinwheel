import Pinwheel.Hardware.StreamingReady.RegisteredStore
import Pinwheel.Hardware.StreamingReady.SegmentPackage
import Pinwheel.Hardware.StreamingReady.ProtocolOwnership

/-! Recover the existing Ready session semantics while executing the older
    instruction set on the segmented hardware. -/
namespace Pinwheel.Hardware.StreamingReady.SegmentLegacy

open Pinwheel.Hardware SegmentCore
open Pinwheel.Program.StreamingReady (Compiled Phase)

private def selected (registered : Bool) (i : Values Core.Input) (s : Values (Register a)) :
    Values (Register a) := withFetch s ((word registered).eval i s)

private def cacheView (s : Values (Register a)) : Values (RegisteredStore.Register a)
  | _, .base r => s (.base r)
  | _, .fetched => s .fetched

private theorem selected_coherent (registered : Bool) (i : Values Core.Input)
    (s : Values (Register a)) (coherent : registered = true → SegmentStore.Coherent s) :
    RegisteredStore.Related (cacheView (selected registered i s)) := by
  simp only [RegisteredStore.Related, Core.entryWord, Execution.readTree_correct, Expr.eval]
  change (word registered).eval i s = s (.base (.word ((s (.base .pc)).extractLsb' 0 6)))
  cases registered with
  | false =>
    simp only [word, Bool.false_eq_true, if_false, lift, Expr.eval_bind, Core.entryWord,
      Execution.readTree_correct, Expr.eval]
  | true => exact coherent rfl

private theorem inputs_unmasked (i : Values Core.Input) (s : Values (Register a))
    (enabled : denyTX.eval i s = 0#1) : (fun {w} (port : Core.Input w) => (runtimeInput port).eval i s) = @i := by
  funext w port
  cases port <;> first | rfl | simp [runtimeInput, both, Expr.eval, enabled]
  have one (x : BitVec 1) : 1#1 &&& x = x := by decide +revert +kernel
  exact one _

private def cacheLeaf (decoded : Bool) {w : Nat} :
    Core.Register a w → RegisteredStore.E a w :=
  if decoded then fun
    | .word _ => .reg .fetched
    | reg => .reg (.base reg)
  else fun reg => .reg (.base reg)

private theorem cache_next (r : Core.Register a w) : (RegisteredStore.circuit a).next (.base r) =
    (Core.next r).bind .input (cacheLeaf (usesEntryWord r)) := by
  cases r <;> rfl

private theorem ordinary_next (i : Values Core.Input) (s : Values (Register a)) (r : Core.Register a w)
    (enabled : denyTX.eval i s = 0#1) :
    (originalNext r).eval i s = ((RegisteredStore.circuit a).next (.base r)).eval i (cacheView s) := by
  rw [originalNext, cache_next, Expr.eval_bind, Expr.eval_bind, inputs_unmasked i s enabled]
  congr 1
  funext w p
  by_cases decoded : usesEntryWord r = true <;> cases p <;>
    simp [cacheLeaf, decodedRegister, decoded, Expr.eval, cacheView]

private structure Inactive (i : Values Core.Input) (s : Values (Register a)) : Prop where
  setCount : setCount.eval i s = 0#1
  branch : branch.eval i s = 0#1
  discard : SegmentCore.discard.eval i s = 0#1
  txClosed : s .txClosed = 0#1

private theorem inactive (i : Values Core.Input) (s : Values (Register a))
    (closed : s .txClosed = 0#1)
    (legacy : fetching.eval i s = 0#1 ∨ (kind.eval i s).toNat ≤ 4) : Inactive i s := by
  rcases legacy with stopped | old
  · exact ⟨by simp [setCount, both, Expr.eval, stopped], by simp [branch, both, Expr.eval, stopped],
      by simp [SegmentCore.discard, both, Expr.eval, stopped], closed⟩
  · have notCount : kind.eval i s ≠ 5#3 := by
      intro bad
      rw [bad] at old
      contradiction
    have notBranch : kind.eval i s ≠ 6#3 := by
      intro bad
      rw [bad] at old
      contradiction
    have notDiscard : s .fetched ≠ 7#64 := by
      intro bad
      change ((s .fetched).extractLsb' 0 3).toNat ≤ 4 at old
      rw [bad] at old
      contradiction
    exact ⟨by simp [setCount, both, Expr.eval, notCount], by simp [branch, both, Expr.eval, notBranch],
      by simp [SegmentCore.discard, both, Expr.eval, notDiscard], closed⟩

private theorem Inactive.control_off (h : Inactive i s) : SegmentCore.control.eval i s = 0#1 := by
  simp [SegmentCore.control, either, Expr.eval, h.setCount, h.branch]

private theorem Inactive.accepts_tx (h : Inactive i s) : denyTX.eval i s = 0#1 := by
  simp [denyTX, either, Expr.eval, h.discard, h.txClosed]

/-- The only instruction-dependent premise concerns the reached fetch.
    Old rows beyond the installed length cannot activate segmented control. -/
def Edge (registered : Bool) (i : Values Core.Input) (s : Values (Register a)) : Prop :=
  let state : Values (Register a) := selected registered i s
  fetching.eval i state = 0#1 ∨ (kind.eval i state).toNat ≤ 4

theorem edge_of_not_fetch (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (phase : s (.base .phase) ≠ 1#3) : Edge registered i s := by
  left
  simp [fetching, both, lift, Expr.eval_bind, Core.fetching, Core.both, Core.isPhase, Expr.eval,
    selected, withFetch, phase]

theorem core_step (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (closed : s .txClosed = 0#1) (legacy : Edge registered i s)
    (coherent : registered = true → SegmentStore.Coherent s) :
    let after : Values (Register a) := (circuit a registered).step i s
    @project a after = @Circuit.step _ _ _ (Core.circuit a) i (project s) ∧ after .txClosed = 0#1 := by
  dsimp only
  let state : Values (Register a) := selected registered i s
  have quiet := inactive i state closed legacy
  have cached := RegisteredStore.project_step i (cacheView state) (selected_coherent registered i s coherent)
  refine ⟨?_, ?_⟩
  · funext w r
    have evaluated := congrArg (fun registers : Values (Core.Register a) => registers r) cached
    change (bindWord (word registered) (nextBase r)).eval i s = _
    rw [bindWord_eval]
    have stripped : (nextBase r).eval i state = (originalNext r).eval i state := by
      cases r <;> simp [nextBase, Expr.eval, quiet.discard, quiet.setCount, quiet.branch, quiet.control_off]
    exact stripped.trans ((ordinary_next i state r quiet.accepts_tx).trans evaluated)
  · change (bindWord (word registered) (next .txClosed)).eval i s = _
    rw [bindWord_eval]
    change (next .txClosed).eval i state = _
    simp [next, Expr.eval, either, quiet.discard, quiet.txClosed]

theorem core_observe (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (closed : s .txClosed = 0#1) (legacy : Edge registered i s) :
    @Circuit.observe _ _ _ (circuit a registered) i s = @Circuit.observe _ _ _ (Core.circuit a) i (project s) := by
  funext w port
  let state : Values (Register a) := selected registered i s
  have quiet := inactive i state closed legacy
  change (bindWord (word registered) (output port)).eval i s = _
  rw [bindWord_eval]
  change (output port).eval i state = (Core.output port).eval i (project s)
  have lift_eval (expr : Core.E a w) : (lift expr).eval i state = expr.eval i (project s) :=
    Expr.eval_bind .input _ expr i state
  cases port <;> first | exact lift_eval _ | skip
  simp [output, either, both, Expr.eval, quiet.accepts_tx, lift_eval]
  have identity (x : BitVec 1) : ~~~(~~~x &&& 1#1) = x := by decide +revert +kernel
  exact identity _

theorem package_step (registered : Bool) (s : SegmentPackage.State a) (pins : Package.Pins)
    (openTX : s.core .txClosed = 0#1) (legacy : Edge registered (s.coreInputs pins) s.core)
    (coherent : registered = true → SegmentStore.Coherent s.core) :
    let after := s.step registered pins
    after.project = s.project.step (Package.Components.typed a) pins ∧
      after.core .txClosed = 0#1 ∧ (registered = true → SegmentStore.Coherent after.core) := by
  have evidence := core_step registered (s.coreInputs pins) s.core openTX legacy coherent
  have outputs := core_observe registered (s.coreInputs pins) s.core openTX legacy
  refine ⟨?_, evidence.2, ?_⟩
  · unfold SegmentPackage.State.step SegmentPackage.State.project SegmentPackage.State.status
    change Streaming.Package.State.mk _ (project ((circuit a registered).step (s.coreInputs pins) s.core)) = _
    rw [evidence.1, outputs]
    rfl
  · intro selected
    subst registered
    exact SegmentStore.coherent_after_edge _ _

/-- Every executed fetch in this portion of a session uses the original
    Ready instruction set. Loading and runtime edges can be interleaved. -/
def Trace (registered : Bool) (state : SegmentPackage.State a) : List Package.Pins → Prop
  | [] => True
  | pins :: rest => Edge registered (state.coreInputs pins) state.core ∧
      Trace registered (state.step registered pins) rest

/-- Legacy protocol session proofs apply to the projected state of the
    shared segmented package on a history with no active extended opcode. -/
theorem package_run (registered : Bool) (s : SegmentPackage.State a) (pins : List Package.Pins)
    (openTX : s.core .txClosed = 0#1) (coherent : registered = true → SegmentStore.Coherent s.core)
    (legacy : Trace registered s pins) :
    (pins.foldl (SegmentPackage.State.step registered) s).project =
      s.project.run (Package.Components.typed a) pins := by
  induction pins generalizing s with
  | nil => rfl
  | cons nextPins rest ih =>
    have edge := package_step registered s nextPins openTX legacy.1 coherent
    change (rest.foldl (SegmentPackage.State.step registered) (s.step registered nextPins)).project =
      (s.project.step (Package.Components.typed a) nextPins).run (Package.Components.typed a) rest
    rw [ih (s.step registered nextPins) edge.2.1 edge.2.2 legacy.2, edge.1]

/-- Close a reached fixed-length session, such as SPI, on the very same
    package that runs the extended I²C program. At the completed cut no
    extended fetch can interfere with the original ownership proof. -/
theorem release_fixed {rows : List Pinwheel.Program.StreamingReady.Instruction} {idle}
    {image : Compiled rows idle} {rep : SourceRefinement.Image image.program}
    {source : Pinwheel.Program.StreamingReady.Session.State a} {trace}
    (registered : Bool) (actual : SegmentPackage.State a)
    (reached : InitializedCustody.Reached image actual.project source trace rep)
    (pin : Pinwheel.Program.StreamingReady.Session.Pins) (ha : a ≤ 3)
    (runtime : Pinwheel.Program.StreamingReady.Session.RuntimeInput source pin)
    (admitted : InitializedCustody.ActualRelease actual.project pin)
    (completed : source.core.phase = .completed) (openTX : actual.core .txClosed = 0#1)
    (coherent : registered = true → SegmentStore.Coherent actual.core) :
    let after := source.step image.program false pin
    (ProtocolOwnership.fixedReport source after).Valid ∧
      (actual.step registered (SessionCorrespondence.pins pin)).project = SessionCorrespondence.values rep after := by
  have observed := congrArg (fun s : Package.State a => s.core .phase) reached.package
  change actual.core (.base .phase) = source.core.phase.code at observed
  have noFetch : actual.core (.base .phase) ≠ 1#3 := by
    rw [observed, completed]
    decide
  let pins := SessionCorrespondence.pins pin
  have legacy := edge_of_not_fetch registered (actual.coreInputs pins) actual.core noFetch
  have transition := package_step registered actual pins openTX legacy coherent
  have ready := SessionProof.release_to_free reached pin ha runtime admitted
  have fixed := ProtocolOwnership.fixed_release reached pin ha runtime admitted completed
  exact ⟨fixed.1, transition.1.trans ready.package⟩

end Pinwheel.Hardware.StreamingReady.SegmentLegacy
