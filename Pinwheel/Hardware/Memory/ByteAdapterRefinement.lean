import Pinwheel.Hardware.Memory.ByteAdapterCircuitProofs
import Pinwheel.Hardware.Memory.ByteAdapterEffects

/-! Completion events read the actual response ports and the retained request
metadata. Atomic byte semantics require the owned-word snapshot invariant;
raw functional circuit correspondence itself does not. Event replay reconstructs
RAM contents, not the internal Q or inactive metadata. This is pure RAM, not MMIO.
-/
namespace Pinwheel.Hardware.Memory.ByteAdapterRefinement

open ByteAdapterInterface ByteAdapterCircuit Timed
set_option backward.isDefEq.respectTransparency false

/-- All four physical response encodings have an explicit interpretation. -/
def decodeResponse (code : BitVec 2) (data : BitVec 32) : ByteAdapterModel.Response :=
  if code = 0 then .read data else if code = 1 then .stored
  else if code = 2 then .fault .reservedSize else .fault .misaligned

@[simp] theorem decodeResponse_encode (response : ByteAdapterModel.Response) :
    decodeResponse (code response) (payload response) = response := by
  cases response with
  | read data => rfl
  | stored => rfl
  | fault fault => cases fault <;> rfl

/-- A pre-edge accepted response is counted once. The response is decoded from
the supplied hardware observation, never recomputed from a model expectation.
The actual retained request supplies identity fields absent from response ports.
-/
def extract (i : Values (Input a)) (r : Values (Register a)) (o : Values Output) :
    List (ByteAdapterEffects.Event a) :=
  if o responseValid = 1 ∧ i responseReady = 1 then
    [⟨storedRequest r, decodeResponse (o responseCode) (o responseData)⟩] else []

def events (i : Values (Input a)) (r : Values (Register a)) : List (ByteAdapterEffects.Event a) :=
  extract i r ((circuit a).observe i r)

theorem events_eq (i : Values (Input a)) (r : Values (Register a)) :
    events i r = ByteAdapterEffects.events (decode i) (view r) := by
  unfold events extract
  simp only [output_eq]
  rcases BitVec.eq_zero_or_eq_one (i reset) with hr | hr
  all_goals rcases BitVec.eq_zero_or_eq_one (r pending) with hp | hp
  all_goals rcases BitVec.eq_zero_or_eq_one (i responseReady) with hd | hd
  all_goals simp [ByteAdapterInterface.spec, outputValues, ByteAdapterModel.component,
    ByteAdapterModel.machine, Hardware.Stream.Machine.component, ByteAdapterModel.offer,
    ByteAdapterEffects.events, ByteAdapterModel.completedRequests, decode, view, responseValid, responseCode, responseData, hr, hp, hd]

/-- The logical adapter with physical pin decoding; no environment restriction
is needed for finite-prefix safety, including hostile offers and reset. -/
def pinRefinement (a : Nat) : EventRefinement (ByteAdapterInterface.spec a)
    (ByteAdapterEffects.atomic a) (fun i s => ByteAdapterEffects.events (decode i) s)
    (fun _ _ => True) where
  Rel s contents := ByteAdapterModel.Valid s ∧ s.memory.contents = contents
  edge i s contents h _ := by
    rcases h with ⟨hs, rfl⟩
    exact ⟨(ByteAdapterModel.step (decode i) s).memory.contents,
      ByteAdapterEffects.edge_path (decode i) s hs,
      ByteAdapterModel.valid_preserved (decode i) s hs, rfl⟩

def refinement (a : Nat) : EventRefinement (circuit a).component
    (ByteAdapterEffects.atomic a) events (fun _ _ => True) :=
  (pinRefinement a).ofLockstep (implementation a).refinement events (fun _ _ => True)
    (by intro i r s h; rcases h with ⟨_, rfl⟩; exact events_eq i r)
    (by intros; trivial)

theorem related_iff (r : Values (Register a)) (contents : Contents a 32) :
    (refinement a).Rel r contents ↔
      ByteAdapterModel.Valid (view r) ∧ (view r).memory.contents = contents := by
  simp [refinement, EventRefinement.ofLockstep, DecodedImplementation.refinement,
    implementation, pinRefinement]

theorem all_legal (r : Values (Register a)) (traffic : List (Values (Input a))) :
    (circuit a).component.Legal (fun _ _ => True) r traffic := by
  induction traffic generalizing r with
  | nil => trivial
  | cons i rest ih => exact ⟨trivial, ih _⟩

theorem trace_path (r : Values (Register a)) (valid : ByteAdapterModel.Valid (view r))
    (traffic : List (Values (Input a))) :
    (ByteAdapterEffects.atomic a).Path (view r).memory.contents
      ((circuit a).component.eventTrace events r traffic)
      (view ((circuit a).component.run r traffic)).memory.contents := by
  obtain ⟨last, path, related⟩ := (refinement a).trace r (view r).memory.contents traffic
    ((related_iff _ _).mpr ⟨valid, rfl⟩) (all_legal r traffic)
  exact ((related_iff _ _).mp related).2 ▸ path

theorem replay_trace (r : Values (Register a)) (valid : ByteAdapterModel.Valid (view r))
    (traffic : List (Values (Input a))) :
    ByteAdapterEffects.replay (view r).memory.contents
      ((circuit a).component.eventTrace events r traffic) =
      some (view ((circuit a).component.run r traffic)).memory.contents :=
  ByteAdapterEffects.replay_of_path (trace_path r valid traffic)

/-- Empty means only pending=0: all words, Q and inactive metadata are arbitrary. -/
def initial (r : Values (Register a)) : Prop := r pending = 0

theorem initial_valid (r : Values (Register a)) (h : initial r) : ByteAdapterModel.Valid (view r) := by
  simp [initial] at h
  simp [view, ByteAdapterModel.Valid, h]

/-- Construct an empty physical adapter for any memory image and any retained
metadata values. Only its pending bit is forced to zero. -/
def emptyRaw (memory : Sram.State a 32) (metadata : Values (Metadata a)) : Values (Register a)
  | _, .left r => CommandFlops.encode memory r
  | _, .right r => if ((metadataPorts a).interface.position r).val = 6 then 0 else metadata r

theorem emptyRaw_metadata (memory : Sram.State a 32) (metadata : Values (Metadata a))
    (r : Metadata a b) (h : ((metadataPorts a).interface.position r).val ≠ 6) :
    emptyRaw memory metadata (.right r) = metadata r := by simp [emptyRaw, h]

theorem view_emptyRaw (memory : Sram.State a 32) (metadata : Values (Metadata a)) :
    view (emptyRaw memory metadata) = ⟨memory, none⟩ := by
  change ByteAdapterModel.State.mk (CommandFlops.view (CommandFlops.encode memory)) none = _
  rw [CommandFlops.view_encode]

theorem every_memory_image (memory : Sram.State a 32) (metadata : Values (Metadata a)) :
    initial (emptyRaw memory metadata) ∧
      (refinement a).Rel (emptyRaw memory metadata) memory.contents := by
  constructor
  · rfl
  · rw [related_iff, view_emptyRaw]
    simp [ByteAdapterModel.Valid]

theorem coverage (a : Nat) : (refinement a).InitialCoverage initial (fun _ => True) where
  nonempty := ⟨emptyRaw ⟨fun _ => 0, 0⟩ (fun _ => 0), rfl⟩
  covered r h := ⟨(view r).memory.contents, trivial, (related_iff _ _).mpr ⟨initial_valid r h, rfl⟩⟩

theorem reset_events (i : Values (Input a)) (r : Values (Register a)) (hr : i reset = 1) :
    events i r = [] := by
  rw [events_eq]
  simp [ByteAdapterEffects.events, ByteAdapterModel.completedRequests, decode, hr]

theorem reset_trace (i : Values (Input a)) (r : Values (Register a)) (hr : i reset = 1)
    (traffic : List (Values (Input a))) :
    (ByteAdapterEffects.atomic a).Path (view r).memory.contents
      ((circuit a).component.eventTrace events ((circuit a).step i r) traffic)
      (view ((circuit a).component.run ((circuit a).step i r) traffic)).memory.contents := by
  have hv : ByteAdapterModel.Valid (view ((circuit a).step i r)) := by
    rw [reset_view i r hr]
    exact ByteAdapterModel.reset_valid _
  simpa only [reset_view i r hr, ByteAdapterModel.resetState] using
    trace_path ((circuit a).step i r) hv traffic

theorem replay_after_reset (i : Values (Input a)) (r : Values (Register a)) (hr : i reset = 1)
    (traffic : List (Values (Input a))) :
    ByteAdapterEffects.replay (view r).memory.contents
      ((circuit a).component.eventTrace events ((circuit a).step i r) traffic) =
      some (view ((circuit a).component.run ((circuit a).step i r) traffic)).memory.contents :=
  ByteAdapterEffects.replay_of_path (reset_trace i r hr traffic)

/-- Conditional one-edge progress. Readiness and absence of reset are explicit;
the result is the actual decoded response, and pending clears after the edge. -/
theorem completion (i : Values (Input a)) (r : Values (Register a))
    (hr : i reset = 0) (hd : i responseReady = 1) (hp : r pending = 1) :
    events i r = [⟨storedRequest r, decodeResponse ((circuit a).observe i r responseCode)
      ((circuit a).observe i r responseData)⟩] ∧ (circuit a).step i r pending = 0 := by
  constructor
  · simp [events, extract, Circuit.observe, circuit, responseValid, responseValidExpr, Expr.eval, hr, hp, hd]
  · rw [pending_step]; simp [hr, hp, hd]

variable {rtl : Timed.Component (Values (Input a)) (Values (Register a)) (Values Output)}

/-- Uses the imported component's actual outputs and actual retained registers.
Nothing is asserted until the caller supplies complete artifact correspondence. -/
def artifactEvents (rtl : Timed.Component (Values (Input a)) (Values (Register a)) (Values Output))
    (i : Values (Input a)) (r : Values (Register a)) : List (ByteAdapterEffects.Event a) :=
  extract i r (rtl.observe i r)

theorem artifact_events_eq (proof : Artifact.Correspondence (circuit a) rtl)
    (i : Values (Input a)) (r : Values (Register a)) : artifactEvents rtl i r = events i r := by
  simp only [artifactEvents, events, proof.output_eq]

def artifactRefinement (proof : Artifact.Correspondence (circuit a) rtl) :
    EventRefinement rtl (ByteAdapterEffects.atomic a) (artifactEvents rtl) (fun _ _ => True) :=
  (refinement a).ofLockstep proof.refinement (artifactEvents rtl) (fun _ _ => True)
    (by intro i r s h; cases h; exact artifact_events_eq proof i r)
    (by intros; trivial)

theorem artifact_related_iff (proof : Artifact.Correspondence (circuit a) rtl)
    (r : Values (Register a)) (contents : Contents a 32) :
    (artifactRefinement proof).Rel r contents ↔
      ByteAdapterModel.Valid (view r) ∧ (view r).memory.contents = contents := by
  simp only [artifactRefinement, EventRefinement.ofLockstep, Artifact.Correspondence.refinement]
  constructor
  · rintro ⟨s, rfl, h⟩
    exact (related_iff _ _).mp h
  · intro h
    exact ⟨r, rfl, (related_iff _ _).mpr h⟩

theorem artifact_coverage (proof : Artifact.Correspondence (circuit a) rtl) :
    (artifactRefinement proof).InitialCoverage initial (fun _ => True) where
  nonempty := (coverage a).nonempty
  covered r h := ⟨(view r).memory.contents, trivial,
    (artifact_related_iff proof _ _).mpr ⟨initial_valid r h, rfl⟩⟩

theorem artifact_reset_events (proof : Artifact.Correspondence (circuit a) rtl)
    (i : Values (Input a)) (r : Values (Register a)) (hr : i reset = 1) :
    artifactEvents rtl i r = [] := by rw [artifact_events_eq proof]; exact reset_events i r hr

theorem artifact_eventTrace (proof : Artifact.Correspondence (circuit a) rtl)
    (r : Values (Register a)) (traffic : List (Values (Input a))) :
    rtl.eventTrace (artifactEvents rtl) r traffic = (circuit a).component.eventTrace events r traffic := by
  induction traffic generalizing r with
  | nil => rfl
  | cons i rest ih =>
    simp only [Component.eventTrace, artifact_events_eq proof, proof.step_eq, ih]
    rfl

theorem artifact_trace_path (proof : Artifact.Correspondence (circuit a) rtl)
    (r : Values (Register a)) (valid : ByteAdapterModel.Valid (view r))
    (traffic : List (Values (Input a))) :
    (ByteAdapterEffects.atomic a).Path (view r).memory.contents
      (rtl.eventTrace (artifactEvents rtl) r traffic) (view (rtl.run r traffic)).memory.contents := by
  rw [artifact_eventTrace proof, proof.run_eq]
  exact trace_path r valid traffic

theorem artifact_replay_trace (proof : Artifact.Correspondence (circuit a) rtl)
    (r : Values (Register a)) (valid : ByteAdapterModel.Valid (view r))
    (traffic : List (Values (Input a))) :
    ByteAdapterEffects.replay (view r).memory.contents (rtl.eventTrace (artifactEvents rtl) r traffic) =
      some (view (rtl.run r traffic)).memory.contents :=
  ByteAdapterEffects.replay_of_path (artifact_trace_path proof r valid traffic)

/-- Reset establishes event safety for every raw imported state. Earlier stores
remain in the starting image, while the discarded transaction emits no event. -/
theorem artifact_reset_trace (proof : Artifact.Correspondence (circuit a) rtl)
    (i : Values (Input a)) (r : Values (Register a)) (hr : i reset = 1)
    (traffic : List (Values (Input a))) :
    (ByteAdapterEffects.atomic a).Path (view r).memory.contents
      (rtl.eventTrace (artifactEvents rtl) (rtl.step i r) traffic)
      (view (rtl.run (rtl.step i r) traffic)).memory.contents := by
  rw [artifact_eventTrace proof, proof.run_eq, proof.step_eq]
  exact reset_trace i r hr traffic

theorem artifact_replay_after_reset (proof : Artifact.Correspondence (circuit a) rtl)
    (i : Values (Input a)) (r : Values (Register a)) (hr : i reset = 1)
    (traffic : List (Values (Input a))) :
    ByteAdapterEffects.replay (view r).memory.contents
      (rtl.eventTrace (artifactEvents rtl) (rtl.step i r) traffic) =
      some (view (rtl.run (rtl.step i r) traffic)).memory.contents :=
  ByteAdapterEffects.replay_of_path (artifact_reset_trace proof i r hr traffic)

end Pinwheel.Hardware.Memory.ByteAdapterRefinement
