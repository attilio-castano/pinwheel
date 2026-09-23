import Pinwheel.Hardware.Storage.SramController

/-! Initialization coverage for the hybrid SRAM controller. The loader's
accepted cursor establishes every dictionary word before commit; neither reset
nor a partial upload is assumed to clear either physical memory copy. -/
namespace Pinwheel.Hardware.Storage.SramCoverage
open Pinwheel.Hardware Loader

abbrev Model := Memory.Sram.Model 6 64 2

/-- The accepted dictionary request; the read addresses do not affect coverage. -/
def request (i : Loader.Inputs) (c : Loader.State) (reads : Fin 2 → BitVec 6) :
    Memory.Request 6 64 2 :=
  ⟨⟨Loader.push i c && c.cursor.toNat < 32,
    Memory.Sram.bankAddress (!c.active) (c.cursor.extractLsb' 0 5), i.data⟩, reads⟩

/-- A valid bank is fully initialized. An upload has initialized the dictionary
prefix below its accepted cursor in the inactive bank. -/
structure Covered (c : Loader.State) (t : Model) : Prop where
  active : c.valid = true → ∀ k : BitVec 5, t.Defined (Memory.Sram.bankAddress c.active k)
  staged : c.pending = true → ∀ k : BitVec 5, k.toNat < c.cursor.toNat →
    t.Defined (Memory.Sram.bankAddress (!c.active) k)

/-- Reset invalidates ownership; it makes no claim about cleared memory. -/
theorem covered_initial (t : Model) : Covered {} t := by
  exact ⟨by simp, by simp⟩

theorem covered_next (i : Loader.Inputs) (c : Loader.State) (t : Model)
    (reads : Fin 2 → BitVec 6) (h : Covered c t) :
    Covered (Loader.next i c) (t.step (request i c reads)) := by
  by_cases hp : Loader.push i c = true
  · rw [Loader.push_next i c hp]
    refine ⟨fun hv k => t.defined_step _ _ (h.active hv k), fun hpend k hk => ?_⟩
    have hinc := Loader.cursor_increment c.cursor (Loader.push_requires_valid i c hp).2.2.2.2.2.1
    by_cases hlt : k.toNat < c.cursor.toNat
    · exact t.defined_step _ _ (h.staged hpend k hlt)
    simp only [hinc] at hk
    have heq : c.cursor.toNat = k.toNat := by omega
    have haddr : c.cursor.extractLsb' 0 5 = k :=
      BitVec.eq_of_toNat_eq (by simp [BitVec.extractLsb'_toNat, heq, k.isLt])
    simpa only [request, haddr] using
      t.write_defined (request i c reads) (by simp [request, hp, heq, k.isLt])
  · by_cases hc : Loader.commit i c = true
    · rw [Loader.commit_next i c hc]
      obtain ⟨_, _, _, _, hpend, hcursor⟩ := Loader.commit_requires_complete i c hc
      exact ⟨fun _ k => t.defined_step _ _ (h.staged hpend k
        (by simpa [hcursor] using Nat.lt_trans k.isLt (by decide : 2 ^ 5 < 322))), by simp⟩
    · have hm : Covered c (t.step (request i c reads)) :=
        ⟨fun hv k => t.defined_step _ _ (h.active hv k),
          fun hp k hk => t.defined_step _ _ (h.staged hp k hk)⟩
      simp only [Loader.next, hp, hc]
      repeat' split
      all_goals first | contradiction | exact hm | exact ⟨hm.active, by simp⟩ | exact ⟨by simp, by simp⟩
      done

/-- Couple the existing loader step to the partial memory model. Read addresses
may depend on earlier responses; coverage holds for every resulting history. -/
def advance (s : Loader.State × Model) (i : Loader.Inputs × (Fin 2 → BitVec 6)) :
    Loader.State × Model :=
  (Loader.next i.1 s.1, s.2.step (request i.1 s.1 i.2))

theorem covered_run (inputs : List (Loader.Inputs × (Fin 2 → BitVec 6)))
    (s : Loader.State × Model) (h : Covered s.1 s.2) :
    Covered (inputs.foldl advance s).1 (inputs.foldl advance s).2 := by
  induction inputs generalizing s with
  | nil => exact h
  | cons i rest ih =>
    exact ih _ (covered_next i.1 s.1 s.2 i.2 h)

/-- Initialization establishes coverage even from an arbitrary controller and
memory model; every later command history preserves it. -/
theorem initialized_run (inputs : List (Loader.Inputs × (Fin 2 → BitVec 6)))
    (s : Loader.State × Model) (i : Loader.Inputs × (Fin 2 → BitVec 6))
    (hi : i.1.init = true) :
    Covered (inputs.foldl advance (advance s i)).1 (inputs.foldl advance (advance s i)).2 := by
  apply covered_run
  simpa [advance, Loader.next, hi] using covered_initial (s.2.step (request i.1 s.1 i.2))

/-- The emitted hybrid request is exactly the request used by the coverage
invariant, including capacity-adapted push acceptance. -/
theorem controller_request (i : Machine.Inputs) (s : Backend.State)
    (q : Bool → BitVec 64) (extra : Values SramController.Extra) :
    SramController.hybridRequest (SramController.inputValues i q)
      (SramController.registerValues s extra) =
    request (Machine.controlInput (Backend.adapt i s) s.reference.machine) s.control
      (SramController.hybridRequest (SramController.inputValues i q)
        (SramController.registerValues s extra)).read := by
  simp only [SramController.hybridRequest, request, Memory.Request.mk.injEq,
    Memory.Write.mk.injEq, and_true]
  exact ⟨SramController.hybrid_request_enable i s q extra,
    SramController.hybrid_write_address i s q extra, rfl⟩

theorem controller_covered_next (i : Machine.Inputs) (s : Backend.State)
    (q : Bool → BitVec 64) (extra : Values SramController.Extra) (t : Model)
    (h : Covered s.control t) :
    Covered (Loader.next (Machine.controlInput (Backend.adapt i s) s.reference.machine) s.control)
      (t.step (SramController.hybridRequest (SramController.inputValues i q)
        (SramController.registerValues s extra))) := by
  rw [controller_request]
  exact covered_next _ _ _ _ h

/-- The selected bank is initialized on every usable read, including the
commit edge before the active-bank register switches. -/
theorem selected_defined (i : Loader.Inputs) (c : Loader.State) (t : Model)
    (h : Covered c t) (hv : c.valid = true ∨ Loader.commit i c = true) (k : BitVec 5) :
    t.Defined (Memory.Sram.bankAddress (if Loader.commit i c then !c.active else c.active) k) := by
  by_cases hc : Loader.commit i c = true
  · obtain ⟨_, _, _, _, hpend, hcursor⟩ := Loader.commit_requires_complete i c hc
    simpa only [hc, ite_true] using h.staged hpend k
      (by simpa [hcursor] using Nat.lt_trans k.isLt (by decide : 2 ^ 5 < 322))
  · simpa [hc] using h.active (hv.resolve_right hc) k

/-- Each actual hybrid read address names an initialized dictionary word when
the loader is valid or committing, regardless of the chosen program address. -/
theorem controller_read_defined (i : Machine.Inputs) (s : Backend.State)
    (q : Bool → BitVec 64) (extra : Values SramController.Extra) (t : Model)
    (h : Covered s.control t)
    (hv : s.control.valid = true ∨ Machine.committing (Backend.adapt i s) s.reference.machine = true)
    (port : Fin 2) :
    t.Defined ((SramController.hybridRequest (SramController.inputValues i q)
      (SramController.registerValues s extra)).read port) := by
  simp only [SramController.hybridRequest, SramController.hybrid_read_address]
  exact selected_defined (Machine.controlInput (Backend.adapt i s) s.reference.machine)
    s.control t h hv _

/-- On a usable non-write edge, each physical copy returns a value established
by the upload model, even if the copies began with unrelated contents. -/
theorem controller_response_defined (i : Machine.Inputs) (s : Backend.State)
    (q : Bool → BitVec 64) (extra : Values SramController.Extra) (t : Model)
    (arrays : Fin 2 → Memory.Sram.State 6 64) (h : Covered s.control t)
    (hr : Memory.Sram.Related arrays t)
    (hv : s.control.valid = true ∨ Machine.committing (Backend.adapt i s) s.reference.machine = true)
    (hw : (SramController.hybridRequest (SramController.inputValues i q)
      (SramController.registerValues s extra)).write.enable = false) (port : Fin 2) :
    let req := SramController.hybridRequest (SramController.inputValues i q)
      (SramController.registerValues s extra)
    ∃ v, (t.step req).q port = some v ∧ (Memory.Sram.step req arrays port).q = v := by
  obtain ⟨v, hword⟩ := controller_read_defined i s q extra t h hv port
  exact ⟨v, by simpa [Memory.Sram.Model.step, hw] using hword,
    Memory.Sram.read_defined _ _ _ hr hw port v hword⟩

end Pinwheel.Hardware.Storage.SramCoverage
