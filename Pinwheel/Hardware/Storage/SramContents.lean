import Pinwheel.Hardware.Storage.SramCoverage
import Pinwheel.Hardware.Loader.Program

/-! Correspondence between initialized SRAM words and the existing loader's
program image. This strengthens coverage with value equality; memory contents
remain arbitrary until the corresponding upload establishes them. -/
namespace Pinwheel.Hardware.Storage.SramContents
open Pinwheel.Hardware Loader

def Agrees (memory : Bool → Store.Image) (t : SramCoverage.Model) : Prop :=
  ∀ bank (k : BitVec 5) v, t.contents (Memory.Sram.bankAddress bank k) = some v →
    memory bank (.word (k.zeroExtend 6)) = v

theorem write_at (i : Loader.Inputs) (c : Loader.State) (reads : Fin 2 → BitVec 6)
    (bank : Bool) (k : BitVec 5) :
    ((SramCoverage.request i c reads).write.enable &&
      (SramCoverage.request i c reads).write.address == Memory.Sram.bankAddress bank k) =
    (Loader.push i c && (bank != c.active) && c.cursor == Store.offset (.word (k.zeroExtend 6))) := by
  simp only [SramCoverage.request, Store.offset]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, decide_eq_true_eq]
  by_cases hb : bank = c.active
  · have hn := Memory.Sram.bankAddress_ne (!c.active) bank (c.cursor.extractLsb' 0 5) k
      (by rw [hb]; cases c.active <;> decide)
    exact ⟨fun h => (hn h.2).elim, fun h => (h.1.2 hb).elim⟩
    done
  · have hs : (!c.active) = bank := by cases he : c.active <;> cases bank <;> simp_all
    rw [hs]
    change ((Loader.push i c = true ∧ c.cursor.toNat < 32) ∧
        ((BitVec.ofBool bank) ++ c.cursor.extractLsb' 0 5) = ((BitVec.ofBool bank) ++ k)) ↔
      ((Loader.push i c = true ∧ bank ≠ c.active) ∧ c.cursor = BitVec.ofNat 9 (k.zeroExtend 6).toNat)
    simp only [BitVec.append_right_inj]
    simp [ne_eq, hb, ← BitVec.toNat_inj, BitVec.extractLsb'_toNat, BitVec.toNat_ofNat,
      BitVec.toNat_setWidth]
    constructor
    · rintro ⟨⟨hp, hc⟩, he⟩
      exact ⟨hp, by omega⟩
      done
    · rintro ⟨hp, he⟩
      have hk : k.toNat < 32 := k.isLt
      exact ⟨⟨hp, by omega⟩, by omega⟩
      done
    done
  done

theorem agrees_next (i : Machine.Inputs) (s : Machine.State) (t : SramCoverage.Model)
    (reads : Fin 2 → BitVec 6) (h : Agrees s.memory t) :
    Agrees (Machine.next i s).memory
      (t.step (SramCoverage.request (Machine.controlInput i s) s.control reads)) := by
  intro bank k v hv
  simp only [Memory.Sram.Model.step, write_at] at hv
  simp only [Machine.next, Store.tick, Machine.memoryInput]
  split at hv <;> simp_all only [↓reduceIte, Bool.false_eq_true, BitVec.extractLsb'_eq_self, Option.some.injEq]
  all_goals first | exact hv | exact h bank k v hv
  done

theorem agrees_initial (memory : Bool → Store.Image) :
    Agrees memory Memory.Sram.Model.initial := by
  simp [Agrees, Memory.Sram.Model.initial]
  done

/-- The controller's actual request preserves program-word correspondence,
even when its scheduler is fed an arbitrary response word. -/
theorem controller_agrees_next (i : Machine.Inputs) (s : Backend.State)
    (q : Bool → BitVec 64) (extra : Values SramController.Extra) (t : SramCoverage.Model)
    (h : Agrees s.reference.machine.memory t) (word : BitVec 64) :
    Agrees (Backend.Policy.fedNext word i s).reference.machine.memory
      (t.step (SramController.hybridRequest (SramController.inputValues i q)
        (SramController.registerValues s extra))) := by
  simp only [Backend.Policy.fedNext, Backend.State.reference, Backend.State.small, Small.State.reference]
  change Agrees (Backend.next i s).reference.machine.memory _
  rw [Backend.reference_next, SramCoverage.controller_request]
  simp only [Cache.next]
  exact agrees_next _ _ _ _ h
  done

/-- A defined dictionary entry is the word of the existing indexed program
image at the requested program address. -/
theorem lookup_word (s : Backend.State) (t : SramCoverage.Model)
    (h : Agrees s.reference.machine.memory t) (bank : Bool) (pc : BitVec 8)
    (hd : t.Defined (Memory.Sram.bankAddress bank ((s.indices bank)[pc.toNat]))) :
    t.contents (Memory.Sram.bankAddress bank ((s.indices bank)[pc.toNat])) =
      some (Loader.Store.read (s.reference.machine.memory bank) pc) := by
  obtain ⟨v, hv⟩ := hd
  rw [hv, ← h bank _ v hv]
  simp only [Loader.Store.read, Backend.State.reference, Backend.State.small, Small.State.reference,
    BitVec.zeroExtend_eq_setWidth, BitVec.setWidth_eq_append (by decide : 5 ≤ 6)]
  rfl
  done

/-- Program address chosen by the actual controller before the SRAM lookup. -/
def address (i : Machine.Inputs) (s : Backend.State) (q : Bool → BitVec 64)
    (extra : Values SramController.Extra) (port : Fin 2) : BitVec 8 :=
  (if port.val == 1 then SramController.sched (Dispatch.candidateExpr true)
    else SramController.address0).eval
      (WithWire.values (SramController.inputValues i q)
        (SramController.successor.eval (SramController.inputValues i q) (SramController.registerValues s extra)))
      (SramController.registerValues s extra)

theorem controller_read_word (i : Machine.Inputs) (s : Backend.State)
    (q : Bool → BitVec 64) (extra : Values SramController.Extra) (t : SramCoverage.Model)
    (h : Agrees s.reference.machine.memory t) (hc : SramCoverage.Covered s.control t)
    (hv : s.control.valid = true ∨ Machine.committing (Backend.adapt i s) s.reference.machine = true)
    (port : Fin 2) :
    t.contents ((SramController.hybridRequest (SramController.inputValues i q)
      (SramController.registerValues s extra)).read port) =
      some (Loader.Store.read (s.reference.machine.memory
        (Machine.selected (Backend.adapt i s) s.reference.machine)) (address i s q extra port)) := by
  have hd := SramCoverage.controller_read_defined i s q extra t hc hv port
  simp only [SramController.hybridRequest, SramController.hybrid_read_address] at hd ⊢
  exact lookup_word s t h _ _ hd
  done

/-- The actual read response equals the selected image's word on the next
edge. Initial contents and idle responses need not be equal across copies. -/
theorem physical_read_word (i : Machine.Inputs) (s : Backend.State)
    (q : Bool → BitVec 64) (extra : Values SramController.Extra) (t : SramCoverage.Model)
    (arrays : Fin 2 → Memory.Sram.State 6 64)
    (h : Agrees s.reference.machine.memory t) (hc : SramCoverage.Covered s.control t)
    (hr : Memory.Sram.Related arrays t)
    (hv : s.control.valid = true ∨ Machine.committing (Backend.adapt i s) s.reference.machine = true)
    (hw : (SramController.hybridRequest (SramController.inputValues i q)
      (SramController.registerValues s extra)).write.enable = false) (port : Fin 2) :
    (Memory.Sram.step (SramController.hybridRequest (SramController.inputValues i q)
      (SramController.registerValues s extra)) arrays port).q =
      Loader.Store.read (s.reference.machine.memory
        (Machine.selected (Backend.adapt i s) s.reference.machine)) (address i s q extra port) := by
  exact Memory.Sram.read_defined _ _ _ hr hw port _ (controller_read_word i s q extra t h hc hv port)
  done

end Pinwheel.Hardware.Storage.SramContents
