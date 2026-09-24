import Pinwheel.Hardware.Memory.Flops
import Pinwheel.Hardware.Storage.SramController

/-! A local-decoding index-map tile. Reuse the proved latency-zero memory;
only its projection and the existing loader/address wiring are new. The chip
does not instantiate this experimental boundary yet. -/
namespace Pinwheel.Hardware.Storage.MapTile
open Loader

abbrev Input := Memory.Flops.Input 4 5 2
abbrev Register := Memory.Flops.Register 4 5
abbrev Output := Memory.Flops.Output 5 2
abbrev circuit := Memory.Flops.circuit 4 5 2

/-- A bottom subtree of the existing read tree fixes the low address nibble. -/
def wordAddress (low high : BitVec 4) : BitVec 8 := high ++ low

def writeAddress (cursor : BitVec 9) : BitVec 8 := (cursor - 64).extractLsb' 0 8

/-- The full range check matters: truncated cursors outside 64..319 must not alias. -/
def selected (cursor : BitVec 9) (low : BitVec 4) : Bool :=
  decide (64#9 ≤ cursor) && decide (cursor < 320#9) &&
    (writeAddress cursor).extractLsb' 0 4 == low

def request (i : Store.Inputs) (low : BitVec 4) (pcs : Fin 2 → BitVec 8) :
    Memory.Request 4 5 2 :=
  ⟨⟨i.write && selected i.cursor low, (writeAddress i.cursor).extractLsb' 4 4,
    i.data.extractLsb' 0 5⟩, fun port => (pcs port).extractLsb' 4 4⟩

def project (m : Store.Image) (low : BitVec 4) : Memory.Contents 4 5 :=
  fun high => (m (.index (wordAddress low high))).extractLsb' 0 5

theorem cursor_match (cursor : BitVec 9) (low high : BitVec 4) :
    (selected cursor low && (writeAddress cursor).extractLsb' 4 4 == high) =
      (cursor == Store.offset (.index (wordAddress low high))) := by
  simp only [selected, writeAddress, wordAddress, Store.offset, BitVec.ofNat_add,
    BitVec.ofNat_toNat]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  have hcat := BitVec.toNat_append high low
  rw [← Nat.shiftLeft_add_eq_or_of_lt low.isLt, Nat.shiftLeft_eq] at hcat
  simp only [BitVec.le_def, BitVec.lt_def, ← BitVec.toNat_inj, BitVec.extractLsb'_toNat,
    BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow]
  bv_omega
  done

/-- Every tile word makes exactly the existing store's update, including hold
on non-index cursors, rejected writes, reset and writes to the other bank. -/
theorem next_current (i : Store.Inputs) (m : Store.Image) (low high : BitVec 4)
    (pcs : Fin 2 → BitVec 8) :
    circuit.step (Memory.Flops.requestValues (request i low pcs))
      (Memory.Flops.contentsValues (project m low)) (.word high) =
      (Store.tick i m (.index (wordAddress low high))).extractLsb' 0 5 := by
  rw [Memory.Flops.next_correct]
  simp only [Memory.Contents.write, request, Bool.and_assoc, cursor_match, Store.tick,
    project, apply_ite]
  split <;> simp_all
  done

/-- Both tile outputs are the current read tree restricted to this low nibble. -/
theorem read_current (i : Store.Inputs) (m : Store.Image) (low : BitVec 4)
    (pcs : Fin 2 → BitVec 8) (port : Fin 2) :
    circuit.observe (Memory.Flops.requestValues (request i low pcs))
      (Memory.Flops.contentsValues (project m low)) (.data port) =
      ((Execution.readTree 8 (fun k => .reg (.index k))
        (.lit (wordAddress low ((pcs port).extractLsb' 4 4))) :
          Expr Store.Input Store.Register 6).eval i.values m).extractLsb' 0 5 := by
  simp [Memory.Flops.observe_correct, request, project, Execution.readTree_correct, Expr.eval]
  done

/-- Choosing the tile by the PC's low nibble recovers the complete lookup. -/
theorem selected_read (i : Store.Inputs) (m : Store.Image)
    (pcs : Fin 2 → BitVec 8) (port : Fin 2) :
    circuit.observe (Memory.Flops.requestValues
      (request i ((pcs port).extractLsb' 0 4) pcs))
      (Memory.Flops.contentsValues (project m ((pcs port).extractLsb' 0 4))) (.data port) =
      (m (.index (pcs port))).extractLsb' 0 5 := by
  simp only [Memory.Flops.observe_correct, request, project, wordAddress]
  rw [BitVec.extractLsb'_append_extractLsb' (x := pcs port) (w := 4) (len := 4)]
  done

/-- Tie the tile update to the actual hybrid controller, after its existing
capacity, loader and inactive-bank admission. No cleared-memory assumption. -/
theorem controller_next (i : Machine.Inputs) (s : Backend.State)
    (q : Bool → BitVec 64) (extra : Values SramController.Extra)
    (bank : Bool) (low high : BitVec 4) (pcs : Fin 2 → BitVec 8) :
    circuit.step (Memory.Flops.requestValues
      (request (Machine.memoryInput (Backend.adapt i s) s.reference.machine bank) low pcs))
      (Memory.Flops.contentsValues (project (s.reference.machine.memory bank) low)) (.word high) =
      (SramController.core false).step (SramController.inputValues i q)
        (SramController.registerValues s extra) (.inner (.index bank (wordAddress low high))) := by
  rw [next_current]
  simpa only [SramController.core, Netlist.step, Circuit.step, SramController.body,
    SramController.liftW_eval, Backend.Policy.fedNext, Backend.next, Backend.State.values,
    Vector.getElem_ofFn, Cache.next, Machine.next, BitVec.ofFin, BitVec.toNat] using
    (Backend.Policy.core_step
      (SramController.successor.eval (SramController.inputValues i q)
        (SramController.registerValues s extra)) i s (.index bank (wordAddress low high))).symm
  done

def controllerPCs (i : Machine.Inputs) (s : Backend.State)
    (q : Bool → BitVec 64) (extra : Values SramController.Extra)
    (word : BitVec 64) (port : Fin 2) : BitVec 8 :=
  (if port.val == 1 then SramController.sched (Dispatch.candidateExpr true)
    else SramController.address0).eval
      (WithWire.values (SramController.inputValues i q) word)
      (SramController.registerValues s extra)

/-- Both candidate lookups retain the actual selected bank and PC, including
commit and start bypasses. No extra cycle or assumption about branch spacing. -/
theorem controller_read (i : Machine.Inputs) (s : Backend.State)
    (q : Bool → BitVec 64) (extra : Values SramController.Extra)
    (word : BitVec 64) (port : Fin 2) :
    let bank := Machine.selected (Backend.adapt i s) s.reference.machine
    let pcs := controllerPCs i s q extra word
    Memory.Sram.bankAddress bank
      (circuit.observe (Memory.Flops.requestValues
        (request (Machine.memoryInput (Backend.adapt i s) s.reference.machine bank)
          ((pcs port).extractLsb' 0 4) pcs))
        (Memory.Flops.contentsValues
          (project (s.reference.machine.memory bank) ((pcs port).extractLsb' 0 4))) (.data port)) =
      ((SramController.readAddress false (port.val == 1)).eval
        (WithWire.values (SramController.inputValues i q) word)
        (SramController.registerValues s extra)).extractLsb' 0 6 := by
  dsimp only
  rw [selected_read]
  simpa only [controllerPCs, Backend.State.reference, Backend.State.small,
    Small.State.reference, BitVec.extractLsb'_append_eq_right] using
    (SramController.hybrid_read_address i s q extra word (port.val == 1)).symm
  done

end Pinwheel.Hardware.Storage.MapTile
