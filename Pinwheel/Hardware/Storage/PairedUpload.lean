import Pinwheel.Hardware.Storage.PairedLoader
import Pinwheel.Hardware.Storage.PairedClosed

/-! Upload correspondence for the actual named paired graph. The acceptance
predicate is read from that graph; it is not an assumption that every host word
passes validation. -/
namespace Pinwheel.Hardware.Storage.PairedUpload
open Pinwheel.Hardware PairedController
set_option backward.isDefEq.respectTransparency false

def control (s : Values Register) : Loader.State :=
  ⟨s .active == 1, s .valid == 1, s .pending == 1, s .cursor⟩

def inputs (g : Values GraphInput) (s : Values Register) : Loader.Inputs :=
  ⟨init.eval g s == 1, reset.eval g s == 1, busy.eval g s == 1,
    g (.base .command), data.eval g s⟩

def admitted (g : Values GraphInput) (s : Values Register) : Bool := good.eval g s == 1

def banks (s : Values Register) (m : Memory.Sram.State 9 64) : PairedLoader.Banks
  | b, _, .parameter k => s (.parameter b k)
  | b, _, .row k => m.contents (Memory.Sram.bankAddress b k)
  | b, _, .boot => s (.boot b)
  | b, _, .idle => s (.idle b)

theorem bit_cases (v : BitVec 1) : v = 0 ∨ v = 1 := by bv_omega

theorem bit_value (v : BitVec 1) : BitVec.ofBool (v == 1) = v := by
  rcases bit_cases v with h | h <;> simp [h]

private theorem bit_binding (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s) (name : Computation) (e : E 1)
    (hb : (name, .concat (.lit (0 : BitVec 63)) e) ∈ bindings) :
    (g (.node name)).extractLsb' 0 1 = e.eval g s := by
  simpa only [Expr.eval, BitVec.extractLsb'_append_eq_right] using
    congrArg (fun v : BitVec 64 => v.extractLsb' 0 1) (h name _ hb)

theorem accepting_value (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s) :
    accepting.eval g s = BitVec.ofBool (Loader.enabled (inputs g s)) := by
  have hr : resetting.eval g s = resettingExpr.eval g s :=
    bit_binding g s h .resetting resettingExpr (by simp [bindings])
  have ha : accepting.eval g s = acceptingExpr.eval g s :=
    bit_binding g s h .accepting acceptingExpr (by simp [bindings])
  simp only [ha, acceptingExpr, either, Expr.eval, hr, resettingExpr, inputs, Loader.enabled]
  rcases bit_cases (init.eval g s) with hi | hi <;> simp_all
  all_goals rcases bit_cases (reset.eval g s) with hr | hr <;> simp_all
  all_goals rcases bit_cases (busy.eval g s) with hb | hb <;> simp_all
  done

theorem push_value (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s) :
    push.eval g s = BitVec.ofBool (PairedLoader.push (inputs g s) (admitted g s) (control s)) := by
  have hp : push.eval g s = pushExpr.eval g s :=
    bit_binding g s h .push pushExpr (by simp [bindings])
  simp only [hp, pushExpr, both, cmd, below, Expr.eval, accepting_value g s h,
    PairedLoader.push, control, admitted, inputs, BitVec.reduceToNat]
  conv => lhs; rw [← bit_value (s .pending), ← bit_value (good.eval g s)]
  simp only [BitVec.ofBool_and_ofBool, Bool.beq_eq_decide_eq, Bool.and_assoc]
  done

theorem commit_value (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s) :
    commit.eval g s = BitVec.ofBool (PairedLoader.commit (inputs g s) (control s)) := by
  have hc : commit.eval g s = commitExpr.eval g s :=
    bit_binding g s h .commit commitExpr (by simp [bindings])
  simp only [hc, commitExpr, both, cmd, atCursor, Expr.eval, accepting_value g s h,
    PairedLoader.commit, control, inputs]
  conv => lhs; rw [← bit_value (s .pending)]
  simp only [BitVec.ofBool_and_ofBool, Bool.beq_eq_decide_eq, Bool.and_assoc]
  done

theorem inactive_value (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s) : inactive.eval g s = ~~~s .active := by
  simpa only [inactive, inactiveExpr, Expr.eval] using
    bit_binding g s h .inactive inactiveExpr (by simp [bindings])

private theorem control_ext (c d : Loader.State) (ha : c.active = d.active)
    (hv : c.valid = d.valid) (hp : c.pending = d.pending) (hc : c.cursor = d.cursor) : c = d := by
  cases c <;> cases d <;> simp_all

private theorem active_ite (p : Prop) [Decidable p] (c d : Loader.State) :
    (if p then c else d).active = if p then c.active else d.active := by split <;> rfl
private theorem valid_ite (p : Prop) [Decidable p] (c d : Loader.State) :
    (if p then c else d).valid = if p then c.valid else d.valid := by split <;> rfl
private theorem pending_ite (p : Prop) [Decidable p] (c d : Loader.State) :
    (if p then c else d).pending = if p then c.pending else d.pending := by split <;> rfl
private theorem cursor_ite (p : Prop) [Decidable p] (c d : Loader.State) :
    (if p then c else d).cursor = if p then c.cursor else d.cursor := by split <;> rfl

theorem control_next (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s) :
    control (body.step g s) = PairedLoader.next (inputs g s) (admitted g s) (control s) := by
  have hs : selected.eval g s = selectedExpr.eval g s :=
    bit_binding g s h .selected selectedExpr (by simp [bindings])
  have hr : resetting.eval g s = resettingExpr.eval g s :=
    bit_binding g s h .resetting resettingExpr (by simp [bindings])
  simp only [control, Circuit.step, body, PairedController.next, Expr.eval, hs, hr,
    selectedExpr, resettingExpr, both, either, cmd, inactive_value g s h,
    accepting_value g s h, push_value g s h, commit_value g s h,
    PairedLoader.next, PairedLoader.commit, PairedLoader.push, inputs, control, admitted, Loader.enabled]
  apply control_ext
  all_goals simp only [active_ite, valid_ite, pending_ite, cursor_ite]
  all_goals rcases bit_cases (init.eval g s) with hi | hi <;> simp_all
  all_goals rcases bit_cases (reset.eval g s) with hr | hr <;> simp_all
  all_goals rcases bit_cases (busy.eval g s) with hb | hb <;> simp_all
  all_goals rcases bit_cases (s .valid) with hv | hv <;> simp_all
  all_goals by_cases hc : g (.base .command) = 1 <;> simp_all
  all_goals by_cases hc : g (.base .command) = 4 <;> simp_all
  all_goals rcases bit_cases (s .pending) with hp | hp <;> simp_all
  all_goals by_cases hc : g (.base .command) = 3 <;> simp_all
  all_goals simp_all [Bool.beq_eq_decide_eq]
  all_goals by_cases hc : s .cursor = 290 <;> simp_all
  all_goals rcases bit_cases (s .active) with ha | ha <;> simp_all
  done

theorem bit_and_one (a b : BitVec 1) : a &&& b = 1 ↔ a = 1 ∧ b = 1 := by
  rcases bit_cases a with ha | ha <;> rcases bit_cases b with hb | hb <;> simp_all

theorem bank_eq (a : BitVec 1) (b : Bool) :
    ~~~a = BitVec.ofBool b ↔ (b != (a == 1)) = true := by
  cases b <;> rcases bit_cases a with ha | ha <;> simp_all

def memoryNext (g : Values GraphInput) (s : Values Register) (m : Memory.Sram.State 9 64) :=
  Memory.SinglePort.step m (PairedClosed.command (body.observe g s))

private theorem memory_contents (o : Values (SramController.Out O)) (m : Memory.Sram.State 9 64)
    (address : BitVec 9) :
    (Memory.SinglePort.step m (PairedClosed.command o)).contents address =
      if o (.port .write) = 1 ∧ o (.port (.address false)) = address
      then o (.port .data) else m.contents address := by
  by_cases hw : o (.port .write) = 1 <;> by_cases hr : o (.port .read) = 1 <;>
    simp_all [PairedClosed.command, Memory.SinglePort.step, Memory.Sram.State.step, Memory.Contents.write]

private theorem address_eq (a b : BitVec 1) (r k : BitVec 8) :
    a ++ r = b ++ k ↔ a = b ∧ r = k := by
  refine ⟨fun h => ⟨?_, ?_⟩, fun ⟨ha, hr⟩ => ha ▸ hr ▸ rfl⟩
  · simpa only [BitVec.extractLsb'_append_eq_left] using congrArg (fun v : BitVec 9 => v.extractLsb' 8 1) h
  · simpa only [BitVec.extractLsb'_append_eq_right] using congrArg (fun v : BitVec 9 => v.extractLsb' 0 8) h

private theorem row_offset (c : BitVec 9) (k : BitVec 8) :
    (¬c.toNat < 32) ∧ c.toNat < 288 ∧ (c - 32).extractLsb' 0 8 = k ↔
      c.toNat = 32 + k.toNat := by
  simp only [← BitVec.toNat_inj, BitVec.extractLsb'_toNat, BitVec.toNat_sub,
    Nat.shiftRight_zero, BitVec.reduceToNat, Nat.reducePow]
  omega
  done

private theorem parameter_offset (c : BitVec 9) (k : BitVec 5) :
    c.toNat < 32 ∧ c = BitVec.ofNat 9 k.toNat ↔ c.toNat = k.toNat := by bv_omega

private theorem guarded_eq (p : Prop) [Decidable p] (a b c : α) :
    (p ∧ (if p then a else b) = c) ↔ p ∧ a = c := by by_cases h : p <;> simp [h]

theorem banks_next (g : Values GraphInput) (s : Values Register) (m : Memory.Sram.State 9 64)
    (h : PairedSemantics.Equations bindings g s) :
    banks (body.step g s) (memoryNext g s m) =
      PairedLoader.write (inputs g s) (admitted g s) (control s) (banks s m) := by
  funext b w slot
  cases slot with
  | row k =>
    have hw : writing.eval g s = writingExpr.eval g s :=
      bit_binding g s h .writing writingExpr (by simp [bindings])
    simp only [banks, memoryNext, memory_contents, Circuit.observe, body, request, Expr.eval,
      PairedLoader.write, PairedLoader.offset, inputs, control, BitVec.extractLsb'_eq_self]
    congr 1
    simp only [guarded_eq, hw, writingExpr, both, below, Expr.eval,
      bit_and_one, push_value g s h, inactive_value g s h, Memory.Sram.bankAddress, address_eq,
      bank_eq, Reactive.bool_one, BitVec.not_ofBool, Bool.not_eq_true', decide_eq_false_iff_not,
      decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq, BitVec.reduceToNat]
    simpa only [inputs, control, and_assoc, and_left_comm, and_comm] using
      congrArg (fun p : Prop => PairedLoader.push (inputs g s) (admitted g s) (control s) = true ∧
        (b != (s .active == 1)) = true ∧ p) (propext (row_offset (s .cursor) k))
    done
  | parameter k =>
    simp only [banks, Circuit.step, body, PairedController.next, both, below, Expr.eval,
      push_value g s h, inactive_value g s h, PairedLoader.write, PairedLoader.offset, inputs, control]
    congr 1
    simp only [bit_and_one, Reactive.bool_one, decide_eq_true_eq, bank_eq,
      Bool.and_eq_true, beq_iff_eq, BitVec.reduceToNat]
    simpa only [inputs, control, and_assoc, and_left_comm, and_comm] using
      congrArg (fun p : Prop => PairedLoader.push (inputs g s) (admitted g s) (control s) = true ∧
        (b != (s .active == 1)) = true ∧ p) (propext (parameter_offset (s .cursor) k))
    done
  | boot | idle =>
    simp only [banks, Circuit.step, body, PairedController.next, both, atCursor, Expr.eval,
      push_value g s h, inactive_value g s h, PairedLoader.write, PairedLoader.offset, inputs, control,
      bit_and_one, Reactive.bool_one, decide_eq_true_eq, bank_eq, Bool.and_eq_true, beq_iff_eq]
    simp only [← BitVec.toNat_inj, BitVec.reduceToNat, and_assoc, and_comm]
    done

theorem init_value (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s) : init.eval g s = g (.base .init) := by
  simpa only [init, initExpr, Expr.eval] using
    bit_binding g s h .init initExpr (by simp [bindings])

theorem data_value (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s) : data.eval g s = g (.base .data) := by
  simpa only [data, dataExpr, Expr.eval, BitVec.extractLsb'_eq_self] using
    h .data dataExpr (by simp [bindings])

/-- Every upload write preserves the previously active bank, including the
parameter registers and both metadata registers, with no initialization premise. -/
theorem active_storage_preserved (g : Values GraphInput) (s : Values Register)
    (m : Memory.Sram.State 9 64) (h : PairedSemantics.Equations bindings g s)
    (slot : PairedLoader.Slot w) :
    banks (body.step g s) (memoryNext g s m) (control s).active slot =
      banks s m (control s).active slot :=
  (congrArg (fun b : PairedLoader.Banks => b (control s).active slot) (banks_next g s m h)).trans
    (PairedLoader.write_active (inputs g s) (admitted g s) (control s) (banks s m) slot)

end Pinwheel.Hardware.Storage.PairedUpload
