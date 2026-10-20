import Pinwheel.Hardware.Buffered.SerialModel

/-! Universal correspondence of the sampled serial expression graph with its
independent Boolean/Nat record model. These results concern the typed frontend;
neither RTL emission nor physical sampling is assumed. -/
namespace Pinwheel.Hardware.Buffered.Serial
open Pinwheel.Hardware

private theorem append_toNat_add (a : BitVec m) (b : BitVec n) :
    (a ++ b).toNat = a.toNat * 2^n + b.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt b.isLt, Nat.shiftLeft_eq]
  done

private theorem one_and (x : BitVec 1) : 1#1 &&& x = x := by
  have cases : x = 0#1 ∨ x = 1#1 := by bv_omega
  rcases cases with rfl | rfl <;> rfl
  done

private theorem ofBool_one (b : Bool) : BitVec.ofBool b = 1#1 ↔ b = true := by
  cases b <;> decide
  done

private theorem ofBool_beq_one (x : BitVec 1) : BitVec.ofBool (x == 1#1) = x := by
  have cases : x = 0#1 ∨ x = 1#1 := by bv_omega
  rcases cases with rfl | rfl <;> rfl
  done

theorem request_shift (word : BitVec 160) (bit : Bool) :
    word.extractLsb' 0 159 ++ BitVec.ofBool bit =
      BitVec.ofNat 160 (2 * word.toNat + bit.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [append_toNat_add]
  simp [Nat.shiftRight_eq_div_pow]
  cases bit <;> simp <;> omega
  done

theorem requestField_eq (s : State) (start width : Nat) :
    requestField s start width = s.request.extractLsb' start width := by
  apply BitVec.eq_of_toNat_eq
  simp [requestField, Nat.shiftRight_eq_div_pow]
  done

theorem opcode_toNat (s : State) (i : Inputs) :
    (opcode.eval i.values s.values).toNat = requestOpcode s := by
  simp [opcode, Expr.eval, State.values, requestOpcode, Nat.shiftRight_eq_div_pow]
  done

private theorem bitvec_eq_nat (a b : BitVec w) : a = b ↔ a.toNat = b.toNat :=
  ⟨congrArg BitVec.toNat, BitVec.eq_of_toNat_eq⟩

theorem op_correct (s : State) (i : Inputs) (n : Nat) (bound : n < 16) :
    (op n).eval i.values s.values = BitVec.ofBool (requestOpcode s == n) := by
  simp only [op, Expr.eval, bitvec_eq_nat, opcode_toNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt bound]
  rfl
  done

theorem headerValid_correct (s : State) (i : Inputs) :
    headerValid.eval i.values s.values = BitVec.ofBool (s.request.toNat / 2^148 == 0xA71) := by
  simp +instances [headerValid, Expr.eval, State.values, bitvec_eq_nat,
    Nat.shiftRight_eq_div_pow]
  have hb : s.request.toNat / 2^148 < 4096 := by have := s.request.isLt; omega
  rw [Nat.mod_eq_of_lt hb]
  rfl
  done

theorem reserved_correct (s : State) (i : Inputs) (used : Nat) (bound : used ≤ 128) :
    (reserved used bound).eval i.values s.values =
      BitVec.ofBool ((s.request.toNat % 2^128) / 2^used == 0) := by
  simp +instances [reserved, payload, Expr.eval, State.values, bitvec_eq_nat,
    Nat.shiftRight_eq_div_pow]
  rw [← Nat.mod_mul_right_div_self, ← Nat.pow_add, Nat.add_sub_of_le bound]
  rfl
  done

private theorem requestOpcode_cases (s : State) :
    requestOpcode s = 0 ∨ requestOpcode s = 1 ∨ requestOpcode s = 2 ∨
    requestOpcode s = 3 ∨ requestOpcode s = 4 ∨ requestOpcode s = 5 ∨
    requestOpcode s = 6 ∨ requestOpcode s = 7 ∨ requestOpcode s = 8 ∨
    requestOpcode s = 9 ∨ requestOpcode s = 10 ∨ requestOpcode s = 11 ∨
    requestOpcode s = 12 ∨ requestOpcode s = 13 ∨ requestOpcode s = 14 ∨
    requestOpcode s = 15 := by
  have bound : requestOpcode s < 16 := Nat.mod_lt _ (by decide)
  omega
  done

theorem reservedValid_correct (s : State) (i : Inputs) :
    reservedValid.eval i.values s.values = BitVec.ofBool
      (match requestOpcode s with
      | 0 => s.request.toNat % 2^128 / 2^5 == 0
      | 1 => s.request.toNat % 2^128 / 2^98 == 0
      | 2 => s.request.toNat % 2^128 / 2^24 == 0
      | 3 => s.request.toNat % 2^128 / 2^60 == 0
      | 4 => s.request.toNat % 2^128 / 2^32 == 0
      | 6 => s.request.toNat % 2^128 / 2^60 == 0
      | 7 | 8 => s.request.toNat % 2^128 == 0
      | _ => false) := by
  rcases requestOpcode_cases s with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals simp [reservedValid, either, Expr.eval, op_correct s i 0 (by decide),
    op_correct s i 1 (by decide), op_correct s i 2 (by decide), op_correct s i 3 (by decide),
    op_correct s i 4 (by decide), op_correct s i 6 (by decide),
    op_correct s i 7 (by decide), op_correct s i 8 (by decide), reserved_correct, h]
  done

theorem closingCode_correct (s : State) (i : Inputs) :
    closingCode.eval i.values s.values = requestCode s := by
  simp +instances [closingCode, Expr.eval, State.values, headerValid_correct,
    reservedValid_correct, requestCode, bitvec_eq_nat]
  rcases requestOpcode_cases s with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals simp [h]
  done

theorem delivering_correct (s : State) (i : Inputs) :
    delivering.eval i.values s.values = BitVec.ofBool (deliver i s) := by
  simp [delivering, both, deliver, Expr.eval, Inputs.values, State.values]
  simp [Bool.and_assoc, Bool.beq_eq_decide_eq]
  rfl
  done

theorem coreInput_correct (s : State) (i : Inputs) (p : Reactive.Input w) :
    (coreInput p).eval i.values s.values = s.coreInput i p := by
  cases p
  all_goals simp [coreInput, State.coreInput, both, either, Expr.eval,
    delivering_correct, op_correct s i 4 (by decide), op_correct s i 6 (by decide),
    op_correct s i 8 (by decide), headerValid_correct, reserved_correct,
    payload, State.values, Inputs.values, requestField_eq]
  case command =>
    simp only [opcode, Expr.eval, State.values]
    split
    · apply BitVec.eq_of_getLsbD_eq
      intro j bound
      have bound4 : j < 4 := by omega
      simp [bound, bound4]
    · rfl
  case address =>
    split
    · apply BitVec.eq_of_toNat_eq
      rw [append_toNat_add]
      simp [Nat.shiftRight_eq_div_pow]
      omega
    · rfl
  case branch =>
    split
    · rfl
    · apply BitVec.eq_of_toNat_eq
      rw [append_toNat_add]
      simp [Nat.shiftRight_eq_div_pow]
      omega
  case readIndex =>
    rw [op_correct s i 0 (by decide)]
    simp
    have hpacked : s.request.toNat / 2^144 = 0xA710 ↔
        s.request.toNat / 2^148 = 0xA71 ∧ requestOpcode s = 0 := by
      unfold requestOpcode
      omega
    simp [hpacked, and_assoc]
    done
  done

theorem packedStatus_toNat (s : State) (i : Inputs) :
    (packedStatus.eval i.values s.values).toNat = statusNat i s := by
  simp [packedStatus, Expr.eval, Inputs.values, State.values, statusNat,
    Reactive.outputs, Reactive.outputLabel]
  repeat rw [append_toNat_add]
  simp only [BitVec.toNat_ofBool, Nat.reducePow]
  omega
  done

theorem responseCode_toNat (s : State) (i : Inputs) :
    (responseCode.eval i.values s.values).toNat =
      if s.code == 0 && s.rejected then 4 else s.code.toNat := by
  dsimp [responseCode, both, Expr.eval, State.values]
  simp +instances
  cases hr : s.rejected <;> by_cases hc : s.code = 0 <;> simp_all +instances
  done

theorem capturedResponse_correct (s : State) (i : Inputs) :
    capturedResponse.eval i.values s.values = s.capturedResponse i := by
  apply BitVec.eq_of_toNat_eq
  change (((0x5A1 : BitVec 12) ++ responseCode.eval i.values s.values) ++
    (s.sequence ++ ((0 : BitVec 5) ++ packedStatus.eval i.values s.values))).toNat = _
  repeat rw [append_toNat_add]
  rw [responseCode_toNat, packedStatus_toNat]
  dsimp [State.capturedResponse]
  have hp : statusNat i s < 2^155 := (packedStatus_toNat s i) ▸
    (packedStatus.eval i.values s.values).isLt
  have hc := (responseCode.eval i.values s.values).isLt
  rw [responseCode_toNat] at hc
  have hs := s.sequence.isLt
  simp only [BitVec.toNat_ofNat]
  cases hr : s.rejected <;> by_cases hz : s.code = 0 <;> simp_all +instances <;> omega
  done

private theorem fold_select (n x : Nat) (f : Nat → α) (base : α) :
    (List.finRange n).foldl (fun acc k => if x = k.val then f k.val else acc) base =
      if x < n then f x else base := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.finRange_succ_last, List.foldl_append, List.foldl_map]
    simp only [List.foldl_cons, List.foldl_nil, Fin.val_last, Fin.val_castSucc]
    rw [ih]
    by_cases he : x = n
    · subst x
      simp
    · by_cases hl : x < n
      · simp [he, hl, Nat.lt_succ_of_lt hl]
      · have hn : ¬x < n + 1 := by omega
        simp [he, hl, hn]
    done
  done

private theorem miso_fold (s : State) (i : Inputs) :
    ((List.finRange 192).foldl (fun acc k =>
      Expr.mux (.equal (.reg .count) (.lit (BitVec.ofNat 9 k.val)))
        (.slice (191-k.val) 1 (by omega) (.reg .response)) acc) (.lit 0)).eval
      i.values s.values =
    if s.count.toNat < 192 then s.response.extractLsb' (191-s.count.toNat) 1 else 0 := by
  rw [← List.foldl_hom (fun e : E 1 => e.eval i.values s.values)
    (g₂ := fun acc (k : Fin 192) => if s.count.toNat = k.val then
      s.response.extractLsb' (191-k.val) 1 else acc)]
  · exact fold_select 192 s.count.toNat (fun k => s.response.extractLsb' (191-k) 1) 0
  · intro x y
    have hy : y.val < 512 := Nat.lt_trans y.isLt (by decide)
    simp [Expr.eval, State.values, bitvec_eq_nat, Nat.mod_eq_of_lt hy]
  done

private theorem extract_one (x : BitVec n) (k : Nat) :
    x.extractLsb' k 1 = BitVec.ofBool (x.getLsbD k) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j
  simp [BitVec.getLsbD_extractLsb', BitVec.getLsbD_ofBool]
  intro h
  subst j
  simp
  done

theorem miso_correct (s : State) (i : Inputs) :
    miso.eval i.values s.values = s.miso i := by
  simp only [miso, Expr.eval]
  rw [miso_fold s i]
  simp [both, Expr.eval, Inputs.values, State.values, State.miso, Bool.and_assoc]
  cases i.cold <;> cases s.active <;> cases s.reading <;>
    by_cases hc : s.count.toNat < 192 <;> simp [hc, extract_one]
  done

theorem ready_correct (s : State) (i : Inputs) :
    circuit.observe i.values s.values .ready = s.readyOutput i := by
  cases hc : i.cold <;> cases hr : s.ready <;>
    simp [Circuit.observe, circuit, output, Expr.eval, State.values, Inputs.values, State.readyOutput, hc, hr]
  done

theorem State.step_values (s : State) (i : Inputs) :
    @State.values (s.step i) = @Circuit.step Input Register Output circuit i.values s.values := by
  funext w p
  cases p
  all_goals cases hc : i.cold
  all_goals simp [State.step, State.values, Circuit.step, circuit, next, nextUninitialized,
    Expr.eval, Inputs.values, starting, closing, closingRequest, closingReadExact,
    taking, receiving, both, closingCode_correct, capturedResponse_correct,
    delivering_correct, hc]
  all_goals try simp only [one_and, BitVec.ofBool_and_ofBool, ofBool_one, Bool.and_assoc, and_assoc,
    requestField_eq, request_shift]
  all_goals try simp only [Bool.and_eq_true, Bool.not_eq_true']
  case active.false =>
    cases hp : s.csnPrev <;> cases hc : i.csn <;> cases hk : i.sck <;>
      cases ha : s.active <;> cases hd : s.dispatch <;> cases hb : s.capture <;> simp_all
  case reading.false => split <;> rfl
  case count.false =>
    have hi : s.count + 1#9 = s.count - 511#9 := by bv_omega
    by_cases hn : s.count.toNat < 193
    all_goals simp only [hi, hn, and_true, and_false, ite_true, ite_false]
    all_goals first | rfl | simp
  case sequence.false =>
    by_cases hs : s.count = 160#9 <;> simp_all +instances
  case rejected.false =>
    cases hd : s.dispatch <;> cases hl : deliver i s <;> simp_all [ofBool_beq_one]
  case ready.false =>
    by_cases hs : s.count = 192#9
    all_goals cases hcap : s.capture <;> cases ha : s.active <;>
      cases hcs : i.csn <;> cases hr : s.reading <;> cases hready : s.ready <;> simp_all +instances
  done

def State.fromValues (r : Values Register) : State where
  sckPrev := r .sckPrev == 1
  csnPrev := r .csnPrev == 1
  active := r .active == 1
  reading := r .reading == 1
  count := r .count
  request := r .request
  dispatch := r .dispatch == 1
  capture := r .capture == 1
  code := r .code
  sequence := r .sequence
  rejected := r .rejected == 1
  response := r .response
  ready := r .ready == 1

theorem State.values_fromValues (r : Values Register) :
    @State.values (State.fromValues r) = @r := by
  funext w p
  cases p <;> simp [State.values, State.fromValues, ofBool_beq_one]
  done

def State.observe (s : State) (i : Inputs) : {w : Nat} → Output w → BitVec w
  | _, .core p => s.coreInput i p
  | _, .miso => s.miso i
  | _, .ready => s.readyOutput i

theorem State.observe_values (s : State) (i : Inputs) (o : Output w) :
    circuit.observe i.values s.values o = s.observe i o := by
  cases o
  · exact coreInput_correct s i _
  · exact miso_correct s i
  · exact ready_correct s i
  done

def State.run (s : State) (inputs : List Inputs) : State := inputs.foldl State.step s

def actualRun (r : Values Register) (inputs : List Inputs) : Values Register :=
  @List.foldl (Values Register) Inputs
    (fun bank i => fun {w} (p : Register w) => circuit.step i.values bank p) @r inputs

theorem State.run_values (s : State) (inputs : List Inputs) :
    @State.values (s.run inputs) = @actualRun s.values inputs := by
  induction inputs generalizing s with
  | nil => rfl
  | cons i rest ih =>
    change @State.values ((s.step i).run rest) = @actualRun (circuit.step i.values s.values) rest
    rw [← State.step_values]
    exact ih (s.step i)
  done

theorem initialized_run (r : Values Register) (cold : Inputs) (hc : cold.cold = true)
    (inputs : List Inputs) :
    @actualRun r (cold :: inputs) =
      @State.values (({sckPrev := cold.sck, csnPrev := cold.csn} : State).run inputs) := by
  have h := State.run_values (State.fromValues r) (cold :: inputs)
  rw [State.values_fromValues] at h
  simpa [State.run, State.step, hc] using h.symm
  done

end Pinwheel.Hardware.Buffered.Serial
