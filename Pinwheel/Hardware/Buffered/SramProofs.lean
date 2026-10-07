import Pinwheel.Hardware.Buffered.Sram

/-! Digital scheduling laws for the actual typed buffered SRAM controller.
The address substitution, upload ports and row-zero mirror are the expressions
used by emission. Array response laws compose them with `Memory.Sram`.
These are local controller/array laws, not a complete upload/core trace
refinement or physical macro/address-path qualification. -/
namespace Pinwheel.Hardware.Buffered.Sram
open Pinwheel.Hardware

/-- Requests are computed from both forced branch arms of the actual post-edge
core register update, including counted loop and newly loaded branch caches. -/
theorem readAddress_correct (b : Bool) (i : Values Input) (s : Values Register) :
    (readAddress b).eval i s =
      ((SramCandidates.candidate b).eval (fun _ => 0)
        (fun r => circuit.step i s (.core r))).extractLsb' 0 6 := by
  cases b <;> simp only [readAddress, readAddressFalse, readAddressTrue,
    Bool.false_eq_true, ↓reduceIte, Expr.eval, MemoBind.eval_bind]
  all_goals rfl
  done

/-- Input-free candidate scheduling permits any input valuation when reading
the materialized actual prospective core state. -/
theorem readAddress_postcore (b : Bool) (i : Values Input) (s : Values Register)
    (j : Values Reactive.Input) :
    (readAddress b).eval i s =
      ((SramCandidates.candidate b).eval j
        (fun r => circuit.step i s (.core r))).extractLsb' 0 6 :=
  (readAddress_correct b i s).trans
    (congrArg (fun word : BitVec 7 => word.extractLsb' 0 6)
      (SramCandidates.candidate_input_independent b (fun _ => 0) j
        (fun r => circuit.step i s (.core r))))

private theorem zero_ne_one : (0 : BitVec 1) ≠ 1 := by decide +kernel

private theorem band_zero_left : ∀ a : BitVec 1, 0 &&& a = 0 := by decide +kernel

private theorem band_ones : (1 : BitVec 1) &&& 1 = 1 := by decide +kernel

/-- Actual port selection on a read edge is exactly the prospective candidate
address, rather than an unconstrained address from a second scheduler. -/
theorem request_address_read (b : Bool) (i : Values Input) (s : Values Register)
    (hw : (request .write).eval i s = 0) :
    (request (.address b)).eval i s = (readAddress b).eval i s := by
  simp only [request] at hw ⊢
  simp only [Expr.eval, hw, zero_ne_one, ↓reduceIte]
  done

/-- Accepted row uploads drive the same write address on both macro ports. -/
theorem request_address_write (b : Bool) (i : Values Input) (s : Values Register)
    (hw : (request .write).eval i s = 1) :
    (request (.address b)).eval i s = i (.base .address) := by
  simp only [request] at hw ⊢
  simp only [Expr.eval, hw, ↓reduceIte]
  done

/-- The actual typed enables are mutually exclusive on every represented
state, not just admitted or running states. -/
theorem request_read_write_exclusive (i : Values Input) (s : Values Register) :
    (request .read).eval i s = ~~~(request .write).eval i s := rfl

private theorem single_access : ∀ write : BitVec 1,
    write.toNat + (~~~write).toNat = 1 := by decide +kernel

/-- Each actual macro has exactly one enabled access on every represented edge. -/
theorem request_one_access (i : Values Input) (s : Values Register) :
    ((request .write).eval i s).toNat + ((request .read).eval i s).toNat = 1 := by
  rw [request_read_write_exclusive]
  exact single_access _
  done

/-- The row-zero instruction mirror tracks exactly an accepted full-word row
zero upload. Metadata and dictionary identity are established separately. -/
theorem start_mirror_write (i : Values Input) (s : Values Register)
    (hw : (request .write).eval i s = 1) (ha : i (.base .address) = 0) :
    circuit.step i s .startWord = i (.base .word) := by
  simp only [request] at hw
  simp only [Circuit.step, circuit, next, Expr.eval, hw, ha, decide_true,
    BitVec.ofBool_true, band_ones, ↓reduceIte]
  done

/-- Every nonwrite edge retains the mirror, including immediate COMMIT/START
and rejected writes while a transfer owns the image. -/
theorem start_mirror_nonwrite (i : Values Input) (s : Values Register)
    (hw : (request .write).eval i s = 0) :
    circuit.step i s .startWord = s .startWord := by
  simp only [request] at hw
  simp only [Circuit.step, circuit, next, Expr.eval, hw, band_zero_left, zero_ne_one,
    ↓reduceIte]
  done

/-- START uses its row-zero mirror, regardless of both stale macro responses. -/
theorem instruction_start (i : Values Input) (s : Values Register)
    (hs : starting.eval i s = 1) : instruction.eval i s = s .startWord := by
  simp only [instruction, Expr.eval, hs, ↓reduceIte]
  done

/-- The actual controller ports interpreted as a replicated single-port macro
request. This is a digital interpretation of the typed output expressions. -/
def arrayRequest (i : Values Input) (s : Values Register) : Memory.Request 6 64 2 :=
  ⟨⟨decide ((request .write).eval i s = 1),
    (request (.address false)).eval i s, (request .data).eval i s⟩,
    fun port => (request (.address (decide (port = 1)))).eval i s⟩

/-- On every actual nonwrite edge, Q receives the word requested by the actual
prospective-core address expression. -/
theorem array_response_read (i : Values Input) (s : Values Register)
    (arrays : Fin 2 → Memory.Sram.State 6 64)
    (hw : (request .write).eval i s = 0) (port : Fin 2) :
    (Memory.Sram.step (arrayRequest i s) arrays port).q =
      (arrays port).contents ((readAddress (decide (port = 1))).eval i s) := by
  simp only [Memory.Sram.step, Memory.Sram.State.step, arrayRequest, hw,
    zero_ne_one, decide_false]
  simp only [Bool.false_eq_true, ↓reduceIte,
    request_address_read (decide (port = 1)) i s hw]
  done

/-- The actual nonwrite request leaves every stored instruction untouched. -/
theorem array_read_preserves_bank (i : Values Input) (s : Values Register)
    (arrays : Fin 2 → Memory.Sram.State 6 64)
    (hw : (request .write).eval i s = 0) (port : Fin 2) :
    (Memory.Sram.step (arrayRequest i s) arrays port).contents = (arrays port).contents :=
  Memory.write_disabled (arrays port).contents (arrayRequest i s).write
    (by simp only [arrayRequest, hw, zero_ne_one, decide_false])

/-- An accepted upload delivers the actual data port to both SRAM replicas. -/
theorem array_write_broadcast (i : Values Input) (s : Values Register)
    (arrays : Fin 2 → Memory.Sram.State 6 64)
    (hw : (request .write).eval i s = 1) (port : Fin 2) :
    (Memory.Sram.step (arrayRequest i s) arrays port).contents (i (.base .address)) =
      i (.base .word) := by
  have hb := Memory.Sram.broadcast_write (arrayRequest i s) arrays
    (by simp only [arrayRequest, hw, decide_true]) port
  change (Memory.Sram.step (arrayRequest i s) arrays port).contents
    ((request (.address false)).eval i s) = (request .data).eval i s at hb
  rw [request_address_write false i s hw] at hb
  exact hb
  done

/-- Actual upload edges hold Q in both replicated single-port macros. -/
theorem array_write_holds_q (i : Values Input) (s : Values Register)
    (arrays : Fin 2 → Memory.Sram.State 6 64)
    (hw : (request .write).eval i s = 1) (port : Fin 2) :
    (Memory.Sram.step (arrayRequest i s) arrays port).q = (arrays port).q := by
  simp only [Memory.Sram.step, Memory.Sram.State.step, arrayRequest, hw,
    decide_true, ↓reduceIte]
  done

/-- The candidate response invariant renews through the actual emitted request
ports whenever resident/live instruction words agree with both macro copies.
Connecting this premise to loader coverage is a separate controller obligation. -/
theorem actual_candidate_availability (i : Values Input) (s : Values Register)
    (arrays : Fin 2 → Memory.Sram.State 6 64)
    (contents : Memory.Contents 6 64) (live : BitVec 6 → Bool)
    (hw : (request .write).eval i s = 0)
    (hbank : ∀ port k, live k = true → (arrays port).contents k = contents k) :
    SramCandidates.Ready (Memory.Sram.step (arrayRequest i s) arrays) contents live
      (fun port => (readAddress (decide (port = 1))).eval i s) := by
  intro port
  cases hl : live ((readAddress (decide (port = 1))).eval i s) <;>
    simp [SramCandidates.project, array_response_read i s arrays hw port, hl,
      hbank port ((readAddress (decide (port = 1))).eval i s)]
  done

private theorem widened_index (k : BitVec 6) :
    (BitVec.ofNat 7 k.toNat).toNat = k.toNat := by
  simp only [BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (Nat.lt_trans k.isLt (by decide +kernel : 2^6 < 2^7))]
  done

/-- The compact tail is projected to all-zero before dictionary expansion.
This hides stale instruction Q and resets the branch reference itself. -/
theorem rowExpr_tail (k : BitVec 6) (i : Values Input) (s : Values Register)
    (ht : (s (.core .count)).toNat ≤ k.toNat) : (rowExpr k).eval i s = 0 := by
  simp only [rowExpr, Expr.eval, widened_index, Nat.not_lt.mpr ht, decide_false,
    BitVec.ofBool_false, zero_ne_one, ↓reduceIte]
  done

/-- Within the resident count, row assembly uses exactly the FF metadata and
the current selected SRAM/mirror instruction. -/
theorem rowExpr_live (k : BitVec 6) (i : Values Input) (s : Values Register)
    (hl : k.toNat < (s (.core .count)).toNat) :
    (rowExpr k).eval i s = s (.metadata k) ++ instruction.eval i s := by
  simp only [rowExpr, Expr.eval, widened_index, hl, decide_true,
    BitVec.ofBool_true, ↓reduceIte]
  done

end Pinwheel.Hardware.Buffered.Sram
