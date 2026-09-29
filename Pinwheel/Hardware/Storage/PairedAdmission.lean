import Pinwheel.Hardware.Storage.PairedHost
import Pinwheel.Hardware.Loader.Upload

/-! A certified paired upload is accepted by the actual controller. Admission
reads the parameter table already installed by the first 32 accepted words;
neither the validation decision nor the staged transcript is a premise. -/
namespace Pinwheel.Hardware.Storage.PairedAdmission
open Pinwheel.Hardware PairedController PairedUpload PairedRunning PairedControl
open PairedCoverage (Tracked graphInputs advance graph_equations)
open Pinwheel.Hardware.Loader.Machine (Quiet Carries Delivers)
set_option backward.isDefEq.respectTransparency false

theorem token_matches (p : Execution.Image) (image : PairedImage.Image)
    (node : PairedImage.Node) (word : E 32) (parameter : E 20)
    (g : Values GraphInput) (s : Values Register)
    (hm : PairedImage.Matches p image node (word.eval g s))
    (hp : parameter.eval g s = image.parameters[(PairedImage.index (word.eval g s)).toNat]) :
    (tokenValid word parameter).eval g s = 1 := by
  cases node with
  | none =>
    simp_all [PairedImage.Matches, tokenValid, terminal, isKind, kind, both, either, Expr.eval]
  | some pc =>
    by_cases hk : (PairedImage.fields p pc).kind = 4
    case pos =>
      simp_all [PairedImage.Matches, tokenValid, terminal, isKind, kind, both, either, Expr.eval]
    case neg =>
      simp only [PairedImage.Matches, hk, if_false] at hm
      have hw := (PairedE64.token_fields (word.eval g s) (PairedImage.fields p pc) hm.2.2.2.2.1).1
      simp only [tokenValid, both, either, terminal, isKind, kind, allowed, captureValid,
        Expr.eval, hw, hm.2.2.2.1, hp.trans hm.2.2.2.2.2,
        decide_true, BitVec.ofBool_true]
      cases ho : p.fetch pc.toFin
      case checked a =>
        cases hf : a.finish <;> simp [PairedImage.fields, ho, PairedImage.parameter,
          Execution.fields, Execution.finishFields, Execution.actionFields, hf]
        all_goals cases he : a.action.capture <;> cases ht : a.terminalCapture <;>
          simp only [Execution.captureBits]
        all_goals bv_normalize
        all_goals done
      all_goals simp [PairedImage.fields, ho, PairedImage.parameter,
        Execution.fields, Execution.actionFields] at hk ⊢
      case action a =>
        rw [show 1048512#20 = (16383#14) ++ (0#6) from rfl,
          BitVec.and_append]
        cases he : a.capture <;> simp only [Execution.captureBits]
        all_goals bv_normalize
        all_goals done
      case wait w =>
        rw [show 1036287#20 = (15#4) ++ ((3#2) ++ (0#1) ++ (0#1)) ++ (63#6) ++ (63#6) from rfl,
          BitVec.and_append, BitVec.and_append, BitVec.and_append, BitVec.and_append, BitVec.and_append]
        bv_normalize
        done
      case qualify q =>
        rw [show 986880#20 = (15#4) ++ (0#4) ++ (15#4) ++ (0#8) from rfl,
          BitVec.and_append, BitVec.and_append, BitVec.and_append]
        bv_normalize
        done

theorem row_admitted (p : Execution.Image) (image : PairedImage.Image)
    (hc : PairedImage.Corresponds p image) (k : BitVec 8) (choice : Bool)
    (word : E 32) (parameter : E 20) (g : Values GraphInput) (s : Values Register)
    (hw : word.eval g s = PairedImage.select image.rows[k.toNat] choice)
    (hp : parameter.eval g s = image.parameters[(PairedImage.index (word.eval g s)).toNat]) :
    (tokenValid word parameter).eval g s = 1 := by
  by_cases hk : k.toNat ≤ p.last.val
  case pos =>
    exact token_matches p image (PairedImage.successor p k choice) word parameter g s
      (by simpa only [if_pos hk, ← hw] using hc.2.2 k choice) hp
  case neg =>
    have ht : word.eval g s = 4 := hw.trans (by simpa only [if_neg hk] using hc.2.2 k choice)
    simp [tokenValid, terminal, isKind, kind, both, either, Expr.eval, ht]
    done

theorem validation_parameters (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s) (hv : validatingExpr.eval g s = 1) :
    parameter0.eval g s = s (.parameter (!(s .active == 1)) ((data.eval g s).extractLsb' 17 5)) ∧
    parameter1.eval g s = s (.parameter (!(s .active == 1)) ((data.eval g s).extractLsb' 49 5)) := by
  have hr := PairedValidation.validation_reads_match g s (PairedSemantics.upstream_equations g s h) hv
  rcases bit_cases (s .active) with ha | ha <;>
    simpa [PairedValidation.validationLookup, Expr.eval, Execution.readTree_correct,
      inactive_value g s h, ha] using hr
  done

theorem upload_parameter (image : PairedImage.Image) (k : BitVec 5) :
    (PairedImage.upload image).getD k.toNat 0 = image.parameters[k.toNat].zeroExtend 64 := by
  simp [PairedImage.upload, List.getElem?_append, show k.toNat < 32 from k.isLt]

theorem upload_row (image : PairedImage.Image) (k : BitVec 8) :
    (PairedImage.upload image).getD (32 + k.toNat) 0 = image.rows[k.toNat] := by
  simp [PairedImage.upload, List.getElem?_append, show ¬32 + k.toNat < 32 from by omega,
    show k.toNat < 256 from k.isLt]

theorem upload_boot (image : PairedImage.Image) :
    (PairedImage.upload image).getD 288 0 = image.boot.zeroExtend 64 := by
  simp [PairedImage.upload]

theorem upload_idle (image : PairedImage.Image) :
    (PairedImage.upload image).getD 289 0 = image.idle.zeroExtend 64 := by
  simp [PairedImage.upload]

private theorem high_index (word : BitVec 64) :
    (word.extractLsb' 32 32).extractLsb' 17 5 = word.extractLsb' 49 5 := by
  apply BitVec.eq_of_getElem_eq
  exact fun i hi => by simp [BitVec.getElem_extractLsb', show 17 + i < 32 from by omega, ← Nat.add_assoc]
  done

private theorem high_zero (word : BitVec w) (n : Nat) : word.extractLsb' w n = 0 := by
  apply BitVec.eq_of_getElem_eq
  exact fun i hi => by simp [BitVec.getElem_extractLsb']
  done

theorem word_good (p : Execution.Image) (image : PairedImage.Image)
    (hc : PairedImage.Corresponds p image) (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s) (ha : accepting.eval g s = 1)
    (hcmd : g (.base .command) = 2) (hp : s .pending = 1) (hb : (s .cursor).toNat < 290)
    (hw : data.eval g s = (PairedImage.upload image).getD (s .cursor).toNat 0)
    (ht : 32 ≤ (s .cursor).toNat → ∀ k, s (.parameter (!(s .active == 1)) k) = image.parameters[k.toNat]) :
    good.eval g s = 1 := by
  rw [(PairedSemantics.upstream_equations g s h).good]
  by_cases hlo : (s .cursor).toNat < 32
  case pos =>
    have hd : data.eval g s = image.parameters[(BitVec.ofNat 5 (s .cursor).toNat).toNat].zeroExtend 64 :=
      hw.trans (by simpa only [BitVec.toNat_ofNat, Nat.reducePow, Nat.mod_eq_of_lt hlo]
        using upload_parameter image (BitVec.ofNat 5 (s .cursor).toNat))
    simp [goodExpr, below, Expr.eval, hlo, hd, BitVec.extractLsb'_setWidth_of_le]
    exact high_zero _ _
    done
  case neg =>
    by_cases hhi : (s .cursor).toNat < 289
    case neg =>
      have hcurs : s .cursor = 289 := by bv_omega
      have hd : data.eval g s = image.idle.zeroExtend 64 :=
        hw.trans (by simpa only [hcurs, BitVec.reduceToNat] using upload_idle image)
      simp [goodExpr, below, atCursor, both, Expr.eval, hcurs, hd,
        BitVec.extractLsb'_setWidth_of_le, high_zero]
      done
    case pos =>
      have hv : validatingExpr.eval g s = 1 := by
        simp [validatingExpr, both, cmd, below, Expr.eval, ha, hcmd, hp, hlo, hhi]
      have hp0 := (validation_parameters g s h hv).1.trans (ht (by omega) _)
      have hp1 := (validation_parameters g s h hv).2.trans (ht (by omega) _)
      by_cases hrow : (s .cursor).toNat < 288
      case neg =>
        have hcurs : s .cursor = 288 := by bv_omega
        have hd : data.eval g s = image.boot.zeroExtend 64 :=
          hw.trans (by simpa only [hcurs, BitVec.reduceToNat] using upload_boot image)
        have low := token_matches p image (some 0) (.slice 0 32 (by decide) data) parameter0 g s
          (by simpa only [Expr.eval, hd, BitVec.extractLsb'_setWidth_of_le (by decide : 0 + 32 ≤ 64),
            BitVec.extractLsb'_eq_self] using hc.1)
          (by simpa (disch := omega) only [PairedImage.index, Expr.eval,
            BitVec.extractLsb'_extractLsb'_of_le] using hp0)
        simp only [goodExpr, below, atCursor, Expr.eval, hcurs, BitVec.reduceToNat,
          Nat.reduceLT, decide_false, decide_true, BitVec.ofBool_false, BitVec.ofBool_true,
          BitVec.reduceEq, if_false, if_true, both, Expr.eval, low, hd,
          BitVec.extractLsb'_setWidth_of_le (by decide : 32 + 32 ≤ 64), high_zero, BitVec.reduceAnd]
        done
      case pos =>
        let k : BitVec 8 := BitVec.ofNat 8 ((s .cursor).toNat - 32)
        have hk : 32 + k.toNat = (s .cursor).toNat := by
          simp only [k, BitVec.toNat_ofNat, Nat.reducePow]
          omega
        have hd : data.eval g s = image.rows[k.toNat] :=
          hw.trans (by simpa only [hk] using upload_row image k)
        have low := row_admitted p image hc k false (.slice 0 32 (by decide) data) parameter0 g s
          (by simp [Expr.eval, PairedImage.select, hd])
          (by simpa (disch := omega) only [PairedImage.index, Expr.eval, BitVec.extractLsb'_extractLsb'_of_le] using hp0)
        have high := row_admitted p image hc k true (.slice 32 32 (by decide) data) parameter1 g s
          (by simp [Expr.eval, PairedImage.select, hd])
          (by simpa only [PairedImage.index, Expr.eval, high_index] using hp1)
        simp only [goodExpr, below, Expr.eval, BitVec.reduceToNat, hlo, hrow,
          decide_false, decide_true, BitVec.ofBool_false, BitVec.ofBool_true,
          BitVec.reduceEq, if_false, if_true, both, Expr.eval, low, high, BitVec.reduceAnd]
        done

end Pinwheel.Hardware.Storage.PairedAdmission
