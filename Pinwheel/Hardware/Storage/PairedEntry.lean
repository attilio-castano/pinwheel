import Pinwheel.Hardware.Storage.PairedControl

/-! Entry into a certified instruction, including captures and terminal pins. -/
namespace Pinwheel.Hardware.Storage.PairedEntry
open Pinwheel.Hardware PairedController PairedRunning PairedBits PairedControl PairedE64
set_option backward.isDefEq.respectTransparency false

def view (s : Values Register) : Reactive.State :=
  ⟨s .mode, if s .mode != 0 && (s .mode).toNat < 5 then PairedImage.row (s .current) else 0,
    s .remaining, s .waitLeft, ⟨s .levels, s .enabled⟩, samples (s .samples)⟩

def value (idle : Engine.Reactive.Pins) (slots : Reactive.Samples) (incoming : BitVec 2)
    (word : BitVec 32) (parameter : BitVec 20) : Reactive.State :=
  let k := word.extractLsb' 0 3
  if k = 4 then ⟨5, 0, 0, 0, idle, slots⟩
  else if k = 7 then ⟨7, 0, 0, 0, idle, slots⟩
  else ⟨k - 7, PairedImage.row word, word.extractLsb' 9 8,
    if k = 3 then parameter.extractLsb' 0 8 else 0,
    ⟨word.extractLsb' 3 3, word.extractLsb' 6 3⟩,
    if k = 0 ∨ k = 2 then Engine.Reactive.capture slots
      (Execution.getCapture (parameter.extractLsb' 0 6)) incoming else slots⟩

theorem value_matches (p : Execution.Image) (image : PairedImage.Image)
    (node : PairedImage.Node) (word : BitVec 32) (parameter : BitVec 20)
    (hm : PairedImage.Matches p image node word)
    (hp : parameter = image.parameters[(PairedImage.index word).toNat])
    (slots : Reactive.Samples) (incoming : BitVec 2) :
    value p.idle slots incoming word parameter = Reactive.embed (enterNode p node slots incoming) := by
  cases node with
  | none => simp_all [PairedImage.Matches, value, enterNode, Engine.Reactive.stop, Reactive.embed, Reactive.stopMode]
  | some pc =>
    by_cases hk : (PairedImage.fields p pc).kind = 4
    case neg =>
      simp only [PairedImage.Matches, hk, if_false] at hm
      have hw := token_fields word (PairedImage.fields p pc) hm.2.2.2.2.1
      simp only [value, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2, hp.trans hm.2.2.2.2.2,
        hm.2.2.1, enterNode]
      cases ho : p.fetch pc.toFin
      case checked a =>
        cases hf : a.finish <;> simp [PairedImage.fields, ho, Execution.fields,
          Execution.finishFields, Execution.actionFields, hf, Engine.Reactive.enter, Reactive.embed]
        all_goals simp [parameter_captures, Execution.capture_roundtrip]
      all_goals simp [PairedImage.fields, ho, Execution.fields, Execution.actionFields,
        Engine.Reactive.enter, Reactive.embed, parameter_captures, parameter_budget,
        Execution.capture_roundtrip] at hk ⊢
    case pos =>
      cases ho : p.fetch pc.toFin
      case checked a =>
        cases hf : a.finish <;> simp [PairedImage.fields, ho, Execution.fields,
          Execution.finishFields, Execution.actionFields, hf] at hk
      all_goals simp_all [PairedImage.fields, Execution.fields, Execution.actionFields,
        PairedImage.Matches, value, enterNode, Engine.Reactive.enter, Engine.Reactive.stop,
        Reactive.embed, Reactive.stopMode]

theorem graph_value (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s)
    (hr : resetting.eval g s = 0) (hc : commit.eval g s = 0)
    (hd : ending.eval g s = 0) (he : entering.eval g s = 1)
    (hk : ((entered.eval g s).extractLsb' 0 3).toNat < 4 ∨
      (entered.eval g s).extractLsb' 0 3 = 4 ∨ (entered.eval g s).extractLsb' 0 3 = 7) :
    view (body.step g s) =
      value ⟨(idleWord.eval g s).extractLsb' 0 3, (idleWord.eval g s).extractLsb' 3 3⟩
        (samples (entrySamples.eval g s)) (g (.base .incoming)) (entered.eval g s) (parameter0.eval g s) := by
  have codes : (entered.eval g s).extractLsb' 0 3 = 0 ∨
      (entered.eval g s).extractLsb' 0 3 = 1 ∨ (entered.eval g s).extractLsb' 0 3 = 2 ∨
      (entered.eval g s).extractLsb' 0 3 = 3 ∨ (entered.eval g s).extractLsb' 0 3 = 4 ∨
      (entered.eval g s).extractLsb' 0 3 = 7 := by bv_omega
  rcases codes with hcode | hcode | hcode | hcode | hcode | hcode <;>
    simp [view, value, Circuit.step, body, PairedController.next, nextMode_wire g s h,
      nextModeExpr, nextWord_wire g s h, nextWordExpr, enteringRun_wire g s h,
      enteringRunExpr, stopping_wire g s h, stoppingExpr, captured_wire g s h,
      capturedExpr, entryLevels_wire g s h, entryLevelsExpr, terminal, isKind, kind,
      duration, both, either, Expr.eval, hr, hc, hd, he, hcode, capture_samples,
      incoming_value g s h, PairedImage.row]
  done

private theorem fields_kind_bound (op : Execution.Operation) : (Execution.fields op).kind.toNat ≤ 4 := by
  cases op with
  | checked a => cases hf : a.finish <;> simp [Execution.fields, Execution.finishFields, Execution.actionFields, hf]
  | _ => simp [Execution.fields, Execution.actionFields]

theorem matches_kind (p : Execution.Image) (image : PairedImage.Image)
    (node : PairedImage.Node) (word : BitVec 32) (hm : PairedImage.Matches p image node word) :
    (word.extractLsb' 0 3).toNat < 4 ∨ word.extractLsb' 0 3 = 4 ∨ word.extractLsb' 0 3 = 7 := by
  cases node with
  | none => simp_all [PairedImage.Matches]
  | some pc =>
    by_cases hk : (PairedImage.fields p pc).kind = 4
    case pos => simp_all [PairedImage.Matches]
    case neg =>
      simp only [PairedImage.Matches, hk, if_false] at hm
      have hw := (token_fields word (PairedImage.fields p pc) hm.2.2.2.2.1).1
      have bound : (PairedImage.fields p pc).kind.toNat ≤ 4 := fields_kind_bound (p.fetch pc.toFin)
      bv_omega
      done

theorem decrement_graph (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s)
    (hr : resetting.eval g s = 0) (hc : commit.eval g s = 0)
    (hd : ending.eval g s = 0) (he : entering.eval g s = 0)
    (hm : s .mode = 1 ∨ s .mode = 2 ∨ s .mode = 3) :
    view (body.step g s) = {view s with remaining := s .remaining - 1} := by
  rcases hm with hm | hm | hm <;>
    simp [view, Circuit.step, body, PairedController.next, nextMode_wire g s h,
      nextModeExpr, nextWord_wire g s h, nextWordExpr, enteringRun_wire g s h,
      enteringRunExpr, stopping_wire g s h, stoppingExpr, busy_wire g s h,
      busyExpr, both, either, isMode, Expr.eval, hr, hc, hd, he, hm]

theorem qualify_graph (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s)
    (hr : resetting.eval g s = 0) (hc : commit.eval g s = 0)
    (hd : ending.eval g s = 0) (he : entering.eval g s = 0) (hm : s .mode = 4) :
    view (body.step g s) =
      if guarded.eval g s = 1 then
        {view s with remaining := s .remaining - 1, waitLeft := (s .cached).extractLsb' 0 8}
      else {view s with remaining := (s .current).extractLsb' 9 8, waitLeft := s .waitLeft - 1} := by
  rcases PairedUpload.bit_cases (guarded.eval g s) with hg | hg <;>
    simp [view, Circuit.step, body, PairedController.next, nextMode_wire g s h,
      nextModeExpr, nextWord_wire g s h, nextWordExpr, enteringRun_wire g s h,
      enteringRunExpr, stopping_wire g s h, stoppingExpr, busy_wire g s h,
      busyExpr, both, either, isMode, duration, Expr.eval, hr, hc, hd, he, hm, hg]

theorem stopped_graph (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s)
    (hr : resetting.eval g s = 0) (hc : commit.eval g s = 0)
    (hd : ending.eval g s = 0) (he : entering.eval g s = 0) (hb : busy.eval g s = 0) :
    view (body.step g s) = view s := by
  simp [view, Circuit.step, body, PairedController.next, nextMode_wire g s h,
    nextModeExpr, nextWord_wire g s h, nextWordExpr, enteringRun_wire g s h,
    enteringRunExpr, stopping_wire g s h, stoppingExpr, both, either,
    Expr.eval, hr, hc, hd, he, hb]

theorem ending_graph (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s)
    (hr : resetting.eval g s = 0) (hc : commit.eval g s = 0)
    (hd : ending.eval g s = 1) (he : entering.eval g s = 0) :
    view (body.step g s) =
      ⟨if fault.eval g s = 1 then 7 else 6, 0, 0, 0,
        ⟨(idleWord.eval g s).extractLsb' 0 3, (idleWord.eval g s).extractLsb' 3 3⟩,
        samples (s .samples)⟩ := by
  rcases PairedUpload.bit_cases (fault.eval g s) with hf | hf <;>
    simp [view, Circuit.step, body, PairedController.next, nextMode_wire g s h,
      nextModeExpr, stopping_wire g s h,
      stoppingExpr, both, either, Expr.eval, hr, hc, hd, he, hf]

theorem reset_graph (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s) (hr : resetting.eval g s = 1) :
    view (body.step g s) =
      ⟨0, 0, 0, 0, ⟨(idleWord.eval g s).extractLsb' 0 3,
        (idleWord.eval g s).extractLsb' 3 3⟩, Vector.replicate 16 false⟩ := by
  rcases PairedUpload.bit_cases (commit.eval g s) with hc | hc <;>
    simp [view, Circuit.step, body, PairedController.next, nextMode_wire g s h,
      nextModeExpr, stopping_wire g s h,
      stoppingExpr, both, either, Expr.eval, hr, hc]
  all_goals exact samples_zero

end Pinwheel.Hardware.Storage.PairedEntry
