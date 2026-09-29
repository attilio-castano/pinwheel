import Pinwheel.Hardware.Storage.PairedBits

/-! The canonical source fields seen by the retained paired datapath. -/
namespace Pinwheel.Hardware.Storage.PairedE64
open Pinwheel.Hardware PairedController PairedBits
set_option backward.isDefEq.respectTransparency false

theorem running_parts (p : Execution.Image) (image : PairedImage.Image)
    (pc : BitVec 8) (word : BitVec 32) (h : PairedImage.Matches p image (some pc) word)
    (ht : PairedImage.terminal word = false) :
    word.extractLsb' 0 17 = (PairedImage.fields p pc).duration ++
      (PairedImage.fields p pc).enabled ++ (PairedImage.fields p pc).levels ++
      (PairedImage.fields p pc).kind ∧
    image.parameters[(PairedImage.index word).toNat] = PairedImage.parameter (PairedImage.fields p pc) := by
  by_cases hk : (PairedImage.fields p pc).kind = 4
  case pos => simp_all [PairedImage.Matches, PairedImage.terminal]
  case neg =>
    simp only [PairedImage.Matches, hk, if_false] at h
    exact h.2.2.2.2
    done

theorem token_fields (word : BitVec 32) (f : Execution.Fields)
    (h : word.extractLsb' 0 17 = f.duration ++ f.enabled ++ f.levels ++ f.kind) :
    word.extractLsb' 0 3 = f.kind ∧ word.extractLsb' 3 3 = f.levels ∧
    word.extractLsb' 6 3 = f.enabled ∧ word.extractLsb' 9 8 = f.duration := by
  have hh := congrArg (fun v : BitVec 17 =>
    (v.extractLsb' 0 3, v.extractLsb' 3 3, v.extractLsb' 6 3, v.extractLsb' 9 8)) h
  simp (disch := omega) only [BitVec.extractLsb'_extractLsb'_of_le, Prod.mk.injEq] at hh
  bv_normalize
  done

theorem parameter_checked (a : Engine.Reactive.Checked 255 15) :
    let f := Execution.fields (.checked a)
    (PairedImage.parameter f).extractLsb' 6 6 = Execution.captureBits a.terminalCapture ∧
    (PairedImage.parameter f).extractLsb' 16 4 = f.sample ∧
    (PairedImage.parameter f).extractLsb' 12 4 = Execution.checkBits a.guard := by
  cases hf : a.finish <;> simp only [PairedImage.parameter, Execution.fields,
    Execution.finishFields, Execution.actionFields, hf, BitVec.reduceEq, if_false]
  all_goals bv_normalize
  done

theorem parameter_check (f : Execution.Fields) :
    (PairedImage.parameter f).extractLsb' 12 4 = f.check := by
  by_cases hk : f.kind = 3 <;> simp only [PairedImage.parameter, hk, if_true, if_false]
  all_goals bv_normalize

theorem parameter_captures (f : Execution.Fields) (hk : f.kind ≠ 3) :
    (PairedImage.parameter f).extractLsb' 0 6 = f.entry ∧
    (PairedImage.parameter f).extractLsb' 6 6 = f.terminal ∧
    (PairedImage.parameter f).extractLsb' 16 4 = f.sample := by
  simp only [PairedImage.parameter, hk, if_false]
  bv_normalize

theorem parameter_budget (f : Execution.Fields) (hk : f.kind = 3) :
    (PairedImage.parameter f).extractLsb' 0 8 = f.budget := by
  simp only [PairedImage.parameter, hk, if_true]
  bv_normalize

theorem checked_branch (a : Engine.Reactive.Checked 255 15)
    (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s) (hm : s .mode = 3)
    (hp : s .cached = PairedImage.parameter (Execution.fields (.checked a))) :
    branch.eval g s = BitVec.ofBool
      (Engine.Reactive.capture (samples (s .samples)) a.terminalCapture
        (g (.base .incoming)))[(Execution.fields (.checked a)).sample.toNat] := by
  simp only [branch_capture g s h hm, hp, (parameter_checked a).1,
    (parameter_checked a).2.1, Execution.capture_roundtrip]

def enterNode (p : Execution.Image) (node : PairedImage.Node) (slots : Reactive.Samples)
    (incoming : BitVec 2) : Reactive.Model :=
  match node with
  | none => Engine.Reactive.stop p .fault slots
  | some pc => Engine.Reactive.enter p pc.toFin slots incoming

theorem sequential_node (p : Execution.Image) (pc : BitVec 8)
    (slots : Reactive.Samples) (incoming : BitVec 2) :
    enterNode p (if pc.toNat + 1 ≤ p.last.val then some (BitVec.ofNat 8 (pc.toNat + 1)) else none)
      slots incoming = Engine.Reactive.next p pc.toFin slots incoming := by
  by_cases hb : pc.toNat < p.last.val
  case pos =>
    have bound : pc.toNat + 1 < 256 := by have := p.last.isLt; omega
    simp [enterNode, Engine.Reactive.next, hb, show pc.toNat + 1 ≤ p.last.val from by omega]
    exact congrArg (fun address => Engine.Reactive.enter p address slots incoming)
      (Fin.ext (Nat.mod_eq_of_lt bound))
    done
  case neg => simp [enterNode, Engine.Reactive.next, hb, show ¬pc.toNat + 1 ≤ p.last.val from by omega]

theorem checked_successor (p : Execution.Image) (pc : BitVec 8)
    (a : Engine.Reactive.Checked 255 15) (ha : p.fetch pc.toFin = .checked a)
    (slots : Reactive.Samples) (incoming : BitVec 2) :
    enterNode p (PairedImage.successor p pc slots[(Execution.fields (.checked a)).sample.toNat])
      slots incoming = Engine.Reactive.dispatch p pc.toFin a.finish slots incoming := by
  cases hf : a.finish <;> simp only [PairedImage.successor, PairedImage.fields, ha,
    Execution.fields, Execution.finishFields, Execution.actionFields, hf,
    BitVec.reduceEq, and_true, and_false, if_true, if_false,
    Engine.Reactive.dispatch, sequential_node, BitVec.toNat_ofFin]
  case branch sample yes no =>
    cases slots[sample.val] <;> simp only [Bool.false_eq_true, if_false, if_true, BitVec.toNat_ofFin]
    all_goals simp [Engine.Reactive.jump, apply_ite, enterNode]
    all_goals split <;> simp_all
  case jump target =>
    by_cases ht : target.val ≤ p.last.val <;> simp [enterNode, Engine.Reactive.jump, ht]

end Pinwheel.Hardware.Storage.PairedE64
