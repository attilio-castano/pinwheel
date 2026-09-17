"""Checked decomposition for bank-selection and cache-enable experiment variants.

Only proof generation changes. The restricted RTL importer and local-equality
checker are shared with the original backend; every generated hint is proved.
"""
import re

import backend_readback as rb


VARIANTS = ("composed", "command-split", "late-bank", "enable-split")


def read_cuts(path, source, variant):
    expected = [("address", 8), ("selection", 1)]
    expected += ([("index0", 6), ("word0", 64), ("index1", 6), ("word1", 64)]
                 if variant == "late-bank" else [("indexValue", 6)])
    expected += [("successorValue", 64), ("pcValue", 8)]
    rows = [line.split("\t") for line in path.read_text().splitlines()]
    if len(rows) != len(expected):
        raise ValueError("Changed bank-selection cut count")
    cuts = {}
    for row, (role, width) in zip(rows, expected):
        if len(row) != 2 or row[0] != role or not re.fullmatch(r"%v\d+", row[1]):
            raise ValueError("Invalid bank-selection cut labels")
        name = row[1][1:]
        if name in cuts or name not in source.nodes or source.nodes[name].width != width:
            raise ValueError("Aliased or incorrectly sized bank-selection cut")
        cuts[name] = role
    return cuts


def design_source(variant):
    if variant == "composed":
        return "import Pinwheel.Hardware.Storage.BackendReadback\n"
    flag = "true" if variant == "late-bank" else "false"
    owner = "CacheEnable" if variant == "enable-split" else "BankSelect"
    netlist = "CacheEnable.netlist" if variant == "enable-split" else f"BankSelect.netlist {flag}"
    return "import Pinwheel.Hardware.Storage.CacheEnable\n" + rb.HEADER + f"""
abbrev lift := @BankSelect.lift
abbrev feed := @BankSelect.feed
abbrev feedFinal := @BankSelect.feedFinal
abbrev body := {owner}.body
abbrev nextPC := BankSelect.nextPC
abbrev successor := BankSelect.successor {flag}
abbrev netlist := {netlist}
namespace Readback
abbrev target := BankSelect.target
abbrev selected := BankSelect.selected
end Readback
end Pinwheel.Artifact.Backend
"""


def parameters(source, cuts):
    return " ".join(f"({label} : BitVec {source.nodes[n].width})" for n, label in cuts.items())


def scope_source(source, cuts, names, cut_module):
    remaining = list(cuts.items())[2:]
    args = " ".join(label for _, label in remaining)
    params = " ".join(f"({label} : BitVec {source.nodes[n].width})" for n, label in remaining)
    lines = [f"import {cut_module}\n" + rb.HEADER, "set_option linter.unusedSimpArgs false"]
    for kind, name in names:
        n = (source.next if kind == "next" else source.outputs)[name]
        ctor = (rb.REGISTERS if kind == "next" else rb.OUTPUTS)[name][1]
        item = source.nodes[n]
        lhs = source.expression(item, None) if item.op in ("input", "reg") else (
            f"Hint.{n} i s (Readback.target.eval i s) (Readback.selected.eval i s) {args}")
        lines.append(f"theorem hint_{kind}_{name} (i : Values Machine.Input) (s : Values Register)\n"
                     f"    {params} :\n"
                     f"    {lhs} = (body.{kind} ({ctor})).eval\n"
                     "      (WithWire.values (WithWire.values i successorValue) pcValue) s := by\n"
                     "  simp only [body, CacheEnable.body, BankSelect.body, Expr.eval_bind, BankSelect.feedFinal,\n"
                     "    fresh_correct, BankSelect.feed, coreRegF, Expr.eval]\n"
                     "  rfl\n")
    return "\n".join(lines) + "\nend Pinwheel.Artifact.Backend\n"


def cuts_source(source, cuts, variant, embeddings_module, pc_module):
    names = {label: n for n, label in cuts.items()}
    params = parameters(source, cuts)
    args = " ".join(cuts.values())
    concrete = " ".join(f"(Source.{n} i s)" for n in cuts)
    lines = [f"import {embeddings_module}\nimport {pc_module}\n" + rb.HEADER,
             "set_option linter.unusedSimpArgs false"]
    for label, expr, unfolding in (
        ("address", "Readback.target.eval i s", "Readback.target, BankSelect.target, BankSelect.lift, Expr.eval_bind, Storage.Cache.target"),
        ("selection", "Readback.selected.eval i s", "Readback.selected, BankSelect.selected, BankSelect.lift, Storage.Cache.liftExpr, Expr.eval_bind")):
        name = names[label]
        theorem = "target" if label == "address" else "selected"
        lines.append(f"theorem hint_{theorem} (i : Values Machine.Input) (s : Values Register) {params} :\n"
                     f"    Hint.{name} i s {args} = {expr} := by\n  simp only [{unfolding}]\n  rfl\n")
        lines.append(f"theorem source_{theorem} (i : Values Machine.Input) (s : Values Register) :\n"
                     f"    Source.{name} i s = {expr} :=\n"
                     f"  (embed_{name} i s).symm.trans (hint_{theorem} i s {concrete})\n")
    if variant == "late-bank":
        stages = []
        for b in (0, 1):
            bank = "true" if b else "false"
            stages.extend([
                (f"index{b}", f"(BankSelect.Readback.indexStage {bank}).eval (BankSelect.Readback.stageValues address) s"),
                (f"word{b}", f"(BankSelect.Readback.wordStage {bank}).eval (BankSelect.Readback.stageValues index{b}) s")])
        successor_expr = "(if selection = 1 then word1 else word0)"
        read_theorem = "BankSelect.Readback.late_read_correct i.values s.values"
    else:
        stages = [("indexValue", "Storage.Backend.Readback.indexRead.eval (Storage.Backend.Readback.readInputs selection address) s")]
        successor_expr = "Storage.Backend.Readback.wordRead.eval (Storage.Backend.Readback.wordInputs selection indexValue) s"
        read_theorem = "BankSelect.Readback.control_read_correct i s"
    rewrites = ["source_target", "source_selected"]
    for label, expr in stages:
        name = names[label]
        lines.append(f"theorem hint_{label} (i : Values Machine.Input) (s : Values Register) {params} :\n"
                     f"    Hint.{name} i s {args} = {expr} := by\n  rfl\n")
        instantiated = expr
        for role, n in names.items():
            instantiated = re.sub(rf"\b{role}\b", f"(Source.{n} i s)", instantiated)
        # Only replace whole parameter tokens; Lean namespace identifiers remain intact.
        lines.append(f"theorem source_{label} (i : Values Machine.Input) (s : Values Register) :\n"
                     f"    Source.{name} i s = {instantiated} :=\n"
                     f"  (embed_{name} i s).symm.trans (hint_{label} i s {concrete})\n")
        rewrites.insert(0, f"source_{label}")
    successor, pc = names["successorValue"], names["pcValue"]
    lines.append(f"theorem hint_successor (i : Values Machine.Input) (s : Values Register) {params} :\n"
                 f"    Hint.{successor} i s {args} = {successor_expr} := by\n  rfl\n")
    values = concrete.replace(" i s)", " i.values s.values)")
    lines.append(f"theorem source_successor (i : Machine.Inputs) (s : State) :\n"
                 f"    Source.{successor} i.values s.values = successor.eval i.values s.values := by\n"
                 f"  have h := (embed_{successor} i.values s.values).symm.trans (hint_successor i.values s.values {values})\n"
                 f"  simp only [{', '.join(rewrites)}] at h\n"
                 f"  exact h.trans ({read_theorem})\n")
    lines.append("""
theorem body_pc (i : Values Machine.Input) (s : Values Register) (c : BitVec 64) (d : BitVec 8) :
    (body.next (.core .pc)).eval (WithWire.values (WithWire.values i c) d) s =
      nextPC.eval (WithWire.values i c) s := by
  simp only [body, CacheEnable.body, BankSelect.body, nextPC, BankSelect.nextPC, Expr.eval_bind,
    BankSelect.feedFinal, fresh_correct, coreRegF, coreRegS, Expr.eval]
""")
    remaining = " ".join(f"(Source.{n} i s)" for n in list(cuts)[2:])
    lines.append(f"theorem source_pc (i : Values Machine.Input) (s : Values Register) :\n"
                 f"    Source.{pc} i s = nextPC.eval (WithWire.values i (Source.{successor} i s)) s := by\n"
                 f"  have h := (embed_{pc} i s).symm\n"
                 "  simp only [source_target, source_selected] at h\n"
                 f"  exact (h.trans (hint_next_r_pc i s {remaining})).trans (body_pc i s _ _)\n")
    return "\n".join(lines) + "\nend Pinwheel.Artifact.Backend\n"
