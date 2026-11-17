"""Complete typed-interface certificates using the restricted Pinwheel importer.

The profile is trusted Lean source configuration. RTL JSON and source hints are
parsed fail-closed; generated endpoint equalities are checked by Lean. Yosys and
the JSON interpretation remain outside the kernel's trust boundary.
"""
from __future__ import annotations

import importlib.util
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]


def _helper(name):
    spec = importlib.util.spec_from_file_location("_typed_" + name, ROOT / "scripts" / (name + ".py"))
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


abstraction = _helper("readback_boolean_abstraction")
mux_abstraction = _helper("readback_mux_abstraction")
union_abstraction = _helper("readback_union_abstraction")


def source_paths():
    """Owning proof-generator dependencies for every client's evidence closure."""
    return tuple(ROOT / name for name in (
        "scripts/typed_circuit_readback.py", "scripts/backend_readback.py",
        "scripts/typed_artifact_runner.py", "scripts/process_group.py",
        "scripts/readback_boolean_abstraction.py", "scripts/readback_mux_abstraction.py",
        "scripts/readback_union_abstraction.py", "Pinwheel/Hardware/Artifact.lean",
        "Pinwheel/Hardware/Readback/Boolean.lean"))


IDENTIFIER = re.compile(r"[A-Za-z_][A-Za-z0-9_]*\Z")
HEADER = """import Design
open Pinwheel.Hardware
namespace Pinwheel.TypedArtifact
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
"""


def validate_descriptor(descriptor):
    if not isinstance(descriptor.get("module"), str) or not IDENTIFIER.fullmatch(descriptor["module"]):
        raise ValueError("Invalid top module name")
    names = {"clk"}
    for kind in ("inputs", "registers", "outputs"):
        ports = descriptor.get(kind)
        if not isinstance(ports, list):
            raise ValueError(f"Missing typed {kind} enumeration")
        for index, port in enumerate(ports):
            if not isinstance(port, dict):
                raise ValueError("Malformed port")
            name, width = port.get("name"), port.get("width")
            if not isinstance(name, str) or not IDENTIFIER.fullmatch(name) or name in names:
                raise ValueError(f"Invalid or duplicate signal: {name}")
            ordinal = port.get("index", index)
            if type(width) is not int or width <= 0 or type(ordinal) is not int or ordinal != index:
                raise ValueError(f"Invalid width or enumeration index: {name}")
            if kind == "registers" and (not isinstance(port.get("reference", "r_" + name), str) or
                    not IDENTIFIER.fullmatch(port.get("reference", "r_" + name))):
                raise ValueError(f"Invalid register reference: {name}")
            names.add(name)
    references = [p.get("reference", "r_" + p["name"]) for p in descriptor["registers"]]
    if len(set(references)) != len(references):
        raise ValueError("Duplicate register references")
    external = {p["name"] for kind in ("inputs", "outputs") for p in descriptor[kind]} | {"clk", "clock"}
    if set(references) & external:
        raise ValueError("Register references alias an external port or clock")
    # The reused restricted importer reserves these internal SSA node names.
    if any(re.fullmatch(r"[nv][0-9]+", name) or name == "clock"
           for name in [p["name"] for p in descriptor["inputs"]] + references):
        raise ValueError("Signal aliases a reserved importer node name")


def importer(descriptor):
    validate_descriptor(descriptor)
    name = "_typed_circuit_backend_readback"
    spec = importlib.util.spec_from_file_location(name, ROOT / "scripts/backend_readback.py")
    rb = importlib.util.module_from_spec(spec)
    sys.modules[name] = rb
    spec.loader.exec_module(rb)
    rb.TOP = descriptor["module"]
    rb.INPUTS = {p["name"]: (p["width"], f"input_{k}") for k, p in enumerate(descriptor["inputs"])}
    rb.OUTPUTS = {p["name"]: (p["width"], f"output_{k}") for k, p in enumerate(descriptor["outputs"])}
    rb.REGISTERS = {p.get("reference", "r_" + p["name"]): (p["width"], f"register_{k}")
                    for k, p in enumerate(descriptor["registers"])}
    rb.HEADER = HEADER
    return rb


def local_proofs(rb, pairs, *, start=0, plans=None):
    lines = ["import Lean.Elab.Command\nimport Pinwheel.Hardware.Readback.Boolean\n" + HEADER,
             "set_option linter.unusedSimpArgs false"]
    for k, pair in enumerate(pairs, start=start):
        if plans and k in plans:
            _, helper, plan = plans[k]
            lines.append(helper.lean_lemmas(pair, plan, f"local_{k}", rb.render_tree))
            continue
        variables = " ".join(f"(x{j} : BitVec {w})" for j, (w, _, _) in enumerate(pair["variables"]))
        lines.append(f"theorem local_{k} {variables} :\n"
                     f"    {rb.render_tree(pair['left'])} = {rb.render_tree(pair['right'])} := by\n"
                     "  try simp only [ite_self, BitVec.sub_eq_add_neg, Pinwheel.Hardware.Readback.zero_lt_bit]\n"
                     "  all_goals first\n"
                     "  | rfl\n"
                     "  |\n"
                     "    all_goals bv_normalize\n"
                     "    all_goals first | omega | grind (splits := 32)\n"
                     "    done\n"
                     "  | (simp [Pinwheel.Hardware.Readback.eq_bits, Fin.forall_fin_succ,\n"
                     "      BitVec.getElem_append, BitVec.getElem_extractLsb']; all_goals grind (splits := 32))\n")
        if sum(w for w, _, _ in pair["variables"]) <= 8:
            names = " ".join(f"x{j}" for j in range(len(pair["variables"])))
            # Kernel reduction closes small comparison/Boolean identities whose
            # arithmetic and bitwise normal forms otherwise need a bridge.
            lines.append(f"  | ({'revert ' + names + '; ' if names else ''}decide +kernel)\n")
        if k % 100 == 0:
            lines.append(f'run_cmd IO.eprintln "checked local {k}"')
    lines.append("end Pinwheel.TypedArtifact\n")
    return "\n".join(lines)


def generate(directory: Path, descriptor, hints: Path, rtl: Path, solver: Path, *, profile: str,
             interface_checks: str = ""):
    """Profile defines Input/Register/Output, circuit, inputs/registers/outputs.

    Each descriptor must have the corresponding Interface type. Source-hint
    endpoint proofs must reduce to the declared circuit by rfl, so metadata
    cannot silently substitute a different circuit or omit a typed endpoint.
    The returned certificate concerns every bit, including unreachable states.
    """
    rb = importer(descriptor)
    source, actual = rb.read_hints(hints), rb.read_rtl(rtl)
    oracle = rb.cut_oracle(solver)
    pairs = rb.partitions(source, actual, successor="v-1", oracle=oracle)
    matches = {(p["source"], p["rtl"]) for p in pairs}
    for left, right in [(source.next[name], actual.next[name]) for name in rb.REGISTERS] + [
            (source.outputs[name], actual.outputs[name]) for name in rb.OUTPUTS]:
        if (left, right) not in matches:
            # A suggested cut can erase correlations needed at an endpoint.
            # Fall back to its complete expressions, still proved by Lean.
            variables, definitions = {}, set()

            def expand(graph, name, namespace):
                node = graph.nodes[name]
                if node.op in ("input", "reg"):
                    key = (node.width, node.op, node.value)
                    if key not in variables:
                        variables[key] = len(variables)
                    return node.width, "var", (), variables[key]
                definitions.add(f"{namespace}.{name}")
                return node.width, node.op, tuple(expand(graph, arg, namespace) for arg in node.args), node.value

            lhs, rhs = expand(source, left, "Source"), expand(actual, right, "RTL")
            pairs.append({"source": left, "rtl": right, "variables": list(variables),
                          "definitions": sorted(definitions), "dependencies": [], "left": lhs, "right": rhs})
            matches.add((left, right))
    # Wide tag comparisons can hide a tiny Boolean identity from tactic search.
    # Generalize shared predicates, prove the stronger finite lemma by kernel
    # reduction, and instantiate the exact original statement. The solver only
    # filters suggestions; it never supplies evidence accepted by the kernel.
    plans = {}
    for k, pair in enumerate(pairs):
        for kind, helper in (("boolean", abstraction), ("mux", mux_abstraction), ("union", union_abstraction)):
            plan = helper.suggest(pair, max_bits=13)
            if plan is not None and oracle(plan.pair):
                plans[k] = kind, helper, plan
                break
    # Imports belong before the namespace; profiles put all imports first.
    lines = profile.splitlines()
    imports = [line for line in lines if line.startswith("import ")]
    body = [line for line in lines if not line.startswith("import ")]
    design = "\n".join(imports) + "\nimport Pinwheel.Hardware.Artifact\n"
    design += "open Pinwheel.Hardware\nnamespace Pinwheel.TypedArtifact\n"
    design += "set_option backward.isDefEq.respectTransparency false\n" + "\n".join(body) + "\n"
    for kind, typ, stem in (("inputs", "Input", "input"), ("registers", "Register", "register"),
                            ("outputs", "Output", "output")):
        design += f"example : ({kind} : Interface {typ}).size = {len(descriptor[kind])} := by decide +kernel\n"
        for index, port in enumerate(descriptor[kind]):
            design += (f"def {stem}_{index} : {typ} {port['width']} := by with_unfolding_all exact "
                       f"({kind}.signal ⟨{index}, by decide +kernel⟩).2\n")
            label = f'{kind}.label {stem}_{index}'
            expected = port["name"]
            if kind == "registers":
                label = f'"r_" ++ ({label})'
                expected = port.get("reference", "r_" + expected)
            design += f'example : {label} = "{expected}" := by decide +kernel\n'
    (directory / "Design.lean").write_text(design + interface_checks + "\nend Pinwheel.TypedArtifact\n")

    def write(name, text):
        text = text.replace("Values Machine.Input", "Values Input")
        text = text.replace("end Pinwheel.Artifact.Backend", "end Pinwheel.TypedArtifact")
        (directory / f"{name}.lean").write_text(text)

    write("Graphs", HEADER + source.definitions("Source") + actual.definitions("RTL") +
          "end Pinwheel.TypedArtifact\n")
    # Each lemma is independent of the other local lemmas. Bound compilation
    # units so large configurations retain per-unit timeout/progress evidence,
    # without changing either the propositions or the kernel-checked proof path.
    local_modules = []
    if len(pairs) > 50:
        for start in range(0, len(pairs), 50):
            name = f"LocalProofs{start // 50:03d}"
            write(name, local_proofs(rb, pairs[start:start + 50], start=start, plans=plans))
            local_modules.append(name)
        write("LocalProofs", "\n".join(f"import {name}" for name in local_modules) + "\n")
    else:
        write("LocalProofs", local_proofs(rb, pairs, plans=plans))
    write("Links", rb.links_source(source, actual, pairs, "LocalProofs", "Graphs"))

    def value(graph, name, namespace):
        node = graph.nodes[name]
        return graph.expression(node, None) if node.op in ("input", "reg", "lit") else f"{namespace}.{name} i s"

    matches = {(p["source"], p["rtl"]): k for k, p in enumerate(pairs)}
    lines = ["import Links\n" + HEADER]
    parameters = "(i : Values Input) (s : Values Register)"
    endpoint_count = 0
    for kind, mapping, constructors, desc, typ, operation in (
            ("next", source.next, rb.REGISTERS, "registers", "Register", "step"),
            ("output", source.outputs, rb.OUTPUTS, "outputs", "Output", "observe")):
        entries = []
        # Descriptor order, never an incidental parser or dictionary order.
        for name, (_, ctor) in constructors.items():
            sn, rn = mapping[name], (actual.next if kind == "next" else actual.outputs)[name]
            lhs, rhs = value(source, sn, "Source"), value(actual, rn, "RTL")
            stem = f"{kind}_{len(entries)}"
            lines.append(f"theorem hint_{stem} {parameters} :\n"
                         f"  {lhs} = circuit.{operation} i s {ctor} := by rfl\n")
            index = matches.get((sn, rn))
            proof = f"exact link_{index} i s" if index is not None else "rfl"
            lines.append(f"theorem rtl_{stem} {parameters} :\n"
                         f"  {rhs} = circuit.{operation} i s {ctor} := by\n"
                         f"  have h : {lhs} = {rhs} := by {proof}\n"
                         f"  exact h.symm.trans (hint_{stem} i s)\n")
            entries.append((rhs, f"rtl_{stem}"))
        size = len(entries)
        endpoint_count += size
        lines.append(f"def {kind}Table {parameters} : (k : Fin {desc}.size) → BitVec ({desc}.signal k).1\n")
        for index, (expression, _) in enumerate(entries):
            lines.append(f"  | ⟨{index}, _⟩ => by with_unfolding_all exact {expression}\n")
        lines.append(f"  | ⟨k + {size}, h⟩ => False.elim (by change k + {size} < {size} at h; omega)\n")
        lines.append(f"theorem {kind}Table_correct {parameters} (k : Fin {desc}.size) :\n"
                     f"  {kind}Table i s k = circuit.{operation} i s ({desc}.signal k).2 := by\n"
                     f"  match k with\n")
        for index, (_, theorem) in enumerate(entries):
            lines.append(f"  | ⟨{index}, _⟩ => with_unfolding_all exact {theorem} i s\n")
        lines.append(f"  | ⟨k + {size}, h⟩ => exact False.elim (by change k + {size} < {size} at h; omega)\n")
        lines.append(f"def rtl_{operation} {parameters} : Values {typ} :=\n"
                     f"  {desc}.assemble ({kind}Table i s)\n"
                     f"theorem rtl_{operation}_eq {parameters} :\n"
                     f"  (fun {{w}} (p : {typ} w) => rtl_{operation} i s p) = "
                     f"(fun {{w}} (p : {typ} w) => circuit.{operation} i s p) :=\n"
                     f"  Interface.assemble_eq _ _ _ ({kind}Table_correct i s)\n")
    lines.append("""
def rtlComponent : Timed.Component (Values Input) (Values Register) (Values Output) :=
  ⟨rtl_step, rtl_observe⟩

theorem correspondence : Artifact.Correspondence circuit rtlComponent :=
  ⟨rtl_step_eq, rtl_observe_eq⟩

theorem trace_eq (s : Values Register) (inputs : List (Values Input)) :
    rtlComponent.trace s inputs = circuit.component.trace s inputs :=
  correspondence.refinement.trace_eq _ _ rfl inputs

end Pinwheel.TypedArtifact
""")
    write("Proof", "\n".join(lines))
    write("Audit", """import Lean
import Proof
open Lean Elab Command
elab "#audit_typed_artifact" : command => do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "Pinwheel.TypedArtifact." then
      count := count + 1
      let axioms ← collectAxioms name
      let bad := axioms.filter fun a => a != ``propext && a != ``Classical.choice && a != ``Quot.sound
      unless bad.isEmpty do throwError "Unapproved axioms in {name}: {bad}"
  if count == 0 then throwError "Empty artifact proof audit"
  logInfo m!"Typed artifact audit: {count} declarations, standard axioms only."
#audit_typed_artifact
""")
    return ["Design", "Graphs", *local_modules, "LocalProofs", "Links", "Proof", "Audit"], {
        "local_equalities": len(pairs), "endpoints": endpoint_count,
        "local_proof_units": len(local_modules) or 1,
        "boolean_generalizations": sum(kind == "boolean" for kind, _, _ in plans.values()),
        "mux_generalizations": sum(kind == "mux" for kind, _, _ in plans.values()),
        "union_generalizations": sum(kind == "union" for kind, _, _ in plans.values()),
        "max_generalized_bits": max((plan.bits for _, _, plan in plans.values()), default=0),
        "max_mux_label_bits": max((plan.tag_width for kind, _, plan in plans.values() if kind == "mux"), default=0),
        "max_union_label_bits": max((len(plan.leaves) for kind, _, plan in plans.values() if kind == "union"), default=0),
        "source_nodes": len(source.nodes), "rtl_nodes": len(actual.nodes)}
