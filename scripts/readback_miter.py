"""Build an all-endpoint QF_BV miter, preserving each imported graph's sharing."""

from __future__ import annotations


def miter(rb, source, actual, *, invert_first_output=False):
    lines = ["(set-logic QF_BV)"]
    for name, (width, _) in {**rb.INPUTS, **rb.REGISTERS}.items():
        lines.append(f"(declare-fun {name} () (_ BitVec {width}))")

    def emit(graph, prefix):
        names = {}
        for name, node in graph.nodes.items():
            if node.op in ("reg", "input"):
                names[name] = node.value
                continue
            symbol = prefix + name
            names[name] = symbol
            args = [names[k] for k in node.args]
            if node.op == "lit":
                value = f"(_ bv{node.value % (1 << node.width)} {node.width})"
            elif node.op == "slice":
                value = f"((_ extract {node.value + node.width - 1} {node.value}) {args[0]})"
            elif node.op == "mux":
                value = f"(ite (= {args[0]} #b1) {args[1]} {args[2]})"
            elif node.op in ("eq", "lt"):
                op = "=" if node.op == "eq" else "bvult"
                value = f"(ite ({op} {args[0]} {args[1]}) #b1 #b0)"
            elif node.op in ("concat", "and", "or", "xor", "not", "sub", "add"):
                op = "concat" if node.op == "concat" else "bv" + node.op
                value = f"({op} {' '.join(args)})"
            else:
                raise ValueError(f"Unsupported operation {node.op}")
            lines.append(f"(define-fun {symbol} () (_ BitVec {node.width}) {value})")
        return names

    left, right = emit(source, "src_"), emit(actual, "rtl_")
    differences = []
    for kind, names, lhs, rhs in (
        ("next", rb.REGISTERS, source.next, actual.next),
        ("output", rb.OUTPUTS, source.outputs, actual.outputs),
    ):
        if names.keys() != lhs.keys() or names.keys() != rhs.keys():
            raise ValueError("Incomplete endpoint inventory")
        for j, name in enumerate(names):
            observed = right[rhs[name]]
            if invert_first_output and kind == "output" and j == 0:
                observed = f"(bvnot {observed})"
            differences.append(f"(distinct {left[lhs[name]]} {observed})")
    lines.extend([f"(assert (or {' '.join(differences)}))", "(check-sat)"])
    return "\n".join(lines) + "\n"


def check(run, tools, rb, source, actual, directory):
    for mutated, expected in ((False, "unsat"), (True, "sat")):
        label = "core-miter" + ("-inverted-output" if mutated else "")
        path = directory / (label + ".smt2")
        path.write_text(miter(rb, source, actual, invert_first_output=mutated))
        output = run([tools["z3"], "-smt2", path], label, timeout=180)
        if output.strip() != expected:
            raise ValueError(f"{label} expected {expected}, received {output.strip()}")
    return {
        "next_registers": len(rb.REGISTERS),
        "outputs": len(rb.OUTPUTS),
        "all_state_mismatch": "unsat",
        "inverted_output_mismatch": "sat",
    }
