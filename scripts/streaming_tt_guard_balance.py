"""Source-bound guard reassociation witness; this is not a kernel or STA receipt."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess


HELPER = "Pinwheel/Hardware/BalancedConjunction.lean"
CORE = "Pinwheel/Hardware/Streaming/Core.lean"
READY_CORE = "Pinwheel/Hardware/StreamingReady/Core.lean"
FRONTEND = "Pinwheel/Hardware/Streaming/Frontend.lean"
HOST = "Pinwheel/Hardware/Streaming/HostCorrespondence.lean"
INIT = "Pinwheel/Hardware/Streaming/Initialization.lean"
PATHS = (HELPER, CORE, READY_CORE, FRONTEND, HOST, INIT)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def tokens(text: str) -> tuple[str, ...]:
    # No comments occur inside the expression seams accepted below.
    return tuple(re.findall(r"\w+|[^\s\w]", text))


def section(text: str, first: str, after: str) -> tuple[str, str, str]:
    require(text.count(first) == 1 and text.count(after) == 1, "ambiguous source seam")
    start = text.index(first)
    end = text.index(after, start)
    return text[:start], text[start:end], text[end:]


def paren_expression(text: str) -> str:
    text = text.lstrip()
    require(text.startswith("("), "expected parenthesized condition")
    depth = 0
    for index, char in enumerate(text):
        if char == "(":
            depth += 1
        elif char == ")":
            depth -= 1
            if depth == 0:
                return text[:index + 1]
    raise ValueError("unterminated condition")


def eight_tree(text: str):
    _, definition, _ = section(text, "def eight ", "def sixtyFour ")
    body = definition.split(":=", 1)[1]
    stream = re.findall(r"\.band|[()]|\bf\b|\d+|\S+", body)
    cursor = 0

    def parse():
        nonlocal cursor
        require(cursor < len(stream), "missing tree operand")
        token = stream[cursor]
        cursor += 1
        if token == "(":
            value = parse()
            require(cursor < len(stream) and stream[cursor] == ")", "bad tree parentheses")
            cursor += 1
            return value
        if token == ".band":
            return (parse(), parse())
        if token == "f":
            require(cursor < len(stream) and stream[cursor].isdigit(), "nonliteral leaf")
            value = int(stream[cursor])
            cursor += 1
            return value
        raise ValueError("unsupported tree token: " + token)

    tree = parse()
    require(cursor == len(stream), "unparsed tree source")
    return tree


def tree_stats(tree) -> tuple[list[int], int, int]:
    if type(tree) is int:
        return [tree], 0, 0
    left, right = map(tree_stats, tree)
    return left[0] + right[0], left[1] + right[1] + 1, max(left[2], right[2]) + 1


def map_leaves(tree, function):
    return function(tree) if type(tree) is int else tuple(map_leaves(t, function) for t in tree)


def guard_check(old: str, new: str, name: str, condition: str, after: str, add_import: bool):
    before_old, guard_old, end_old = section(old, "def " + name + " ", "def " + after + " ")
    before_new, guard_new, end_new = section(new, "def " + condition + " ", "def " + after + " ")
    if add_import:
        line = "import Pinwheel.Hardware.BalancedConjunction\n"
        require(before_new.count(line) == 1, "missing unique helper import")
        before_new = before_new.replace(line, "", 1)
    require(before_old == before_new and end_old == end_new,
            "state, interface, or other circuit source changed outside guard")
    marker = "(List.finRange 64).foldl (fun acc k => both acc"
    require(guard_old.count(marker) == 1, "baseline is not the historical 64-leaf guard")
    leaf = paren_expression(guard_old.split(marker)[1])
    new_leaf = paren_expression(guard_new.split(":=", 1)[1])
    require(tokens(leaf) == tokens(new_leaf), "guard leaf condition changed")
    require(tokens(guard_old.split(marker)[1]) == tokens(leaf + ") (.lit 1)"),
            "unexpected baseline fold suffix")
    expected = f"def {name} : "
    require(guard_new.count(expected) == 1, "missing unique balanced guard")
    suffix = guard_new.split(expected)[1]
    require(suffix.split("\n", 1)[0].endswith("BalancedConjunction.sixtyFour " + condition),
            "guard does not use the balanced helper")
    require(f"theorem {name}_eval_fold " in guard_new and
            f"exact BalancedConjunction.sixtyFour_eval i r {condition}" in guard_new,
            "missing public denotation bridge")
    # Pin the bridge statement to the very same historical fold, not a replacement premise.
    statement = guard_new.split(f"theorem {name}_eval_fold ")[1].split(":= by")[0]
    require(tokens(guard_old.split(":=", 1)[1]) ==
            tokens(statement.split("= (", 1)[1].rsplit(").eval i r", 1)[0]),
            "denotation bridge does not expose the exact historical fold")
    return {"guard": name, "leaf_condition_identical": True,
            "all_other_circuit_bytes_identical": True}


def inspect(current: dict[str, str], baseline: dict[str, str]) -> dict:
    helper = current[HELPER]
    require(helper.startswith("import Pinwheel.Hardware.Circuit\n"), "unexpected helper dependency")
    small = eight_tree(helper)
    require(tree_stats(small) == (list(range(8)), 7, 3), "eight tree shape/leaf identity changed")
    _, construction, _ = section(helper, "def sixtyFour ", "def legacySixtyFour ")
    expected = """eight fun block => eight fun position =>
      f ⟨block.val * 8 + position.val, by
        have blockBound := block.isLt
        have positionBound := position.isLt
        omega⟩"""
    require(tokens(construction.split(":=", 1)[1]) == tokens(expected), "64-leaf index map changed")
    full = map_leaves(small, lambda block: map_leaves(small, lambda bit: block * 8 + bit))
    leaves, ands, depth = tree_stats(full)
    require(leaves == list(range(64)) and ands == 63 and depth == 6,
            "64-leaf tree is not a complete six-level reassociation")
    guards = [guard_check(baseline[CORE], current[CORE], "covered", "coveredCondition", "countValid", True),
              guard_check(baseline[FRONTEND], current[FRONTEND], "tailCanonical", "tailCondition", "bulkOwner", False)]
    before_old, ready_old, after_old = section(baseline[READY_CORE], "def covered ", "def countValid ")
    before_new, ready_new, after_new = section(current[READY_CORE], "def covered ", "def countValid ")
    require(before_old == before_new and after_old == after_new, "Ready core changed outside guard")
    require(tokens(ready_new) == tokens("def covered : E a 1 := Streaming.Core.covered"),
            "Ready core does not reuse the same balanced coverage expression")
    legacy_old = section(baseline[CORE], "def covered ", "def countValid ")[1]
    require(tokens(legacy_old) == tokens(ready_old), "Ready coverage had different historical leaf semantics")
    guards.append({"guard": "StreamingReady.Core.covered", "leaf_condition_identical": True,
                   "same_expression_as_legacy_core": True, "all_other_circuit_bytes_identical": True})
    for path, old, new in ((HOST, "unfold Frontend.tailCanonical", "rw [Frontend.tailCanonical_eval_fold]"),
                           (INIT, "unfold Core.covered", "rw [Core.covered_eval_fold]")):
        require(baseline[path].count(old) == 1, "ambiguous original proof hook")
        require(current[path] == baseline[path].replace(old, new), "unexpected correspondence proof edit")
    return {"schema": "pinwheel.streaming.guard-balance-source.v1", "passed": True,
            "qualified": False, "kernel_proved": False, "native_state_inventory_checked": False,
            "timing_improvement_measured": False, "expected_register_bits": 6039,
            "guards": guards, "leaves": leaves, "and_nodes": ands, "and_depth": depth,
            "historical_fold_and_nodes": 64, "historical_fold_and_depth": 64,
            "required_next_gate": "Native helper proof, fresh649 foundation and regenerated exact-candidate correspondence"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--baseline", required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    require(not args.output.exists(), "refuse overwriting an earlier witness")
    revision = subprocess.check_output(["git", "rev-parse", args.baseline], cwd=args.root, text=True).strip()
    current = {path: (args.root / path).read_text() for path in PATHS}
    baseline = {path: subprocess.check_output(["git", "show", revision + ":" + path],
                cwd=args.root, text=True) for path in PATHS if path != HELPER}
    result = inspect(current, baseline)
    result["baseline_commit"] = revision
    result["source_sha256"] = {path: hashlib.sha256(value.encode()).hexdigest() for path, value in current.items()}
    result["baseline_sha256"] = {path: hashlib.sha256(value.encode()).hexdigest() for path, value in baseline.items()}
    result["producer_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    require(all((args.root / path).read_text() == value for path, value in current.items()), "source changed during inspection")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"passed": True, "and_depth": result["and_depth"],
                      "output": str(args.output)}))


if __name__ == "__main__":
    main()
