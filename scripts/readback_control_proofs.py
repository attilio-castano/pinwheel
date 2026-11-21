"""Add exhaustive two-bit control cases to generated proof search.

This changes proof tactics only. The four cases include every raw encoding;
none is discarded using an implementation invariant. A first two-bit variable
is merely a search heuristic, never a semantic assumption.
"""
from __future__ import annotations

from pathlib import Path
import re


def split_two_bit_controls(directory: Path, modules: list[str]) -> int:
    count = 0
    for module in modules:
        if not re.fullmatch(r"LocalProofs[0-9]*", module):
            continue
        path = directory / (module + ".lean")

        def strengthen(match):
            nonlocal count
            header, body = match[1], match[2]
            variable = re.search(r"\((x[0-9]+) : BitVec 2\)", header)
            marker = "  all_goals first\n  | rfl\n"
            if variable is None or marker not in body:
                return match[0]
            x = variable[1]
            fallback = ("  | (\n"
                f"      have raw_control_cases : {x} = 0 ∨ {x} = 1 ∨ {x} = 2 ∨ {x} = 3 := by bv_omega\n"
                "      rcases raw_control_cases with rfl | rfl | rfl | rfl\n"
                "      all_goals bv_normalize\n"
                "      all_goals first | omega | grind (splits := 32)\n"
                "      done)\n")
            count += 1
            return header + body.replace(marker, marker + fallback, 1)

        original = path.read_text()
        updated = re.sub(r"(theorem local_[0-9]+ [^\n]* :\n[^\n]* := by\n)(.*?)"
            r"(?=\ntheorem |\nrun_cmd |\nend )", strengthen, original, flags=re.DOTALL)
        path.write_text(updated)
    return count
