"""Add kernel-checked byte-slice proof search without changing propositions.

Two-bit binders are tried in reverse order as possible byte offsets. Every raw
value is considered; no alignment or reachable-state hypothesis is introduced.
The original tactics remain available if the new branches cannot close every goal.
"""
from __future__ import annotations

from pathlib import Path
import re

HELPER_MODULE = "ByteSliceLemmas"
NAMESPACE = "Pinwheel.TypedArtifact.ByteSlices"
LOCAL_MODULE = re.compile(r"LocalProofs[0-9]*\Z")
# Generated ordinary declarations have exactly two header lines. Neither this
# matcher nor the proof-body scanner may consume another top-level declaration.
HEADER = re.compile(r"theorem (local_[0-9]+) ([^\n]*) :\n([ \t]+[^\n]+) := by\n\Z")
ORDINARY_START = re.compile(r"theorem local_[0-9]+(?:\s|$)")
SEARCH_MARKER = "  all_goals first\n  | rfl\n"
PREPASS = "  try simp only [BitVec.append_assoc, BitVec.cast_eq]\n"


def helper_source() -> str:
    source = f"""import Pinwheel.Hardware.Readback.Boolean
namespace {NAMESPACE}
set_option maxRecDepth 100000

theorem eqZero (x : BitVec 1) : BitVec.ofBool (decide (x = (0#1))) = ~~~x := by
  revert x
  decide +kernel

theorem eqOne (x : BitVec 1) : BitVec.ofBool (decide (x = (1#1))) = x := by
  revert x
  decide +kernel

theorem boolOne (b : Bool) : (BitVec.ofBool b = (1#1)) = (b = true) := by
  cases b <;> decide

"""
    for width in (8, 16):
        count, repeated = 32-width, "x"
        for _ in range(count):
            repeated = f"(b ++ {repeated})"
        source += f"""theorem pad{width} (b : BitVec 1) (x : BitVec {width}) :
    ((if b = (1#1) then ({(1 << count)-1}#{count}) else (0#{count})) ++ x) = {repeated} := by
  have h : b = (0#1) ∨ b = (1#1) := by bv_omega
  rcases h with rfl | rfl
  all_goals simp only [BitVec.append_assoc', BitVec.cast_eq]
  all_goals rfl

"""
    return source + f"end {NAMESPACE}\n"


def _branch(variable: str | None) -> str:
    cases = "" if variable is None else f"""      have byte_offset_cases : {variable} = (0#2) ∨ {variable} = (1#2) ∨ {variable} = (2#2) ∨ {variable} = (3#2) := by bv_omega
      rcases byte_offset_cases with rfl | rfl | rfl | rfl
"""
    return "  | (\n"+cases+f"""      all_goals try simp only [BitVec.append_assoc, BitVec.cast_eq]
      all_goals try simp [BitVec.and_assoc, Bool.or_assoc,
        {NAMESPACE}.eqZero, {NAMESPACE}.eqOne, {NAMESPACE}.boolOne]
      all_goals try rw [← {NAMESPACE}.pad8]
      all_goals try rw [← {NAMESPACE}.pad16]
      done)
"""


def _declarations(text: str):
    """Return ordinary theorem header/body spans, rejecting ambiguous boundaries."""
    lines, offsets = text.splitlines(keepends=True), [0]
    for line in lines:
        offsets.append(offsets[-1]+len(line))
    declarations, names, index = [], set(), 0
    while index < len(lines):
        if not ORDINARY_START.match(lines[index]):
            index += 1
            continue
        if index+1 >= len(lines):
            raise ValueError("Truncated ordinary local theorem header")
        header = lines[index]+lines[index+1]
        match = HEADER.fullmatch(header)
        if match is None:
            raise ValueError("Ordinary local theorem header must occupy exactly two lines")
        if match[1] in names:
            raise ValueError("Duplicate ordinary local theorem: " + match[1])
        names.add(match[1])
        end = index+2
        while end < len(lines) and (not lines[end].strip() or lines[end][0] in " \t"):
            end += 1
        if end == len(lines) or not lines[end].startswith(("theorem ", "run_cmd ", "end ")):
            raise ValueError("Missing or unexpected top-level local proof boundary")
        declarations.append((offsets[index], offsets[index+2], offsets[end], header, match[2]))
        index = end
    return declarations


def _rewrite(text: str):
    declarations = _declarations(text)
    replacements, prepasses, branches, direct = [], 0, 0, 0
    for start, body_start, end, header, binders in declarations:
        body = text[body_start:end]
        if SEARCH_MARKER not in body:
            continue
        if body.count(SEARCH_MARKER) != 1 or PREPASS in body or "byte_offset_cases" in body:
            raise ValueError("Repeated or already modified local proof search marker")
        updated = body.replace("  all_goals first\n", PREPASS+"  all_goals first\n", 1)
        variables = re.findall(r"\((x[0-9]+) : BitVec 2\)", binders)
        # Normalize before rfl: definitional comparison of two identical mux
        # guards can otherwise expand a wide concatenation before failing.
        fast_paths = "".join(_branch(variable) for variable in reversed(variables)) if variables else _branch(None)
        updated = updated.replace(SEARCH_MARKER, "  all_goals first\n"+fast_paths+"  | rfl\n", 1)
        branches += len(variables)
        direct += int(not variables)
        replacements.append((start, end, header+updated))
        prepasses += 1
    rewritten = text
    for start, end, replacement in reversed(replacements):
        rewritten = rewritten[:start]+replacement+rewritten[end:]
    before = [item[3] for item in declarations]
    after = [item[3] for item in _declarations(rewritten)]
    if before != after:
        raise AssertionError("Byte-slice proof search changed an original proposition")
    if replacements:
        if f"import {HELPER_MODULE}\n" in rewritten:
            raise ValueError("Existing byte-slice helper import")
        rewritten = f"import {HELPER_MODULE}\n"+rewritten
    return rewritten, {"append_prepasses": prepasses, "finite_offset_branches": branches,
                       "direct_normalization_branches": direct,
                       "preserved_propositions": len(declarations)}


def prepare_byte_slices(directory: Path, modules: list[str]) -> dict:
    """Generate one audited helper and patch ordinary proof tactics in place.

    The helper module is inserted before the first LocalProofs unit. Malformed
    declarations, duplicate preparation, and existing helper files fail before
    any source or module-list mutation. The caller must compile and audit all
    returned modules: preparation itself is never theorem acceptance.
    """
    directory = Path(directory)
    if type(modules) is not list or any(type(module) is not str for module in modules) or len(set(modules)) != len(modules):
        raise ValueError("Expected a distinct ordered module list")
    indices = [index for index, module in enumerate(modules) if LOCAL_MODULE.fullmatch(module)]
    if not indices or HELPER_MODULE in modules or (directory / f"{HELPER_MODULE}.lean").exists():
        raise ValueError("Missing local proofs or byte-slice helper already exists")
    updates = []
    evidence = {"helper_module": HELPER_MODULE, "modified_modules": [], "append_prepasses": 0,
                "finite_offset_branches": 0, "direct_normalization_branches": 0, "preserved_propositions": 0,
                "raw_offset_values_per_branch": 4}
    for index in indices:
        module = modules[index]
        path = directory / (module+".lean")
        original = path.read_text()
        changed, counts = _rewrite(original)
        for key, value in counts.items():
            evidence[key] += value
        if changed != original:
            updates.append((path, changed))
            evidence["modified_modules"].append(module)
    # All source parsing/proposition checks have completed before the first write.
    (directory / f"{HELPER_MODULE}.lean").write_text(helper_source())
    for path, changed in updates:
        path.write_text(changed)
    modules.insert(indices[0], HELPER_MODULE)
    return evidence
