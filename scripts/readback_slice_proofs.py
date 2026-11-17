"""Add a kernel Nat-projection proof branch for single-word slice bounds.

Only proof tactics change. No graph, theorem statement, endpoint, width or
assumption changes, and successful generated proofs still pass the axiom audit.
"""
from pathlib import Path
import re


def prove_slice_bounds(directory: Path, modules: list[str]) -> int:
    count = 0
    for module in modules:
        if not re.fullmatch(r'LocalProofs[0-9]*',module):
            continue
        path = directory/(module+'.lean')
        def strengthen(match):
            nonlocal count
            header,binders,proposition,body = match[1],match[2],match[3],match[4]
            variables = re.findall(r'\((x[0-9]+) : BitVec [0-9]+\)',binders)
            complete_binders = re.fullmatch(r'\(x[0-9]+ : BitVec [0-9]+\)(?: \(x[0-9]+ : BitVec [0-9]+\))*',binders)
            marker = '  all_goals first\n  | rfl\n'
            if not complete_binders or marker not in body or not all(fragment in proposition for fragment in
                    ('BitVec.ofBool','decide','toNat <',"extractLsb'")):
                return match[0]
            if len(variables) == 1 and '= (0#' in proposition:
                branch=("  | (congr 1\n"
                        "     simp only [decide_eq_decide, BitVec.toNat_eq, BitVec.extractLsb'_toNat, BitVec.toNat_ofNat]\n"
                        f"     have slice_bound := {variables[0]}.isLt\n"
                        "     omega)\n")
            elif proposition.lstrip().startswith('(if ') and ') = (if ' in proposition:
                bounds = ''.join(f"     have slice_bound_{x} := {x}.isLt\n" for x in variables)
                branch=("  | (\n"+bounds+
                        "     simp [BitVec.toNat_eq, BitVec.toNat_ofBool, BitVec.extractLsb'_toNat, BitVec.toNat_ofNat]\n"
                        "     all_goals split <;> split <;> simp_all <;> omega)\n")
            else:
                return match[0]
            count += 1
            return header+body.replace(marker,marker+branch,1)
        original=path.read_text()
        updated=re.sub(r'(theorem local_[0-9]+ ([^\n]*) :\n([^\n]*) := by\n)(.*?)'
                       r'(?=\ntheorem |\nrun_cmd |\nend )',strengthen,original,flags=re.DOTALL)
        path.write_text(updated)
    return count
