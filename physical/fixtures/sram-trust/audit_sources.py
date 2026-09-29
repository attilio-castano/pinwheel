"""Read-only provenance audit of the retained SRAM and captured public sources.

Run from a checkout containing the ignored, hash-bound evidence captures.
Print JSON; do not fetch sources, edit views or interpret a match as signoff.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re

MACRO = "RM_IHPSG13_1P_512x64_c2_bm_bist"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def blob(path):
    body = path.read_bytes()
    return hashlib.sha1(b"blob " + str(len(body)).encode() + b"\0" + body).hexdigest()


def require(condition, message):
    if not condition:
        raise ValueError(message)


def widths(path):
    text = re.sub(r"\n\+\s*", " ", path.read_text())
    blocks = re.findall(r"(?ims)^\.subckt ([^\n]+)\n(.*?)^\.ends[^\n]*", text)
    found = [(h, b) for h, b in blocks
             if h.split()[0] == "RM_IHPSG13_512x64_c2_1P_BITKIT_CELL"]
    require(len(found) == 1, "Exactly one bit-cell CDL required")
    result = re.findall(r"(?m)^(R[012]) (\S+) (\S+) lvsres w=(\S+) l=(\S+)$", found[0][1])
    require(len(result) == 3, "Expected three explicit bit-cell resistors")
    return [dict(name=n, terminals=[a, b], width_m=float(w), length_m=float(l))
            for n, a, b, w, l in result]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path.cwd())
    args = parser.parse_args()
    root = args.root.resolve()
    evidence = root / "build/validation/sram-trust-01"
    lock_path = root / "tools/physical-toolchain.json"
    lock = json.loads(lock_path.read_text())
    tree_path = root / "build/physical/upstream/pdk-tree.json"
    require(sha(tree_path) == lock["pdk_tree_sha256"], "PDK inventory changed")
    tree = json.loads(tree_path.read_text())
    require(tree["sha"] == lock["pdk_revision"] and tree["truncated"] is False,
            "Wrong or incomplete PDK tree")
    entries = {x["path"]: x for x in tree["tree"]}
    base = root / "build/physical/paired-buffer-balance-01/experiments/paired-balance-place-02/macro"
    views = []
    for kind, suffix in [("cdl", ".cdl"), ("gds", ".gds"), ("lef", ".lef"),
                         ("verilog", ".v"), ("lib", "_slow_1p08V_125C.lib"),
                         ("lib", "_fast_1p32V_m55C.lib"), ("lib", "_typ_1p20V_25C.lib")]:
        path = base / (MACRO + suffix)
        upstream = "ihp-sg13g2/libs.ref/sg13g2_sram/" + kind + "/" + path.name
        entry = entries[upstream]
        require(entry["type"] == "blob" and blob(path) == entry["sha"],
                "Actual macro differs from pinned release: " + path.name)
        views.append(dict(path=str(path.relative_to(root)), upstream_path=upstream,
                          sha256=sha(path), git_blob=entry["sha"], matches=True))
    link = "ihp-sg13cmos5l/libs.ref/sg13cmos5l_sram"
    captured_link = evidence / "sources-01/pdk-pinned" / link
    require(entries[link]["mode"] == "120000" and blob(captured_link) == entries[link]["sha"],
            "CMOS5L SRAM alias provenance changed")
    require(captured_link.read_text() == "../../ihp-sg13g2/libs.ref/sg13g2_sram",
            "Unexpected SRAM alias")
    core = "RM_IHPSG13_1P_core_behavioral_bm_bist.v"
    behavioral = root / "build/storage/macros" / core
    core_source = "ihp-sg13g2/libs.ref/sg13g2_sram/verilog/" + core
    require(blob(behavioral) == entries[core_source]["sha"], "Behavioral dependency changed")
    captured_core = evidence / "sources-02/pdk-pinned" / core_source
    require(sha(behavioral) == sha(captured_core), "Captured behavioral source differs")
    captures = []
    for directory in ["sources-01", "sources-02", "sources-03"]:
        receipt_path = evidence / directory / "receipt.json"
        receipt = json.loads(receipt_path.read_text())
        for item in receipt["sources"]:
            path = evidence / directory / item["path"]
            require(sha(path) == item["sha256"] and path.stat().st_size == item["bytes"],
                    "Captured public source changed")
        captures.append(dict(path=str(receipt_path.relative_to(root)), sha256=sha(receipt_path),
            status=receipt["status"], source_count=len(receipt["sources"]),
            error=receipt.get("error")))
    original = evidence / "sources-02/pdk-original" / (MACRO + ".cdl")
    source_widths = dict(original_2023=widths(original), pinned=widths(base / (MACRO + ".cdl")))
    require(source_widths["original_2023"] == source_widths["pinned"], "Bit-cell width history changed")
    for kind in ["gds", "cdl"]:
        require(sha(base / (MACRO + "." + kind)) ==
                sha(evidence / "sources-01/pdk-head" / (MACRO + "." + kind)),
                "Captured default-branch view differs")
    tt = json.loads((evidence / "sources-01/tt/src/config.json").read_text())
    print(json.dumps(dict(status="provenance_verified", physical_qualification=False,
        pdk_revision=lock["pdk_revision"], pdk_tree_sha256=sha(tree_path), views=views,
        cmos5l_alias=dict(path=link, target=captured_link.read_text(), git_blob=entries[link]["sha"]),
        behavioral_dependency=dict(path=str(behavioral.relative_to(root)), sha256=sha(behavioral),
            upstream_path=core_source, git_blob=entries[core_source]["sha"], matches=True),
        captures=captures, bitcell_source_dimensions=source_widths,
        reference_policy={k: tt.get(k) for k in ["MAGIC_EXT_ABSTRACT_CELLS", "MAGIC_EXT_USE_GDS",
            "ERROR_ON_LVS_ERROR", "ERROR_ON_MAGIC_DRC", "RUN_KLAYOUT_DRC", "RUN_KLAYOUT_XOR"]},
        interpretation="All seven supplied views and the simulation dependency match one release. "
            "Source width history and a supported library alias do not qualify physical behavior."), indent=2))


if __name__ == "__main__":
    main()
