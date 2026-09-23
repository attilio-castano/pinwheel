#!/usr/bin/env python3
"""Derive a checkpoint with signal-routing keepouts over SRAMs on Metal4.

Run in the pinned OpenROAD Python environment. Adds two obstructions that
exempt power nets. Refuses macros with signal pins on Metal4, preserves the
source checkpoint, and records every input/output identity. No placement,
power-grid, connectivity, RTL, or timing-constraint change is made here.
"""
import argparse
import hashlib
import json
from pathlib import Path

import physical_checkpoint as checkpoint


def topology(block):
    instances = [(i.getName(), i.getMaster().getName(), i.getLocation(), str(i.getOrient()))
                 for i in block.getInsts()]
    nets = [(n.getName(), str(n.getSigType()),
             sorted((t.getInst().getName(), t.getMTerm().getName()) for t in n.getITerms()),
             sorted(t.getName() for t in n.getBTerms())) for n in block.getNets()]
    return hashlib.sha256(json.dumps([sorted(instances), sorted(nets)]).encode()).hexdigest()


def main():
    import odb

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--design", type=Path, required=True)
    parser.add_argument("--state", type=Path, required=True)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    source = checkpoint.verify(args.state, args.manifest, args.design)
    state = json.loads(args.state.read_text())
    database = checkpoint.artifact_path(state["odb"], args.design)
    db = odb.read_db(odb.dbDatabase.create(), str(database))
    block = db.getChip().getBlock()
    before = topology(block)
    before_obstructions = len(block.getObstructions())
    layer = db.getTech().findLayer("Metal4")
    if layer is None:
        raise RuntimeError("Missing Metal4")
    macros = [i for i in block.getInsts() if i.getMaster().isBlock()]
    if {i.getName() for i in macros} != {"memory.storage0", "memory.storage1"}:
        raise RuntimeError("Unexpected macro inventory")
    added = []
    for inst in macros:
        if any(l.getName() == "Metal4" for it in inst.getITerms()
               if str(it.getSigType()) not in {"POWER", "GROUND"} for l, _ in it.getGeometries()):
            raise RuntimeError("Cannot obstruct a layer with macro signal pins")
        rect = inst.getBBox()
        coordinates = [rect.xMin(), rect.yMin(), rect.xMax(), rect.yMax()]
        obs = odb.dbObstruction_create(block, layer, *coordinates)
        obs.setExceptPGNetsObstruction()
        if not obs.isExceptPGNetsObstruction():
            raise RuntimeError("Power-net exemption was not applied")
        added.append(dict(instance=inst.getName(), layer="Metal4", except_power_nets=True,
                          bbox_um=[x / block.getDbUnitsPerMicron() for x in coordinates]))
    if topology(block) != before or len(block.getObstructions()) != before_obstructions + 2:
        raise RuntimeError("Unexpected physical-design change")
    args.output.mkdir(parents=True, exist_ok=False)
    output_db, output_def = args.output / "keepouts.odb", args.output / "keepouts.def"
    odb.write_db(db, str(output_db))
    odb.write_def(block, str(output_def))
    # Re-read the exported database; verify that the new keepouts survive it.
    exported_db = odb.read_db(odb.dbDatabase.create(), str(output_db))
    exported = exported_db.getChip().getBlock()
    if topology(exported) != before or len(exported.getObstructions()) != before_obstructions + 2:
        raise RuntimeError("Keepout database did not round-trip")
    actual = {(o.getBBox().getTechLayer().getName(),
               (o.getBBox().xMin(), o.getBBox().yMin(), o.getBBox().xMax(), o.getBBox().yMax()),
               o.isExceptPGNetsObstruction()) for o in exported.getObstructions()}
    for inst in macros:
        b = inst.getBBox()
        if ("Metal4", (b.xMin(), b.yMin(), b.xMax(), b.yMax()), True) not in actual:
            raise RuntimeError("Keepout geometry or power-net exemption changed on round-trip")
    for kind, file in [("odb", output_db), ("def", output_def)]:
        state[kind] = "/work/core/" + file.resolve().relative_to(args.design.resolve()).as_posix()
    state_path = args.output / "state.json"
    state_path.write_text(json.dumps(state, indent=2) + "\n")
    manifest = checkpoint.capture(state_path, args.output / "manifest.json", args.design)
    checkpoint.verify(args.state, args.manifest, args.design)
    receipt = dict(source_checkpoint=source, added_obstructions=added,
        topology_sha256=before, source_database_sha256=checkpoint.sha(database),
        output_database_sha256=checkpoint.sha(output_db), output_def_sha256=checkpoint.sha(output_def),
        output_manifest_sha256=checkpoint.sha(args.output / "manifest.json"),
        output_state_sha256=manifest["state_sha256"], script_sha256=checkpoint.sha(Path(__file__)),
        metrics_note="Inherited pre-route metrics are unchanged and are not measurements of this derived layout.")
    (args.output / "derivation.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps(added, indent=2))


if __name__ == "__main__":
    main()
