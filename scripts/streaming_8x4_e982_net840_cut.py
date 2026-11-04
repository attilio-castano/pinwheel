#!/usr/bin/env python3
"""Plan and apply the exact e982 FIXED net840 leaf cut for fanout833/A."""

import argparse
import hashlib
import json
from pathlib import Path


TOP = "tt_um_pinwheel_streaming_ready_d2"
NET = "net840"
LEAF = "fanout833"
BEFORE_SHA256 = "26a3898d196ee74403cd8c190b51074f81f1af80841e00d504c4468508ff3550"
AFTER_SHA256 = "d42759f2e380cbd9da816abe02d22df9c7663dc351568279197fa326fc387599"
PATH = 64  # FIXED PATH, including the wire-type bits
LAYER_IDS = {7: "Metal1", 9: "Metal2", 11: "Metal3", 13: "Metal4"}
VIA_IDS = {3: "Via1_XY", 7: "Via1_YY", 22: "Via2_YX", 37: "Via3_XY"}
HORIZONTAL = (PATH, 68, 69, 68, 12)
VERTICAL = (PATH, 68, 69, 69, 12)
VIA = (PATH, 68, 69, 136, 16)
RECT = (PATH, 68, 69, 14, 11, 11, 11)
# Each complete path is independent. Neither the Metal3 trunk nor the eight
# final bridge paths belongs to this Metal2 leaf and its Metal1 pin landing.
CUT = {
    95: tuple(zip(VERTICAL, (9, 775680, 538020, 538440, 0))),
    375: tuple(zip(VIA, (7, 775680, 538440, 3, 0))),
    380: tuple(zip(VIA, (9, 775680, 538020, 22, 0))),
    551: tuple(zip(RECT, (9, 775680, 538440, -100, 0, 100, 155))),
}
BEFORE_TERMINALS = frozenset(
    [(name, "A", "INPUT") for name in (
        "ANTENNA_140", "ANTENNA_156", "ANTENNA_160", "fanout832", LEAF,
        "fanout834", "fanout836", "fanout837", "fanout839",
    )] + [("fanout840", "X", "OUTPUT")]
)
LEAF_TERMINAL = (LEAF, "A", "INPUT")


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(rows):
    encoded = json.dumps(rows, separators=(",", ":")) + "\n"
    return hashlib.sha256(encoded.encode()).hexdigest()


def paths(rows):
    """Read only the four replay templates of the exact frozen FIXED wire."""
    result = {}
    start = None
    for index, row in enumerate(rows):
        require(len(row) == 3 and all(type(value) is int for value in row) and
                row[0] == index, "Invalid native raw wire row")
        _, opcode, operand = row
        if opcode == PATH:
            start = index
            result[start] = []
        require(start is not None, "Missing initial FIXED PATH")
        result[start].append((opcode, operand))
    for path in result.values():
        opcodes = tuple(opcode for opcode, _ in path)
        require(opcodes in (HORIZONTAL, VERTICAL, VIA, RECT) and
                path[0][1] in LAYER_IDS, "Unsupported net840 replay path")
        if opcodes == VIA:
            require(path[3][1] in VIA_IDS and path[4][1] == 0,
                    "Unexpected net840 via or mask")
        elif opcodes != RECT:
            require(path[4][1] == 0, "Unexpected net840 path property")
    return result


def plan_cut(rows):
    """Return the exact expected wire vector, indexed as a native readback."""
    require(len(rows) == 647 and digest(rows) == BEFORE_SHA256,
            "Frozen net840 raw wire differs from the admitted vector")
    original = paths(rows)
    require(len(original) == 125 and
            all(tuple(original.get(start, ())) == path for start, path in CUT.items()),
            "net840 leaf path boundaries differ")
    retained = [entry for start, path in original.items() if start not in CUT for entry in path]
    result = [[index, opcode, operand] for index, (opcode, operand) in enumerate(retained)]
    require(len(result) == 625 and digest(result) == AFTER_SHA256 and
            [row[1:] for row in result[-40:]] == [row[1:] for row in rows[-40:]],
            "net840 cut changed a retained path or antenna bridge")
    return result


def report():
    return {
        "net": NET,
        "cut_terminal": LEAF + "/A",
        "wire_type": "FIXED",
        "before_wire_sha256": BEFORE_SHA256,
        "after_wire_sha256": AFTER_SHA256,
        "removed_ranges_inclusive": [[start, start + len(path) - 1] for start, path in CUT.items()],
    }


def native_net(block):
    require(block.getName() == TOP, "Unexpected OpenDB top")
    net = block.findNet(NET)
    require(net is not None and str(net.getSigType()) == "SIGNAL" and
            not net.isSpecial() and str(net.getWireType()) == "FIXED" and
            not list(net.getBTerms()) and not list(net.getSWires()),
            "Expected the regular FIXED net840 signal")
    wire = net.getWire()
    require(wire is not None and not wire.isGlobalWire(), "Missing net840 detailed wire")
    return net, wire


def native_rows(wire):
    count = wire.length()
    require(count in (625, 647), "Unexpected native net840 wire length")
    return [[index, wire.getOpcode(index), wire.getData(index)] for index in range(count)]


def terminals(net):
    return {(term.getInst().getName(), term.getMTerm().getName(), str(term.getIoType()))
            for term in net.getITerms()}


def apply_cut(odb, block, technology):
    """Apply the admitted cut before reconnecting fanout833/A.

    Work on a disposable in-memory derivative. If this raises, discard that
    derivative. This helper writes no files and leaves the leaf disconnected
    physically until the caller partitions the net and routes the new branch.
    """
    net, wire = native_net(block)
    require(terminals(net) == BEFORE_TERMINALS, "Unexpected frozen net840 pin membership")
    leaf = block.findInst(LEAF)
    require(leaf.getMaster().getName() == "sg13cmos5l_buf_1" and
            tuple(leaf.findITerm("A").getAvgXY()) == (True, 775682, 538445),
            "fanout833 input geometry changed")
    expected = plan_cut(native_rows(wire))
    layers = {index: odb.dbTechLayer.getTechLayer(technology, index) for index in LAYER_IDS}
    vias = {index: odb.dbTechVia.getTechVia(technology, index) for index in VIA_IDS}
    require(all(layer is not None and layer.getName() == LAYER_IDS[index] and
                str(layer.getType()) == "ROUTING" for index, layer in layers.items()) and
            all(via is not None and via.getName() == VIA_IDS[index]
                for index, via in vias.items()), "The e982 layer or technology-via IDs changed")
    replay = paths(expected)
    require(all(vias[path[3][1]].getBottomLayer().getName() == LAYER_IDS[path[0][1]]
                for path in replay.values() if path[3][0] == 136),
            "An e982 via starts on a different layer")

    # These are the same begin/newPath/addPoint/addTechVia/addRect/end calls
    # exercised by the earlier exact net840 FIXED replay.
    encoder = odb.dbWireEncoder()
    encoder.begin(wire)
    for path in replay.values():
        encoder.newPath(layers[path[0][1]], "FIXED")
        x, y = path[1][1], path[2][1]
        encoder.addPoint(x, y)
        opcode, operand = path[3]
        if opcode == 68:
            encoder.addPoint(operand, y)
        elif opcode == 69:
            encoder.addPoint(x, operand)
        elif opcode == 136:
            encoder.addTechVia(vias[operand])
        else:
            encoder.addRect(*(value for _, value in path[3:]))
    encoder.end()
    after_net, after_wire = native_net(block)
    require(native_rows(after_wire) == expected and terminals(after_net) == BEFORE_TERMINALS,
            "Native cut differs from its exact wire projection")
    return report()


def verify_cut(block, branch_name):
    """Verify the fixed wire and moved leaf after reconnecting the clone."""
    net, wire = native_net(block)
    require(digest(native_rows(wire)) == AFTER_SHA256 and
            terminals(net) == BEFORE_TERMINALS - {LEAF_TERMINAL},
            "net840 cut wire or retained terminals changed")
    branch = block.findNet(branch_name)
    require(branch_name != NET and branch is not None and not branch.isSpecial() and
            str(branch.getSigType()) == "SIGNAL" and not list(branch.getBTerms()),
            "Missing distinct fanout833 signal branch")
    terms = terminals(branch)
    require(LEAF_TERMINAL in terms and len(terms) == 2,
            "The new branch does not have the single admitted leaf")
    driver_name, pin, direction = next(iter(terms - {LEAF_TERMINAL}))
    driver = block.findInst(driver_name)
    upstream = block.findInst("fanout840").findITerm("A").getNet()
    clone_upstream = driver.findITerm("A").getNet() if (
        driver.getMaster().getName() == "sg13cmos5l_buf_1") else None
    require((pin, direction) == ("X", "OUTPUT") and clone_upstream is not None and
            upstream is not None and clone_upstream.getName() == upstream.getName(),
            "The new branch is not driven by the admitted equal-master clone")
    return dict(report(), branch=branch_name, clone=driver_name)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("wire_json", type=Path, help="Retained native net840 raw wire receipt")
    args = parser.parse_args()
    receipt = json.loads(args.wire_json.read_text())
    require(receipt["net"] == dict(name=NET, signal_type="SIGNAL", wire_type="FIXED",
                                  global_wire=False, special=False, special_wire_count=0) and
            receipt["raw_scalar_sequence_sha256"] == BEFORE_SHA256 and
            receipt["junction_references"] == [],
            "Receipt does not describe the exact FIXED net840 wire")
    plan_cut(receipt["raw_entries"])
    print(json.dumps(report(), indent=2))


if __name__ == "__main__":
    main()
