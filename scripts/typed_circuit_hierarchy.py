"""Checked metadata normalization for flattened typed circuit hierarchies.

This is part of the explicitly trusted JSON interpretation boundary. It checks
complete bijective state-name binding and widths; Lean subsequently checks every
imported transition and output expression against the flat structural circuit.
"""
from __future__ import annotations

from copy import deepcopy
import json
from pathlib import Path
import re

from typed_circuit_readback import IDENTIFIER, validate_descriptor

PATH = re.compile(r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*\Z")


def normalize_descriptor(descriptor):
    flat = deepcopy(descriptor)
    registers = descriptor.get("registers")
    if not isinstance(registers, list):
        raise ValueError("Missing register enumeration")
    mapping, paths = {}, []
    for actual, normalized in zip(registers, flat["registers"], strict=True):
        if not isinstance(actual, dict):
            raise ValueError("Malformed hierarchy register")
        canonical, path = actual.get("flat_reference"), actual.get("reference")
        if not isinstance(canonical, str) or not isinstance(path, str) or not PATH.fullmatch(path):
            raise ValueError("Invalid hierarchical state reference")
        if canonical in mapping or path in paths:
            raise ValueError("Hierarchy state map must be bijective")
        mapping[canonical] = path
        paths.append(path)
        normalized["reference"] = canonical
    if descriptor.get("register_map") != mapping or descriptor.get("hierarchical_registers") != paths:
        raise ValueError("Hierarchy state maps disagree with the complete register enumeration")
    validate_descriptor(flat)
    return flat


def prepare_json(original, destination, descriptor):
    flat = normalize_descriptor(descriptor)
    document = json.loads(original.read_text())
    if set(document.get("modules", {})) != {descriptor["module"]}:
        raise ValueError("Expected one flattened top module")
    names = document["modules"][descriptor["module"]].get("netnames", {})
    for register in descriptor["registers"]:
        canonical, actual, width = register["flat_reference"], register["reference"], register["width"]
        if actual not in names or len(names[actual].get("bits", [])) != width:
            raise ValueError(f"Missing or wrong-width hierarchical state: {actual}")
        if canonical in names and canonical != actual:
            raise ValueError(f"Ambiguous canonical state alias: {canonical}")
        names[canonical] = deepcopy(names[actual])
    destination.write_text(json.dumps(document) + "\n")
    return flat


def source_paths():
    return (Path(__file__).resolve(), Path(__file__).with_name("readback_miter.py"))


def lower_leaves(run, tools, directory, descriptor):
    leaves = descriptor.get("leaves")
    if (not isinstance(leaves, list) or not leaves
            or any(not isinstance(n, str) or not IDENTIFIER.fullmatch(n) for n in leaves)
            or len(set(leaves)) != len(leaves)):
        raise ValueError("Expected distinct leaf module identifiers")
    sources = []
    for index, leaf in enumerate(leaves):
        target = directory / (leaf + ".sv")
        target.write_text(run([tools["circt"], directory / (leaf + ".mlir"), "--canonicalize",
                               "--lower-seq-to-sv", "--lower-hw-to-sv", "--hw-legalize-modules",
                               "--export-verilog", "-o", "/dev/null"],
                              directory.name + f"-lower-{index}"))
        sources.append(target)
    return sources


def import_assembly(run, tools, directory, descriptor, leaves, *, normalize_muxes=False):
    """Import the actual assembled hierarchy, retaining physical and canonical names."""
    from typed_module_checks import cad
    flat = normalize_descriptor(descriptor)
    actual = directory / "hierarchical.sv"
    top = directory / "hierarchy_top.sv"
    actual.write_text("\n".join(p.read_text() for p in [*leaves, top]))
    raw, imported, script = (directory / n for n in ("raw.json", "import.json", "import.ys"))
    mux_pass = "pmuxtree\n" if normalize_muxes else ""
    script.write_text(f"read_verilog -sv {cad.yosys_quote(actual)}\n"
                      f"hierarchy -check -top {flat['module']}\n"
                      f"flatten -noscopeinfo\nproc\n{mux_pass}opt_clean\ncheck -assert\n"
                      f"write_json {cad.yosys_quote(raw)}\n")
    run([tools["yosys"], "-Q", "-T", "-s", script], directory.name + "-import")
    flat = prepare_json(raw, imported, descriptor)
    (directory / "canonical-interface.json").write_text(json.dumps(flat, indent=2) + "\n")
    return flat


def path_checks(descriptor, design):
    """Bind the physical paths used by Yosys to the declared instance state."""
    return "\n".join(
        f"example : {design}.statePath register_{index} = {json.dumps(r['reference'])} := by decide +kernel"
        for index, r in enumerate(descriptor["registers"])
    )


def swap_instance_inputs(text, instances, pin):
    """Exchange one named input's wiring on two instances of the same leaf."""
    instance_matches, wires = [], []
    for name in instances:
        pattern = r"(?m)^(\w+) " + re.escape(name) + r"\(([^\n]*)\);$"
        matches = list(re.finditer(pattern, text))
        if len(matches) != 1:
            raise ValueError(f"Expected exactly one connection list for instance {name}")
        instance = matches[0]
        ports = list(re.finditer(r"\." + re.escape(pin) + r"\((\w+)\)", instance[2]))
        if len(ports) != 1:
            raise ValueError(f"Expected exactly one {pin} connection on {name}")
        instance_matches.append(instance)
        port = ports[0]
        wires.append((instance.start(2) + port.start(1), instance.start(2) + port.end(1), port[1]))
    left, right = wires
    if instance_matches[0][1] != instance_matches[1][1] or left[2] == right[2]:
        raise ValueError("Miswire requires distinct wires on the same leaf input")
    for start, end, wire in sorted([(left[0], left[1], right[2]), (right[0], right[1], left[2])],
                                   reverse=True):
        text = text[:start] + wire + text[end:]
    return text


def check_miswire(run, tools, directory, descriptor, leaves, mlir, profile, checks, instances, pin):
    from readback_miter import miter
    import typed_circuit_readback as readback
    from typed_module_checks import reject_semantic_certificate

    negative = directory / ("miswire-" + directory.name)
    negative.mkdir()
    top = (directory / "hierarchy_top.sv").read_text()
    (negative / "hierarchy_top.sv").write_text(swap_instance_inputs(top, instances, pin))
    flat = import_assembly(run, tools, negative, descriptor, leaves)
    imported = negative / "import.json"
    rb = readback.importer(flat)
    query = negative / "mismatch.smt2"
    query.write_text(miter(rb, rb.read_hints(mlir), rb.read_rtl(imported)))
    if run([tools["z3"], "-smt2", query], negative.name + "-mismatch").strip() != "sat":
        raise ValueError("Deliberate cross-instance miswire must change an endpoint")
    modules, _ = readback.generate(negative, flat, mlir, imported, tools["z3"], profile=profile,
                                   interface_checks=checks)
    failure = reject_semantic_certificate(run, negative, modules)
    return {"instances": instances, "input": pin, "mismatch": "sat", "kernel_rejection_module": failure}
