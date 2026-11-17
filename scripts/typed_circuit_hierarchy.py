"""Checked metadata normalization for flattened typed circuit hierarchies.

This is part of the explicitly trusted JSON interpretation boundary. It checks
complete bijective state-name binding and widths; Lean subsequently checks every
imported transition and output expression against the flat structural circuit.
"""
from __future__ import annotations

from copy import deepcopy
import json
import re

from typed_circuit_readback import validate_descriptor

PATH = re.compile(r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*\Z")


def normalize_descriptor(descriptor):
    flat = deepcopy(descriptor)
    registers = descriptor.get("registers")
    if not isinstance(registers, list):
        raise ValueError("Missing register enumeration")
    mapping, paths = {}, []
    for actual, normalized in zip(registers, flat["registers"], strict=True):
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
