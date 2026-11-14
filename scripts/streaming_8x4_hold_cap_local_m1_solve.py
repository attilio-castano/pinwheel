"""Substitute the frozen GDS-based ground patch into the retained rail model."""

import argparse
from pathlib import Path

import numpy as np
from scipy.sparse.linalg import splu

from streaming_8x4_draft_rc_timing import bound
from streaming_8x4_e982_native import read, require, sha, write
from streaming_8x4_hold_cap_local_m1_grid import ROOT, SHEET_R, WINDOWS
from streaming_8x4_hold_cap_local_m1_mesh import build_mesh, geometry
from streaming_8x4_hold_cap_physical import TARGET


EXTERIOR = ROOT / "m1-exterior-04.json"
EXTERIOR_SHA = "9a00b40675bf41775e27147f2c547749b758a46e9ec3f28c69383a73e4d31e06"


def couple(mesh, exterior):
    labels = [port["name"] for port in exterior["ports"]]
    indices = np.array([mesh.ports[name].item() for name in labels])
    inside = np.ones(len(mesh.rhs), dtype=bool)
    inside[indices] = False
    matrix, rhs = mesh.matrix, mesh.rhs
    factor = splu(matrix[inside][:, inside].tocsc())
    to_ports = matrix[inside][:, indices]
    offset = factor.solve(rhs[inside])
    sensitivities = factor.solve(-to_ports.toarray())
    from_ports = matrix[indices][:, inside]
    y = matrix[indices][:, indices].toarray() + from_ports @ sensitivities
    i0 = from_ports @ offset - rhs[indices]
    require(np.max(np.abs(y - y.T)) < 1e-9 and np.max(np.abs(y.sum(axis=1))) < 1e-8
            and np.linalg.eigvalsh(y).min() > -1e-10, "Local port reduction is not passive and reciprocal")
    impedance = np.array(exterior["port_impedance_ohm"])
    opened = np.array(exterior["open_port_voltages_v"])
    anchor = opened[0]
    port_v = np.linalg.solve(np.eye(len(labels)) + impedance @ y, (opened - anchor) - impedance @ i0)
    solution = np.empty(len(rhs))
    solution[indices] = port_v
    solution[inside] = offset + sensitivities @ port_v
    metrics = mesh.metrics(solution)
    amps = ((matrix @ solution) - rhs)[indices]
    readback_a = [metrics["ports"][name]["current_a_into_local"] for name in labels]
    require(np.allclose(amps, readback_a, rtol=0, atol=1e-10), "Mesh and reduced boundary currents differ")
    reduced_residual = float(np.max(np.abs(port_v - (opened - anchor - impedance @ amps))))
    require(reduced_residual < 1e-10 and abs(amps.sum() + rhs.sum()) < 2e-10,
            "Assembled local/exterior solve failed boundary balance")
    return_v = np.array(exterior["open_source_voltages_v"]) - np.array(exterior["external_source_response_ohm"]) @ amps
    error = abs(float(return_v.sum()) - exterior["total_native_load_a"])
    require(error < 1e-9, "Ground returns do not balance the original load")
    return dict(local=metrics, voltage_reference_v=float(anchor), ports=labels, port_voltages_v=(port_v + anchor).tolist(),
                port_currents_a_into_local=amps.tolist(), local_admittance_s=y.tolist(),
                max_boundary_voltage_residual_v=reduced_residual, ground_return_currents_a=return_v.tolist(),
                global_load_error_a=error)


def cases(local, ext):
    steps = (80, 40, 20) if ext["window_dbu"][2] - ext["window_dbu"][0] > 40000 else (80, 40, 20, 10)
    variants = [(step, 20.0, 5.0, "typ", SHEET_R) for step in steps]
    variants += [(20, 20.0, None, "typ", SHEET_R), (20, 20.0, 0.0, "min", SHEET_R),
                 (20, 20.0, 20.0, "max", SHEET_R)]
    if local.via_cut_boxes_dbu:
        variants += [(20, 5.0, 5.0, "typ", SHEET_R), (20, 9.0, 5.0, "typ", SHEET_R),
                     (20, 5.0, 5.0, "typ", 0.135)]
    result = []
    for pitch, via, lower, contact, sheet in variants:
        ports = [dict(port, resistance_ohm=via) if port["kind"] == "via" else port for port in ext["ports"]]
        model = build_mesh(local, ports, ext["terminal_loads"], mesh_limit=pitch,
                           lower_sheet_ohm=lower, contact_corner=contact, sheet_ohm=sheet)
        record = couple(model, ext)
        result.append(dict(mesh_max_pitch_dbu=pitch, via_ohm_per_cut=via if local.via_cut_boxes_dbu else None,
                           lower_sheet_ohm_per_square=lower, metal1_sheet_ohm_per_square=sheet,
                           contact_corner=contact, **record))
        peak = record["local"]["reference_section"]["current_a_positive_x"] * 1e6
        print(f"{ext['window_dbu']} mesh={pitch} via={via} lower={lower} reference={peak:.6f} uA", flush=True)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    out = parser.parse_args().out.resolve()
    require(out.parent == ROOT and not out.exists() and sha(EXTERIOR) == EXTERIOR_SHA,
            "Use a fresh output and exact exterior receipt")
    exterior = read(EXTERIOR)
    require(exterior["schema"] == "pinwheel.streaming-8x4-hold-cap-m1-exterior.v1"
            and exterior["odb"]["sha256"] == TARGET["odb_sha256"]
            and exterior["gds"]["sha256"] == TARGET["gds_sha256"]
            and exterior["windows"].keys() == WINDOWS.keys(), "Wrong exterior target or partition")
    for key in ("odb", "gds", "def_view", "dump", "terminal_readback", "producer"):
        item = exterior[key]
        require(bound(item["path"]) == item, "Exterior input or producer changed")
    windows = {}
    for name, window in WINDOWS.items():
        row = exterior["windows"][name]
        require(tuple(row["window_dbu"]) == window, "Partition geometry changed")
        local = geometry(window)
        windows[name] = dict(geometry_inputs=local.bindings, area_um2=local.metal.area() / 1e6,
                             window_dbu=window, cases=cases(local, row))
    require(sha(EXTERIOR) == EXTERIOR_SHA and all(bound(item["path"]) == item
            for row in windows.values() for item in row["geometry_inputs"]), "Frozen inputs changed during solve")
    write(out, dict(schema="pinwheel.streaming-8x4-hold-cap-local-m1-replacement.v1",
                    status="diagnostic", exterior=bound(EXTERIOR), windows=windows,
                    target_odb_sha256=TARGET["odb_sha256"], target_gds_sha256=TARGET["gds_sha256"],
                    producer=bound(__file__), geometry_producer=bound(Path(__file__).with_name(
                        "streaming_8x4_hold_cap_local_m1_mesh.py")), scope="Exact drawn Metal1 replaces all lumped paths inside "
                    "the cut, with the nearest Via1 replaced to retained Metal2 when present. The selected "
                    "decap lower contacts and fixed leakage are local models. Other local leakage lands on "
                    "its own VSS conductor. Exterior lumped Metal1, other terminal stars and upper grids "
                    "stay at their original modeled assumptions.", qualified_em=False))


if __name__ == "__main__":
    main()
