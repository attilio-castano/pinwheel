"""Complete cell-area and state counts for an exact proof-oriented netlist.

The pinned Liberty supplies area; netlist self-reported areas are ignored.
Hierarchy is expanded by the strict functional interpreter before counting.
This module supplies no equivalence, electrical or physical timing claim.
"""
from collections import Counter
from decimal import Decimal, InvalidOperation
import hashlib
from pathlib import Path

from streaming_mapped_liberty import (LIBRARY_SHA256, FF, group_name, load_library,
    parse_document, require, scalar)
from streaming_mapped_netlist import load_mapped

SCHEMA = 'pinwheel.streaming-mapped-cost.v1'
TT_PORTS = {'ui_in': (8, 'input'), 'uo_out': (8, 'output'), 'uio_in': (8, 'input'),
    'uio_out': (8, 'output'), 'uio_oe': (8, 'output'), 'ena': (1, 'input'),
    'clk': (1, 'input'), 'rst_n': (1, 'input')}


def sha(path): return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def parse_areas(text, selected):
    """Pure extraction for tests; acceptance additionally pins all library bytes."""
    selected = set(selected)
    roots = parse_document(text)
    require(selected and len(roots) == 1 and roots[0].name == 'library', 'Missing selected area library')
    cells = {}
    for item in roots[0].children:
        if item.name != 'cell': continue
        name = group_name(item)
        require(name not in cells, 'Duplicate area cell')
        cells[name] = item
    require(selected <= cells.keys(), 'Missing mapped cell area')
    areas = {}
    for name in sorted(selected):
        raw = scalar(cells[name].children, 'area')
        try: value = Decimal(raw)
        except InvalidOperation as error: raise ValueError('Invalid mapped cell area') from error
        require(value.is_finite() and value > 0, 'Nonpositive or nonfinite mapped cell area')
        areas[name] = value
    return areas


def graph_cost(graph, areas, declared_bits):
    """A count/area calculation, independent of any functional proof result."""
    require(type(declared_bits) is int and declared_bits > 0 and
        len(graph.flipflops) == declared_bits and len(graph.state_bits) == declared_bits,
        'Mapped full-state inventory differs from the declared state')
    counts = Counter(gate.cell for gate in graph.gates)
    counts.update(ff.cell for ff in graph.flipflops)
    require(dict(sorted(counts.items())) == graph.cell_counts and set(counts) <= areas.keys(),
        'Incomplete cell or area inventory')
    require(counts[FF] == declared_bits and all(type(value) is Decimal and value.is_finite() and value > 0
        for value in areas.values()), 'Unsupported state cell or area')
    levels = {}
    for gate in graph.gates:
        model = graph.library.cells[gate.cell]
        parents = [levels.get(bit, 0) for pin, bit in gate.connections.items()
            if model.directions[pin] == 'input']
        levels[gate.output] = 1 + max(parents, default=0)
    endpoints = [ff.d for ff in graph.flipflops]
    endpoints += [bit for bits in graph.outputs.values() for bit in bits]
    total = sum((areas[name] * count for name, count in counts.items()), Decimal(0))
    return dict(declared_state_bits=declared_bits, physical_ff_bits=len(graph.flipflops),
        combinational_cells=len(graph.gates), total_cells=sum(counts.values()),
        cell_counts=dict(sorted(counts.items())), cell_area_um2=str(total),
        cell_area_um2_display=float(total),
        longest_combinational_gate_path=max((levels.get(bit, 0) for bit in endpoints), default=0),
        cell_areas_um2={name: str(areas[name]) for name in sorted(counts)})


def measure(netlist, top, liberty, declared_bits, *, complete=False):
    netlist, liberty = Path(netlist), Path(liberty)
    before = {str(netlist): sha(netlist), str(liberty): sha(liberty)}
    library = load_library(liberty)
    graph = load_mapped(netlist, top, library)
    require(type(complete) is bool, 'Complete package scope must be explicit')
    if complete:
        ports = {name: (len(bits), 'input') for name, bits in graph.inputs.items()}
        ports.update({name: (len(bits), 'output') for name, bits in graph.outputs.items()})
        require(ports == TT_PORTS and top.startswith('tt_um_pinwheel_streaming_ready_d'),
            'Complete cost must include the actual Tiny Tapeout port envelope')
    result = graph_cost(graph, parse_areas(liberty.read_text(), graph.cell_counts), declared_bits)
    require(before == {str(netlist): sha(netlist), str(liberty): sha(liberty)}, 'Cost inputs changed during measurement')
    return dict(schema=SCHEMA, scope='complete-tiny-tapeout' if complete else 'component',
        top=top, liberty_sha256=LIBRARY_SHA256, input_sha256=before, inputs_unchanged=True,
        timing_qualified=False, mapped_equivalence_proved=False,
        boundary='Exact standard-cell bill for this separately measured proof-oriented mapping. '
            'Full source FF inventory is retained. Area is the sum of pinned Liberty cell areas, '
            'not a placed footprint. Gate depth is unweighted; no delay, Fmax or physical signoff claim. '
            'Functional equivalence requires the separate native kernel artifact certificate.',
        **result)
