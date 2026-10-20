"""Fresh matched synthesis cost for the separate sampled-ready packages.

The mapping and saved-netlist accounting backend is shared with streaming_cost.
Only emission and the explicitly named four-row contract differ. Historical
receipts, netlists and caches are never inputs to this producer.
"""
from copy import deepcopy
import json
from pathlib import Path

import streaming_cost as base

SCHEMA = 'pinwheel.streaming-ready-matched-cost.v1'
LABELS = ('streaming-ready-d2', 'streaming-ready-d4',
    'buffered-v1-macro-excluded', 'buffered-v1-full-digital-ff')
LIBRARY_SHA256 = base.LIBRARY_SHA256
BOUNDARY = ('Matched typical CMOS5L saved synthesis cost with identical Yosys/ABC settings '
    'and the same TT pad envelope. These are distinct host protocols and instruction sets, '
    'not functionally equivalent replacements. The sampled-ready microcore supports generic '
    'guarded stream and drive-wait operations; this comparison does not establish ISA '
    'equivalence to the older buffered controller. Area is the sum of Liberty cell areas. '
    'Sequential cells include program, FIFO, shifter, partial RX, current cell, ready-wait '
    'control, frame, CRC, staging, reply/replay and export-custody state. The longest '
    'combinational cell path is an unweighted graph metric. ABC stime -p supplies a separate '
    'combinational Liberty delay estimate with FF/macro boundaries cut and the declared '
    'input-drive/output-load constraints; it excludes clock-to-Q, setup, clocks and '
    'parasitics and implies no guaranteed Fmax. Synthesis functional preservation is '
    'trusted here; no mapped equivalence, placement, routing, parasitics, macro area or '
    'electrical claim.')


def emit_sources(run, out, *, root, circt, lake):
    """Fresh Ready emission plus unchanged old-controller baseline emissions.

    The caller supplies its selected committed source archive and selected native
    tools, and freezes all inputs before consumption. No old report is consumed.
    """
    from streaming_ready_wrapper import package_source, tt_source
    root, out = Path(root), Path(out)
    out.mkdir(parents=True, exist_ok=False)
    targets, frozen = [], {}

    def freeze(paths):
        for path in paths:
            path = Path(path)
            if path.is_symlink() or not path.is_file():
                raise ValueError('Expected a regular emitted synthesis input')
            value = base.sha(path)
            if str(path) in frozen and frozen[str(path)] != value:
                raise RuntimeError('Emitted input changed before use')
            frozen[str(path)] = value

    def lower(directory, component, mlir):
        freeze([mlir])
        text = run([circt, mlir, '--canonicalize', '--lower-seq-to-sv', '--lower-hw-to-sv',
            '--hw-legalize-modules', '--export-verilog', '-o', '/dev/null'],
            'ready-cost-lower-' + directory.name + '-' + component)
        source = directory / (component + '.sv')
        source.write_text(text)
        freeze([source])
        return source

    for depth in (2, 4):
        directory = out / ('d' + str(depth))
        run([lake, 'env', 'lean', '-DwarningAsError=true', '--run',
            'test/StreamingReadyArtifactEmit.lean', directory, '1' if depth == 2 else '2'],
            'ready-cost-emit-d' + str(depth))
        freeze([directory / name for name in ('core.mlir', 'frontend.mlir',
            'assembly.json', 'frontend-assembly.json')])
        core = json.loads((directory / 'assembly.json').read_text())
        front = json.loads((directory / 'frontend-assembly.json').read_text())
        sources = [lower(directory, 'core', directory / 'core.mlir'),
            lower(directory, 'frontend', directory / 'frontend.mlir')]
        for name, text in [('package', package_source(core, front)), ('tt', tt_source(depth))]:
            source = directory / (name + '.sv')
            source.write_text(text)
            freeze([source])
            sources.append(source)
        registers = (base.inventory(core, 'engine.core.', 'streaming-core') +
            base.inventory(front, 'engine.frontend.', 'streaming-frontend'))
        targets.append(dict(label='streaming-ready-d' + str(depth),
            top='tt_um_pinwheel_streaming_ready_d' + str(depth), sources=sources, registers=registers))
    baseline = out / 'old-v1'
    baseline.mkdir()
    request = baseline / 'input.json'
    request.write_text(json.dumps(dict(schema='pinwheel-buffered-sram-serial-input-v1', cases=[])) + '\n')
    freeze([request])
    # Empty evaluator vectors request emission only, never a validation pass.
    run([lake, 'env', 'lean', '-DwarningAsError=true', '--run',
        'test/BufferedSramSerialExport.lean', request, baseline / 'frontend'], 'ready-cost-emit-old-frontend')
    run([lake, 'env', 'lean', '-DwarningAsError=true', '--run',
        'test/SramArtifactEmit.lean', baseline / 'controller'], 'ready-cost-emit-old-controller')
    freeze([baseline / part / name for part, name in [('frontend', 'frontend.mlir'),
        ('frontend', 'assembly.json'), ('controller', 'core.mlir'), ('controller', 'assembly.json')]])
    sources = [lower(baseline, 'frontend', baseline / 'frontend/frontend.mlir'),
        lower(baseline, 'controller', baseline / 'controller/core.mlir')]
    sources += [root / 'physical' / name for name in ('buffered_sram_serial_wrapper.sv',
        'buffered_sram_memory.sv', 'tt_um_pinwheel_buffered.sv')]
    freeze(sources)
    registers = (base.inventory(json.loads((baseline / 'controller/assembly.json').read_text()),
        'engine.controller.', 'buffered-core') +
        base.inventory(json.loads((baseline / 'frontend/assembly.json').read_text()),
        'engine.frontend.', 'buffered-frontend'))
    # Identical full digital storage law to the original matched-cost producer.
    model = '''module RM_IHPSG13_1P_64x64_c2_bm_bist(
input A_CLK,A_MEN,A_DLY,A_WEN,A_REN,
input [5:0] A_ADDR, input [63:0] A_DIN,A_BM, output reg [63:0] A_DOUT,
input A_BIST_CLK,A_BIST_EN,A_BIST_MEN,A_BIST_WEN,A_BIST_REN,
input [5:0] A_BIST_ADDR, input [63:0] A_BIST_DIN,A_BIST_BM);
reg [63:0] memory[0:63];
integer k;
always @(posedge A_CLK) if(A_MEN) begin
  if(A_WEN) begin
    for(k=0;k<64;k=k+1) if(A_BM[k]) memory[A_ADDR][k] <= A_DIN[k];
  end else if(A_REN) A_DOUT <= memory[A_ADDR];
end
endmodule
'''
    digital, blackbox = baseline / 'digital-memory.sv', baseline / 'excluded-macro.sv'
    digital.write_text(model)
    blackbox.write_text('(* blackbox *) ' + model.split(');', 1)[0] + ');\nendmodule\n')
    freeze([digital, blackbox])
    targets += [dict(label='buffered-v1-macro-excluded', top='tt_um_pinwheel_buffered',
        sources=sources, registers=registers, macro_model=blackbox),
        dict(label='buffered-v1-full-digital-ff', top='tt_um_pinwheel_buffered',
            sources=[*sources, digital], registers=registers + base.digital_memory_inventory())]
    return targets, frozen


def check_comparison(result):
    """Require Ready identities, then preserve every backend cost constraint."""
    if (type(result) is not dict or result.get('schema') != SCHEMA or
            type(result.get('rows')) is not list or
            any(type(row) is not dict for row in result['rows']) or
            [row.get('label') for row in result['rows']] != list(LABELS)):
        raise ValueError('Expected the complete sampled-ready matched cost matrix')
    normalized = deepcopy(result)
    normalized['schema'] = 'pinwheel.streaming-matched-cost.v1'
    normalized['rows'][0]['label'] = 'streaming-d2'
    normalized['rows'][1]['label'] = 'streaming-d4'
    base.check_comparison(normalized)


def compare(run, out, *, root, library, yosys, abc, circt, lake):
    """Integration entry point for a separate committed-source Ready gate."""
    if base.sha(library) != LIBRARY_SHA256:
        raise ValueError('Refuse an unmatched technology library before emission')
    out = Path(out)
    out.mkdir(parents=True, exist_ok=False)
    selected = out / 'cells.lib'
    selected.write_bytes(Path(library).read_bytes())
    targets, emitted = emit_sources(run, out / 'emitted', root=root, circt=circt, lake=lake)
    results = []
    for target in targets:
        if any(base.sha(path) != value for path, value in emitted.items()):
            raise RuntimeError('Fresh emission input changed before mapping')
        row = base.map_target(run, out / target['label'], library=selected,
            yosys=yosys, abc=abc, **target)
        row['boundary'] = BOUNDARY
        results.append(row)
    if any(base.sha(path) != value for path, value in emitted.items()) or base.sha(library) != LIBRARY_SHA256:
        raise RuntimeError('Fresh emission or library input changed during mapping')
    result = dict(schema=SCHEMA, boundary=BOUNDARY, liberty_sha256=LIBRARY_SHA256,
        emission_input_sha256=emitted, emission_inputs_unchanged=True, rows=results,
        matched_settings=True, mapped_equivalence_proved=False, timing_qualified=False,
        ratios=dict(depth4_over_depth2_area=results[1]['standard_cell_area_um2'] / results[0]['standard_cell_area_um2'],
            depth2_over_old_macro_excluded_area=results[0]['standard_cell_area_um2'] / results[2]['standard_cell_area_um2'],
            depth2_over_old_full_digital_area=results[0]['standard_cell_area_um2'] / results[3]['standard_cell_area_um2']))
    check_comparison(result)
    (out / 'report.json').write_text(json.dumps(result, indent=2) + '\n')
    return result
