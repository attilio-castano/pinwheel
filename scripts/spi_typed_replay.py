"""Compare legacy and typed Lean emissions at the existing SPI public pins."""

from filecmp import cmp
import json

from streaming_8x4_spi_modes import DEPTH, run_cases
from streaming_ready_artifacts import LOWERING_PASSES, lowering_copy
from streaming_ready_wrapper import bridge_source, package_source, tt_source


COMPONENTS = ('core', 'frontend')


def legacy_assembly(path, *, addr_bits=None):
    """Project the typed interface onto the existing wrapper and readback ABI."""
    description = json.loads(path.read_text())
    if description['clock'] != 'clk':
        raise RuntimeError(f'Unexpected clock port in {path}')
    assembly = dict(schema=1, module=description['module'])
    if addr_bits is not None:
        assembly['addr_bits'] = addr_bits
    for collection in ('inputs', 'registers', 'outputs'):
        fields = ('name', 'width', 'reference') if collection == 'registers' else ('name', 'width')
        rows = description[collection]
        if any(type(row['index']) is not int or row['index'] != index
               for index, row in enumerate(rows)):
            raise RuntimeError(f'Unexpected {collection} indices in {path}')
        assembly[collection] = [{field: row[field] for field in fields} for row in rows]
    return assembly


def replay(run, tools, out, legacy_dir, typed_dir):
    """Lower fresh source emissions, replay both at the pins and retain the RTL."""
    legacy_core = json.loads((legacy_dir / 'assembly.json').read_text())
    legacy_frontend = json.loads((legacy_dir / 'frontend-assembly.json').read_text())
    typed_core = legacy_assembly(typed_dir / 'core-interface.json', addr_bits=DEPTH.bit_length() - 1)
    typed_frontend = legacy_assembly(typed_dir / 'frontend-interface.json')
    for legacy, typed in ((legacy_core, typed_core), (legacy_frontend, typed_frontend)):
        if legacy != typed:
            raise RuntimeError(f'Typed emission changed the assembly inventory for {legacy["module"]}')
    if legacy_core['module'] != f'pinwheel_streaming_ready_core_d{DEPTH}':
        raise RuntimeError(f'The SPI pin replay requires depth {DEPTH}')
    for stem in COMPONENTS:
        if not cmp(legacy_dir / f'{stem}.mlir', typed_dir / f'{stem}.mlir', shallow=False):
            raise RuntimeError(f'Typed emission changed {stem}.mlir')

    out.mkdir(parents=True, exist_ok=False)
    package = out / 'package.sv'
    tt = out / 'tt.sv'
    bridge = out / 'bridge.sv'
    package_text = package_source(typed_core, typed_frontend)
    if package_text != package_source(legacy_core, legacy_frontend):
        raise RuntimeError('Typed emission changed the SPI package wiring')
    package.write_text(package_text)
    tt.write_text(tt_source(DEPTH))
    bridge.write_text(bridge_source(DEPTH))

    for name, emitted in (('legacy', legacy_dir), ('typed', typed_dir)):
        directory = out / name
        directory.mkdir()
        for stem in COMPONENTS:
            lower = directory / f'{stem}-lowering.mlir'
            lowering_copy(emitted / f'{stem}.mlir', lower)
            source = directory / f'{stem}.sv'
            source.write_text(run([tools['circt'], lower, *LOWERING_PASSES],
                                  f'spi-{name}-{stem}-export', timeout=180))

    for stem in COMPONENTS:
        for filename in (f'{stem}-lowering.mlir', f'{stem}.sv'):
            if not cmp(out / 'legacy' / filename, out / 'typed' / filename, shallow=False):
                raise RuntimeError(f'Typed lowering changed {filename}')

    results = {}
    for name in ('legacy', 'typed'):
        directory = out / name
        rtl = [directory / f'{stem}.sv' for stem in COMPONENTS]
        executable = directory / 'bridge.vvp'
        run([tools['iverilog'], '-g2012', '-s', 'streaming_quad_host_bridge',
             '-o', executable, *rtl, package, tt, bridge], f'spi-{name}-bridge-compile')
        results[name] = run_cases(tools['vvp'], executable, directory / 'wire.bin')
        print(f'SPI {name} pin replay: {len(results[name]["cases"])} cases passed', flush=True)

    if results['legacy'] != results['typed'] or not cmp(
            out / 'legacy' / 'wire.bin', out / 'typed' / 'wire.bin', shallow=False):
        raise RuntimeError('Legacy and typed source RTL differ at the SPI public pins')
    return dict(backends=results, source_mlir_identical=True, lowering_inputs_identical=True,
                rtl_identical=True, shared_pin_wrapper=True, public_traces_identical=True)
