"""Prepare one sampled-ready hardware configuration for proofs and pin replay."""

from dataclasses import dataclass
import json
from pathlib import Path

from streaming_ready_artifacts import LOWERING_PASSES, lowering_copy
from streaming_ready_wrapper import bridge_source, package_source, tt_source


COMPONENTS = ('core', 'frontend')


@dataclass(frozen=True)
class EngineBuild:
    rtl: dict[str, Path]
    executable: Path


@dataclass(frozen=True)
class EngineArtifacts:
    addr_bits: int
    out: Path
    legacy: EngineBuild
    typed: EngineBuild
    package: Path
    tt: Path
    bridge: Path

    @property
    def depth(self):
        return 1 << self.addr_bits


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


def prepare(run, tools, out, addr_bits, legacy_dir, typed_dir):
    """Check both source emissions and build the common public-pin shell."""
    if type(addr_bits) is not int or addr_bits not in (1, 2):
        raise ValueError('Qualified streaming address width must be 1 or 2')
    depth = 1 << addr_bits
    legacy, typed = {}, {}
    for stem, assembly_name, options in (
            ('core', 'assembly.json', {'addr_bits': addr_bits}),
            ('frontend', 'frontend-assembly.json', {})):
        legacy[stem] = json.loads((legacy_dir / assembly_name).read_text())
        typed[stem] = legacy_assembly(typed_dir / f'{stem}-interface.json', **options)
        if legacy[stem] != typed[stem]:
            raise RuntimeError(f'Typed emission changed the assembly inventory for {stem}')
        if (legacy_dir / f'{stem}.mlir').read_bytes() != (typed_dir / f'{stem}.mlir').read_bytes():
            raise RuntimeError(f'Typed emission changed {stem}.mlir')
        with (typed_dir / assembly_name).open('x') as file:
            json.dump(typed[stem], file, indent=2)
            file.write('\n')
    if typed['core']['module'] != f'pinwheel_streaming_ready_core_d{depth}':
        raise RuntimeError(f'Emitted streaming core does not have depth {depth}')

    out.mkdir(parents=True, exist_ok=False)
    package = out / 'package.sv'
    tt = out / 'tt.sv'
    bridge = out / 'bridge.sv'
    package_text = package_source(typed['core'], typed['frontend'])
    if package_text != package_source(legacy['core'], legacy['frontend']):
        raise RuntimeError('Typed emission changed the sampled-ready package wiring')
    package.write_text(package_text)
    tt.write_text(tt_source(depth))
    bridge.write_text(bridge_source(depth))

    builds = {}
    for name, emitted in (('legacy', legacy_dir), ('typed', typed_dir)):
        directory = out / name
        directory.mkdir()
        rtl = {}
        for stem in COMPONENTS:
            lower = directory / f'{stem}-lowering.mlir'
            lowering_copy(emitted / f'{stem}.mlir', lower)
            rtl[stem] = directory / f'{stem}.sv'
            rtl[stem].write_text(run([tools['circt'], lower, *LOWERING_PASSES],
                                     f'd{depth}-{name}-{stem}-export', timeout=180))
        builds[name] = EngineBuild(rtl, directory / 'bridge.vvp')

    for stem in COMPONENTS:
        for filename in (f'{stem}-lowering.mlir', f'{stem}.sv'):
            if (out / 'legacy' / filename).read_bytes() != (out / 'typed' / filename).read_bytes():
                raise RuntimeError(f'Typed lowering changed {filename}')

    for name, build in builds.items():
        run([tools['iverilog'], '-g2012', '-s', 'streaming_quad_host_bridge',
             '-o', build.executable, *build.rtl.values(), package, tt, bridge],
            f'd{depth}-{name}-bridge-compile')
    return EngineArtifacts(addr_bits, out, builds['legacy'], builds['typed'], package, tt, bridge)
