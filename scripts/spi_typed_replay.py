"""Compare legacy and typed source RTL at the existing SPI public pins."""

from streaming_8x4_spi_modes import run_cases


def replay(tools, out, engine):
    """Run both builds through the same independent SPI peer and corpus."""
    out.mkdir(parents=True, exist_ok=False)
    results = {}
    for name, build in (('legacy', engine.legacy), ('typed', engine.typed)):
        directory = out / name
        directory.mkdir()
        results[name] = run_cases(tools['vvp'], build.executable, directory / 'wire.bin', depth=engine.depth)
        print(f'SPI depth {engine.depth} {name} pin replay: {len(results[name]["cases"])} cases passed', flush=True)

    if (results['legacy'] != results['typed'] or
            (out / 'legacy/wire.bin').read_bytes() != (out / 'typed/wire.bin').read_bytes()):
        raise RuntimeError('Legacy and typed source RTL differ at the SPI public pins')
    return dict(backends=results, source_mlir_identical=True, lowering_inputs_identical=True,
                rtl_identical=True, shared_pin_wrapper=True, public_traces_identical=True)
