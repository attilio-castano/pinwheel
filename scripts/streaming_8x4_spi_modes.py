"""Replay SPI modes 0 and 2 on the frozen 8×4 release RTL and CMOS5L netlist."""

import argparse
import json
from pathlib import Path
import time

from streaming_8x4_bringup import DEPTH, TOP
from streaming_8x4_e982_native import require, sha, write
from streaming_8x4_jane_street_behavior import GDS, NETLIST, PDK_MODELS, RTL, artifact, compile_model
from streaming_peers import StreamingSPIPeer
from streaming_ready_compile import spi_image
from streaming_ready_transport import ReadyHost
from streaming_ready_wrapper import bridge_source
from streaming_rtl import QuadRTL
from streaming_transport import Flags, Opcode, QuadTransport
from streaming_wire_cases import EdgeTrace


BIT_COUNTS = (1, 33, 257)
MIDSTREAM_STALL_CYCLES = 4_096


def exchange(rtl, transport, loaded, mode, count):
    size = (count + 7) // 8
    tx = bytes((0xD3 + 73 * i) & 255 for i in range(size))
    rx = bytes((0xA5 + 151 * i) & 255 for i in range(size))
    peer = StreamingSPIPeer(tx, rx, mode=mode, bit_count=count)
    rtl.device = peer
    pending = loaded.submit(peer.expected, bit_count=count)
    transport.idle(128)
    waiting = pending.pump(max_bits=0)
    require(waiting.flags & Flags.WAIT_TX and not peer.clock_edges,
            'Initial TX starvation advanced the SPI clock')
    if count == BIT_COUNTS[-1]:
        pending.pump(max_bits=32)
        transport.idle(512)
        require(pending.tx_accepted == 32 and len(peer.bits) == 32 and peer.selected,
                'Initial chunk did not reach an in-transfer queue stall')
        transport.idle(MIDSTREAM_STALL_CYCLES)
        require(peer.selected and len(peer.bits) == 32,
                'Queue stall changed chip selection or consumed another SPI bit')
    terminal = pending.wait(max_exchanges=(count + 31) // 32 * 3 + 20)
    require(not terminal.fault and pending.tx_accepted == count and len(pending.rx_bits) == count,
            'SPI did not complete the exact owned bit count')
    observation = peer.check(pending.rx_bits, require_stall=count == BIT_COUNTS[-1])
    if count == BIT_COUNTS[-1]:
        require(observation['low_extra_edges'] >= MIDSTREAM_STALL_CYCLES,
                'Independent peer did not observe the programmed clock stretch')
    released = pending.release()
    require(released.tag == pending.tag and not released.busy and not released.retained and
            pending.last.rx_start == count and pending.last.rx_valid == 0,
            'SPI owner was not released after exact acknowledgment')
    require(rtl.observation.bit(4) and rtl.observation.bit(3) == int(mode == 2),
            'SPI public pins did not return to their required idle levels')
    rtl.device = None
    return dict(mode=mode, count=count, owner_tag=pending.tag,
                tx_bytes=tx.hex(), rx_bytes=rx.hex(), end_edge=rtl.cycle, peer=observation)


def run_cases(vvp, executable, trace_path):
    trace = EdgeTrace(trace_path)
    images, cases = [], []
    try:
        with QuadRTL(vvp, executable, record_limit=0, record_sink=trace) as rtl:
            transport = QuadTransport(rtl)
            host = ReadyHost(transport, depth=DEPTH)
            host.initialize()
            for mode in (0, 2):
                loaded = host.load(spi_image(mode=mode))
                images.append(dict(mode=mode, words=list(loaded.image.words), generation=loaded.generation,
                                   idle_levels=loaded.image.idle_levels, idle_enabled=loaded.image.idle_enabled))
                for count in BIT_COUNTS:
                    cases.append(exchange(rtl, transport, loaded, mode, count))
            require([image['generation'] for image in images] == [1, 2] and
                    len({case['owner_tag'] for case in cases}) == len(cases) and
                    transport.opcode_counts[Opcode.COMMIT] == 2 and
                    all(transport.opcode_counts[opcode] == len(cases)
                        for opcode in (Opcode.START, Opcode.RELEASE)) and
                    transport.opcode_counts[Opcode.WARM_RESET] == 0,
                    'SPI images did not execute successively on the same instance')
    finally:
        recorded = trace.close()
    return dict(images=images, cases=cases, trace=recorded, exit_code=rtl.process.returncode)


def run(release, models, iverilog, vvp, out):
    netlist = release / 'release' / (TOP + '.v')
    hashes = {netlist: NETLIST, release / 'release' / (TOP + '.gds'): GDS}
    hashes.update({release / 'src' / name: digest for name, digest in RTL.items()})
    hashes.update({models / name: digest for name, digest in PDK_MODELS.items()})
    for path, expected in hashes.items():
        require(sha(path) == expected, f'Frozen release or vendor model hash differs for {path}')

    out.mkdir(parents=True, exist_ok=False)
    directory = Path(__file__).resolve().parent
    input_paths = [*hashes, iverilog, vvp, Path(__file__).resolve(),
                   *(directory / name for name in ('streaming_compile.py', 'streaming_peers.py',
                      'streaming_ready_compile.py', 'streaming_ready_transport.py', 'streaming_transport.py',
                      'streaming_rtl.py', 'streaming_ready_wrapper.py', 'streaming_wire_cases.py',
                      'streaming_8x4_jane_street_behavior.py'))]
    result = dict(schema='pinwheel.streaming-8x4-spi-modes.v1', passed=False,
                  inputs={str(path): artifact(path) for path in input_paths}, stages={}, backends={})
    started = time.monotonic()
    try:
        bridge = out / 'bridge.sv'
        bridge.write_text(bridge_source(DEPTH))
        result['bridge'] = artifact(bridge)
        sources = {'rtl': [release / 'src' / name for name in RTL],
                   'gate': [*(models / name for name in PDK_MODELS), netlist]}
        for name, files in sources.items():
            executable, result['stages'][name] = compile_model(iverilog, out, name, [*files, bridge])
            result['backends'][name] = run_cases(vvp, executable, out / (name + '-wire.bin'))
            print(f'{name}: {len(result["backends"][name]["cases"])} cases passed', flush=True)
            write(out / 'progress.json', result)
        require(result['backends']['rtl'] == result['backends']['gate'],
                'Release RTL and gate public traces or results differ')
        require(result['inputs'] == {str(path): artifact(path) for path in input_paths},
                'A replay input changed while running')
        result['passed'] = True
    except BaseException as error:
        result['error'] = repr(error)
        raise
    finally:
        result['elapsed_seconds'] = time.monotonic() - started
        write(out / 'receipt.json', result)
    print(json.dumps(dict(passed=True, cases=len(result['backends']['rtl']['cases']),
                          trace=result['backends']['rtl']['trace'], receipt=str(out / 'receipt.json')), indent=2))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ('release', 'models', 'iverilog', 'vvp', 'out'):
        parser.add_argument('--' + name, type=Path, required=True)
    args = parser.parse_args()
    run(args.release.resolve(strict=True), args.models.resolve(strict=True),
        args.iverilog.resolve(strict=True), args.vvp.resolve(strict=True), args.out.resolve())


if __name__ == '__main__':
    main()
