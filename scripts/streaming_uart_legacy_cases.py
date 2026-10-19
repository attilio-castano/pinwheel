"""Long SPI/JTAG regressions on the unchanged sampled-ready UART hardware.

Only the uploaded program changes. The Ready compiler must reproduce the old
qualified words exactly before this helper opens any simulator or host link.
The fresh coordinator kernel-checks these Ready source images before calling it.
"""
from pathlib import Path
import re

from streaming_compile import spi_image, jtag_image
from streaming_ready_compile import Instruction, lower, validate_image
from streaming_transport import Code, Flags
from streaming_wire_cases import run_stream

SCHEMA = 'pinwheel.streaming-uart-legacy-wire.v1'
WORKLOADS = (('spi', 32768), ('jtag', 4097))


def require(value, message):
    if not value:
        raise RuntimeError(message)


def ready_image(protocol):
    if protocol not in ('spi', 'jtag'):
        raise ValueError('Expected SPI or JTAG')
    previous = spi_image() if protocol == 'spi' else jtag_image()
    ready = lower((Instruction(row.operation, row.cell) for row in previous.source.instructions),
        idle_levels=previous.idle_levels, idle_enabled=previous.idle_enabled)
    validate_image(ready)
    require(ready.words == previous.words, 'Lift changed a qualified instruction word')
    return ready


def check_legacy_cases(report):
    require(report.get('schema') == SCHEMA and report.get('passed') is True and
        type(report.get('depth')) is int and report['depth'] in (2, 4),
        'Incomplete lifted SPI/JTAG wire corpus')
    rows = report.get('cases')
    require(type(rows) is list and len(rows) == len(WORKLOADS), 'Both long workloads are mandatory')
    for row, (protocol, bits) in zip(rows, WORKLOADS):
        require(row.get('passed') is True and row.get('protocol') == protocol and
            row.get('bits') == bits and row.get('depth') == report['depth'] and
            row.get('fault') is None and row.get('start_count') == 1 and
            row.get('owner_tag') == 65537 and
            row.get('image_words') == list(ready_image(protocol).words),
            'Lifted workload changed its program, transfer or single owner')
        trace, released = row.get('trace', {}), row.get('release', {})
        require(type(row.get('physical_edges')) is int and row['physical_edges'] > bits and
            trace.get('edges') == row['physical_edges'] and trace.get('bytes') == row['physical_edges'] * 20 and
            re.fullmatch(r'[0-9a-f]{64}', trace.get('sha256', '')) and
            type(row.get('exchange_rx_max')) is int and 0 <= row['exchange_rx_max'] <= 32 and
            released.get('code') == int(Code.ACCEPTED) and released.get('tag') == row['owner_tag'] and
            type(released.get('flags')) is int and released['flags'] == int(Flags.VALID) and
            released.get('tx_accepted') == 0 and released.get('rx_valid') == 0 and released.get('rx_queued') == 0,
            'Lifted workload omitted bounded service, trace or matching RELEASE')
    require(report.get('physical_edges') == sum(row['physical_edges'] for row in rows),
        'Lifted workload edge count differs')


def run_legacy_cases(vvp, executable, directory, *, depth):
    require(type(depth) is int and depth in (2, 4), 'Expected a qualified queue depth')
    for protocol, _ in WORKLOADS:
        ready_image(protocol)
    directory = Path(directory)
    directory.mkdir(parents=True, exist_ok=False)
    rows = [run_stream(vvp, executable, directory / protocol,
        protocol=protocol, bits=bits, depth=depth) for protocol, bits in WORKLOADS]
    report = dict(schema=SCHEMA, passed=all(row.get('passed') is True for row in rows),
        depth=depth, cases=rows, physical_edges=sum(row.get('physical_edges', 0) for row in rows))
    check_legacy_cases(report)
    return report
