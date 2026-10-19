"""Nine-row 8N1 receiver image for the unchanged sampled-ready processor.

The one stream is RX-only and START must supply eight cells. Timings include
fetch/boundary/check overhead; low+high+one is the stream sample period.
"""
from dataclasses import dataclass

from streaming_compile import Cell, integer
from streaming_ready_compile import (Guard, Instruction, Pins, Source, WaitLimit,
    lower, validate_image)

QUARTERS = (4, 12, 128)
UART_BITS = 8
UART_ROWS = 9


@dataclass(frozen=True)
class Profile:
    quarter_cycles: int = 4
    rx_input: int = 0

    def __post_init__(self):
        integer(self.quarter_cycles, 4, 128, 'UART quarter cycles')
        integer(self.rx_input, 0, 1, 'UART RX input')

    @property
    def bit_cycles(self): return 4 * self.quarter_cycles


def instructions(profile):
    profile.__post_init__()
    q, mask = profile.quarter_cycles, 1 << profile.rx_input
    def wait(level, limit):
        return Instruction('drive_wait', guard=Guard(mask, mask if level else 0, limit), pins=Pins())
    def pulse(low, high):
        return Instruction('pulse', Cell(low, high))
    return (wait(True, WaitLimit.unbounded()), wait(False, WaitLimit.unbounded()),
        pulse(q - 2, q - 2), wait(False, WaitLimit.misses(1)), pulse(q - 2, q - 1),
        Instruction('stream', Cell(2 * q - 1, 2 * q, rx_input=profile.rx_input, receive=True)),
        pulse(q - 2, q - 2), wait(True, WaitLimit.misses(1)), Instruction('halt'))


def uart_image(quarter_cycles=4, rx_input=0):
    """Compile one frame per START8; every protocol output remains released."""
    return lower(instructions(Profile(quarter_cycles, rx_input)))


def validate_uart_image(image):
    """Revalidate the generic certificate and the exact UART timing profile."""
    validate_image(image)
    source = image.source
    if len(source.instructions) != UART_ROWS or image.certificate.stream_row != 5:
        raise ValueError('UART requires its exact nine-row receiver shape')
    stream = source.instructions[5]
    if stream.cell is None:
        raise ValueError('UART stream has no timing cell')
    high = stream.cell.high_cycles
    if high % 2:
        raise ValueError('UART HIGH duration is not two quarters')
    profile = Profile(high // 2, stream.cell.rx_input)
    if source != Source(instructions(profile), 0, 0):
        raise ValueError('UART source differs from the exact released-pin 8N1 program')
    return profile


def lean_certificate(image):
    """Automatic kernel equality to the independently defined Lean image."""
    p = validate_uart_image(image)
    words = ', '.join(map(str, image.words))
    namespace = f'Pinwheel.Artifact.StreamingUARTImageQ{p.quarter_cycles}Input{p.rx_input}'
    return ('import Pinwheel.Program.StreamingUART\n'
        'open Pinwheel.Program.StreamingUART\n'
        f'namespace {namespace}\n'
        f'def profile : Profile := ⟨⟨{p.quarter_cycles - 4}, by decide⟩, {p.rx_input}⟩\n'
        f'example : (image profile).words = [{words}] := by decide +kernel\n'
        f'end {namespace}\n')


def reverse_byte(value):
    integer(value, 0, 255, 'UART byte')
    return sum(((value >> index) & 1) << (7 - index) for index in range(8))


@dataclass(frozen=True)
class UartResult:
    raw_bits: tuple
    value: int | None
    complete: bool
    fault: bool
    payload_valid: bool


def project(raw_bits, *, fault=False, uart_timing=True):
    """RX tuples are chronological; UART sends the least significant bit first.

    A bad stop retains eight data bits, but never becomes a valid payload.
    Narrow sampling-window diagnostics are explicitly outside valid UART timing.
    """
    if (type(raw_bits) is not tuple or len(raw_bits) > 8 or
            any(type(bit) is not bool for bit in raw_bits) or
            type(fault) is not bool or type(uart_timing) is not bool):
        raise ValueError('UART projection requires at most eight immutable Boolean samples')
    complete = len(raw_bits) == 8
    value = sum(int(bit) << index for index, bit in enumerate(raw_bits)) if complete else None
    return UartResult(raw_bits, value, complete, fault, complete and not fault and uart_timing)
