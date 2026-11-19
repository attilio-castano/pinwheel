"""Compile and decode one 4 MHz keyboard-to-host PS/2 receive frame."""
from streaming_compile import Cell
from streaming_ready_compile import Guard, Instruction, lower


FRAME_BITS = 11
CORE_HZ = 4_000_000


def ps2_receive_image():
    """Sense clock on raw0 and data on raw1, with all outputs released."""
    receive = Instruction('stream', Cell(high_cycles=217, rx_input=1, receive=True), Guard(mask=1))
    return lower((receive, Instruction('halt')))


def decode_ps2_frame(bits):
    """Return the LSB-first payload if the exact frame has valid framing and odd parity."""
    if type(bits) is not tuple or len(bits) != FRAME_BITS or any(type(bit) is not bool for bit in bits):
        raise ValueError('Expected exactly 11 chronological PS/2 frame bits')
    if bits[0] or not bits[-1] or sum(bits[1:-1]) % 2 != 1:
        return None
    return sum(int(bit) << index for index, bit in enumerate(bits[1:9]))
