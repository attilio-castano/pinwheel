"""Compile a passive 125 kbit/s Classical CAN capture and decode it on the host."""
from streaming_compile import Cell
from streaming_ready_compile import Guard, Instruction, Pins, lower


# Lean `StreamingCANClock.Admits`: the receive image below is proved only at
# exactly 32 core clocks per bit, i.e. a 4 MHz core for 125 kbit/s. Its cell
# durations are fixed, so changing either rate needs a new proof, not just a
# new constant.
CORE_HZ = 4_000_000
BIT_RATE = 125_000
BIT_CYCLES = CORE_HZ // BIT_RATE
if CORE_HZ % BIT_RATE or BIT_CYCLES != 32:
    raise ValueError('The CAN receive image is proved only at 32 core clocks per bit')
CAPTURE_BITS = 64
PROTECTED_BITS = 42


def can_receive_image():
    """Wait for dominant SOF, then sample raw0 at the centers of 64 slots."""
    start = Instruction('drive_wait', guard=Guard(mask=1), pins=Pins())
    receive = Instruction('stream', Cell(low_cycles=14, high_cycles=17, receive=True))
    return lower((start, receive, Instruction('halt')))


def _read_bits(bits):
    value = 0
    for bit in bits:
        value = (value << 1) | bit
    return value


def _crc15(bits):
    remainder = 0
    for bit in bits:
        feedback = bit ^ bool(remainder & 0x4000)
        remainder = (remainder << 1) & 0x7fff
        if feedback:
            remainder ^= 0x4599
    return remainder


def _destuff(bits):
    protected = []
    previous, run, cursor = None, 0, 0
    while len(protected) < PROTECTED_BITS:
        if cursor == len(bits):
            return None
        bit = bits[cursor]
        protected.append(bit)
        cursor += 1
        run = run + 1 if bit == previous else 1
        previous = bit
        if run == 5:
            # A required stuff bit still belongs to the protected region when
            # the fifth equal bit was the final bit of the CRC sequence.
            if cursor == len(bits) or bits[cursor] == previous:
                return None
            previous, run = bits[cursor], 1
            cursor += 1
    return protected, cursor


def decode_can_frame(bits):
    """Return (11-bit identifier, byte) for an acknowledged base frame, or None."""
    if type(bits) is not tuple or len(bits) != CAPTURE_BITS or any(type(bit) is not bool for bit in bits):
        raise ValueError('Expected exactly 64 chronological CAN line samples')
    result = _destuff(bits)
    if result is None:
        return None
    protected, cursor = result
    if protected[0] or any(protected[12:18]) or not protected[18]:
        return None  # Dominant SOF, data RTR/IDE/r0, and DLC 1.
    if _read_bits(protected[27:]) != _crc15(protected[:27]):
        return None
    trailer = bits[cursor:]
    if len(trailer) < 10 or trailer[:2] != (True, False) or not all(trailer[2:]):
        return None  # CRC delimiter, external ACK, ACK delimiter, EOF, then recessive padding.
    return _read_bits(protected[1:12]), _read_bits(protected[19:27])
