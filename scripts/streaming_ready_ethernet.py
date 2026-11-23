"""Compile a 10 Mbit/s SNI transmit image and prepare minimum Ethernet frames."""
from binascii import crc32

from streaming_compile import Cell
from streaming_ready_compile import Guard, Instruction, Pins, lower


# Lean `StreamingEthernetClock`: the image is proved only with exactly six core
# clocks per SNI bit, so a 60 MHz core locked to the PHY's 10 MHz TX_CLK, with
# TX_CLK high for under three core clocks. This is above the 20 ns physical
# target (50 MHz).
CORE_HZ = 60_000_000
BIT_RATE = 10_000_000
BIT_CYCLES = CORE_HZ // BIT_RATE
if CORE_HZ % BIT_RATE or BIT_CYCLES != 6:
    raise ValueError('The Ethernet transmit image is proved only at six core clocks per bit')
PREAMBLE = b'\x55' * 7 + b'\xd5'
FRAME_BYTES = 64
WIRE_BITS = (len(PREAMBLE) + FRAME_BYTES) * 8


def ethernet_sni_image():
    """Arm on raw1, align to raw0, then emit TXD/TX_EN on outputs 0/1."""
    idle = Pins(enabled=3)
    high = Guard(mask=1, expected=1)
    source = [Instruction('drive_wait', guard=guard, pins=idle) for guard in
              (Guard(mask=2, expected=2), high, Guard(mask=1), high)]
    stream = Cell(low_levels=2, high_levels=2, low_enabled=3, high_enabled=3, transmit=True)
    return lower((*source, Instruction('stream', stream, high), Instruction('halt')), idle_enabled=3)


def minimum_frame(destination, source, ether_type, payload):
    """Prepare preamble, SFD, padded MAC body and little-endian Ethernet FCS."""
    if any(type(address) is not bytes or len(address) != 6 for address in (destination, source)):
        raise ValueError('Ethernet addresses must be six bytes')
    if type(ether_type) is not int or not 0x600 <= ether_type <= 0xffff:
        raise ValueError('Expected an Ethernet II EtherType')
    if type(payload) is not bytes or len(payload) > 46:
        raise ValueError('Minimum Ethernet payload must contain at most 46 bytes')
    body = destination + source + ether_type.to_bytes(2, 'big') + payload.ljust(46, b'\x00')
    return PREAMBLE + body + crc32(body).to_bytes(4, 'little')


def serial_bits(frame):
    """Convert a complete minimum frame to chronological, LSB-first symbols."""
    if type(frame) is not bytes or len(frame) != WIRE_BITS // 8:
        raise ValueError('Expected preamble and one minimum Ethernet frame')
    return tuple(bool(byte & (1 << bit)) for byte in frame for bit in range(8))
