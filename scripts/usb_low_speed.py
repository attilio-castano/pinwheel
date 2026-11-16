"""Compile an endpoint-zero, low-speed device descriptor read for the USB target."""
from dataclasses import dataclass
from itertools import groupby

from streaming_compile import Cell
from streaming_ready_compile import Guard, Instruction, Pins, WaitLimit, encode, lower


SE0, K, J = range(3)
USB_RECEIVE_DATA1 = 5


def bits(value, width):
    return [(value >> index) & 1 for index in range(width)]


def crc5(address_endpoint):
    register = 31
    for bit in bits(address_endpoint, 11):
        register = (register >> 1) ^ (0x14 * ((register ^ bit) & 1))
    return register ^ 31


def checksum(data):
    # The reflected CRC register emits its least significant bit first.
    register = 0xffff
    for bit in (bit for byte in data for bit in bits(byte, 8)):
        register = (register >> 1) ^ (0xa001 * ((register ^ bit) & 1))
    return bits(register ^ 0xffff, 16)


def wire_encode(packet_id, body):
    last, ones, result = J, 0, []
    for bit in bits(0x80, 8) + bits(packet_id, 8) + body:
        if not bit:
            last = 3 - last
        result.append(last)
        ones = ones + 1 if bit else 0
        if ones == 6:
            last = 3 - last
            result.append(last)
            ones = 0
    return result


def token_packet(packet_id):
    return wire_encode(packet_id, bits(0, 11) + bits(crc5(0), 5))


def data_packet(packet_id, payload):
    return wire_encode(packet_id, [bit for byte in payload for bit in bits(byte, 8)] + checksum(payload))


def static_tx(symbols):
    """Pair alternating J/K runs, accounting for the fetch and reserve edges."""
    runs = [(line, 16 * len(list(group))) for line, group in groupby(symbols)]
    rows, carry, index = [], 0, 0
    while index < len(runs):
        line, clocks = runs[index]
        pair = (index + 2 < len(runs) and line in (J, K)
                and runs[index + 1][0] in (J, K) and runs[index + 2][0] == line)
        if pair:
            following, high_clocks = runs[index + 1]
            rows.append(Instruction('pulse', Cell(clocks - 1 - carry, high_clocks,
                low_levels=line, high_levels=following, low_enabled=3, high_enabled=3)))
            carry = 1
            index += 2
        else:
            rows.append(Instruction('pulse', Cell(1, clocks - 3 - carry,
                low_levels=line, high_levels=line, low_enabled=3, high_enabled=3)))
            carry = 0
            index += 1
    return rows


def receive_handshake():
    def wait(line, budget):
        return Instruction('drive_wait', pins=Pins(), guard=Guard(3, line, WaitLimit.misses(budget)))

    return (wait(K, 127), Instruction('stream', Cell(6, 9, receive=True)),
        wait(SE0, 12), Instruction('pulse', Cell(1, 15)), wait(SE0, 1), wait(J, 32), Instruction('halt'))


@dataclass(frozen=True)
class Stage:
    words: tuple[int, ...]
    receive_bits: int

    def __post_init__(self):
        if not 1 <= len(self.words) <= 64 or not all(0 <= word < 2**64 for word in self.words):
            raise ValueError('USB stage must fit the 64-row store')
        if self.receive_bits not in (16, 64):
            raise ValueError('USB stage must receive an ACK or eight data bytes')


def descriptor_read():
    """Three transactions. TX pulses run at 16 core clocks per symbol."""
    eop = [SE0, SE0, J]
    gap = eop + [J, J]
    setup = token_packet(0x2d) + gap + data_packet(0xc3, bytes.fromhex('8006000100000800')) + eop
    data = token_packet(0x69) + eop
    status = token_packet(0xe1) + gap + data_packet(0x4b, b'') + eop

    def handshake(wave):
        return Stage(lower((*static_tx(wave), *receive_handshake())).words, 16)

    rows = static_tx(data)
    return (handshake(setup), Stage((*map(encode, rows), USB_RECEIVE_DATA1), 64), handshake(status))
