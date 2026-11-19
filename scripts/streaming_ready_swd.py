"""Compile and decode a fixed, successful point-to-point SWD DPIDR read."""
from streaming_ready_compile import Instruction, lower
from streaming_compile import Cell, integer


REPLY_BITS = 36
OK_ACK = (True, False, False)


def dpidr_image(half_cycles=4):
    """DP read at address zero, with the target already operating in SWD mode."""
    integer(half_cycles, 3, 256, 'SWD half cycles')

    def pulse(bit=False, *, drive=True):
        enabled = 3 if drive else 1
        data = 2 * int(bit)
        return Instruction('pulse', Cell(half_cycles, half_cycles, low_levels=data,
            low_enabled=enabled, high_levels=data | 1, high_enabled=enabled))

    request_fields = (False, True, False, False)  # APnDP, RnW, A2, A3.
    request = (True, *request_fields, bool(sum(request_fields) % 2), False, True)
    turnaround = pulse(drive=False)
    receive = Instruction('stream', Cell(half_cycles, half_cycles, low_enabled=1, high_levels=1,
        high_enabled=1, rx_input=1, receive=True))
    return lower((*map(pulse, request), turnaround, receive, turnaround,
                  *((pulse(),) * 8), Instruction('halt')), idle_levels=0, idle_enabled=1)


def decode_dpidr(bits):
    """Return the word when ACK and even parity validate the exact response."""
    if type(bits) is not tuple or len(bits) != REPLY_BITS or any(type(bit) is not bool for bit in bits):
        raise ValueError('Expected exactly 36 chronological SWD response bits')
    if bits[:3] != OK_ACK or sum(bits[3:]) % 2:
        return None
    return sum(int(bit) << index for index, bit in enumerate(bits[3:-1]))
