"""Protocol interpretation above Pinwheel's unchanged raw result mailbox."""
from dataclasses import dataclass
from typing import Literal

from pinwheel_host import Result


@dataclass(frozen=True)
class I2CReadResult:
    outcome: Literal['success', 'timeout', 'nack_or_bus_fault']
    payload: tuple[int, ...] | None
    overrun: bool
    rejected: bool


def i2c_read_result(result: Result, *, byte_count: int) -> I2CReadResult:
    """Decode the compact one/two-byte read frontend's retained result.

    The caller supplies the byte count of the committed read program. On
    success, slots 0..7 hold the first byte in MSB-first wire order; slots 8..15
    hold the second. A one-byte success requires the unused upper slots zero.
    NACK and guarded bus fault intentionally share one outcome. ACK observations
    reuse payload slots before reception, so all samples are discarded on any
    failure. This decoder is not for the older precise-ACK one-byte program.
    """
    if type(byte_count) is not int or byte_count not in (1, 2):
        raise ValueError('I2C read byte count must be 1 or 2')
    if type(result.samples) is not int or not 0 <= result.samples < 1 << 16:
        raise ValueError('I2C captures must be an unsigned 16-bit result')
    if type(result.outcome) is not int or result.outcome not in (5, 6, 7):
        raise ValueError('I2C result must have a terminal engine outcome')
    if result.outcome == 6:
        return I2CReadResult('timeout', None, result.overrun, result.rejected)
    if result.outcome == 7:
        return I2CReadResult('nack_or_bus_fault', None, result.overrun, result.rejected)
    if byte_count == 1 and result.samples >> 8:
        raise ValueError('One-byte I2C success contains unexpected upper captures')
    payload = tuple(sum(((result.samples >> (8 * byte + bit)) & 1) << (7 - bit)
                        for bit in range(8)) for byte in range(byte_count))
    return I2CReadResult('success', payload, result.overrun, result.rejected)
