"""Explicit five-pad package binding and external driver observations."""
from dataclasses import dataclass

from pinwheel_host import Pins

OUTPUT_MASK = 0x1c
INPUT_MASK = 0x03
PAD_MAP = dict(logical_inputs=[0, 1], logical_outputs=[2, 3, 4],
               spi=dict(mosi=2, sclk=3, cs_n=4, miso=0),
               uart=dict(tx=2, rx=0),
               i2c=dict(scl_drive=2, scl_sense=0, sda_drive=3, sda_sense=1,
                        board_links=[[0, 2], [1, 3]]))


@dataclass(frozen=True)
class PadDrive:
    """External strong drivers, weak pullups and two declared I2C board links."""
    levels: int = 0
    enabled: int = 0
    links: int = 0
    pullups: int = 0xff

    def __post_init__(self):
        for name in ('levels', 'enabled', 'pullups'):
            value = getattr(self, name)
            if type(value) is not int or not 0 <= value <= 255:
                raise ValueError('External pad ' + name + ' must fit eight bits')
        if type(self.links) is not int or not 0 <= self.links < 4:
            raise ValueError('Board links must fit two bits')


@dataclass(frozen=True)
class PadObservation:
    status: int
    levels: int
    enabled: int
    wires: int
    known: int

    @property
    def logical(self):
        # Validate the physical contract before decoding. An old map must fail,
        # rather than becoming plausible logical pins by a masking operation.
        if self.levels & ~OUTPUT_MASK or self.enabled & ~OUTPUT_MASK:
            raise RuntimeError('DUT violates five-pad output map: ' + repr(self))
        return Pins(self.status, self.levels >> 2, self.enabled >> 2)

    def bit(self, pad):
        if not self.known & (1 << pad):
            raise RuntimeError('Unknown resolved pad ' + str(pad))
        return (self.wires >> pad) & 1

    def validate_drive(self, drive):
        if self.enabled & drive.enabled:
            raise RuntimeError('External peer drives a DUT-owned package pad')
        connected = (5 if drive.links & 1 else 0) | (10 if drive.links & 2 else 0)
        if connected & ((self.levels & self.enabled) | (drive.levels & drive.enabled)):
            raise RuntimeError('Declared I2C board links require open-drain low/release drivers')
        required = INPUT_MASK | self.enabled | drive.enabled
        if drive.links & 1:
            required |= 5
        if drive.links & 2:
            required |= 10
        if self.known & required != required:
            raise RuntimeError('Unknown/contention on resolved package pads: ' + repr(self))
        self.logical
