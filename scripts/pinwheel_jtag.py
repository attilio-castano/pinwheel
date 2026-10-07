"""A bounded eight-bit JTAG data-register scan on the existing paired engine.

This assumes a target with an eight-bit data register selected after TAP reset.
It does not select an instruction, implement a chain, or read a 32-bit IDCODE.
TDI uses the accepted START byte; capture slot k receives wire bit k (LSB first).
For a resolved package peer with clock-to-output delay tco, the declared receive
envelope is half_cycles >= tco + 3: one callback edge and two sampler edges.
"""
from pinwheel_program import ProgramBuilder


def resident_jtag_scan(half_cycles=4):
    """Reset TAP, scan one resident byte through DR, update, and return to idle.

    Output names are logical TDI0/TCK1/TMS2; input TDO is logical input0.
    Nineteen clocks take 39 half periods including the final low-clock hold.
    The last shifted bit raises TMS, so it is shifted before leaving Shift-DR.
    """
    builder = ProgramBuilder(outputs={'tdi': 0, 'tck': 1, 'tms': 2},
                             inputs={'tdo': 0},
                             idle_enabled=('tdi', 'tck', 'tms'))
    driven = ('tdi', 'tck', 'tms')

    def clock(tms):
        control = ('tms',) if tms else ()
        builder.action(half_cycles, high=control, enabled=driven)
        builder.action(half_cycles, high=(*control, 'tck'), enabled=driven)

    for _ in range(5):
        clock(True)
    # Reset -> Idle -> Select-DR -> Capture-DR -> Shift-DR.
    for tms in (False, True, False, False):
        clock(tms)
    for slot in range(8):
        control = ('tms',) if slot == 7 else ()
        builder.shift('tdi', half_cycles, high=control, enabled=driven)
        builder.keep(half_cycles, preserve=('tdi',), high=(*control, 'tck'),
                     enabled=driven, capture=('tdo', slot))
    # Exit1-DR -> Update-DR -> Idle, then hold the final low clock.
    clock(True)
    clock(False)
    builder.action(half_cycles, enabled=driven).halt()
    return builder.build()
