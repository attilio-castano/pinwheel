"""Compact reactive buffered I2C register-read reference program.

One program accepts address-W/register/address-R as its three TX bytes and
receives one through eight reply bytes. Counted byte/bit bodies remain stored
syntax. Virtual addresses select a position inside them without building an
expanded instruction bank. This program cannot be uploaded to the current chip.
"""
from buffered_engine import (BufferedBlock, BufferedEngine, BufferedInstruction,
                             BufferedProgram, BufferedRepeat, BufferedSequence,
                             BufferedWireSimulation)


def _integer(value, low, high, name):
    if type(value) is not int or not low <= value <= high:
        raise ValueError(f'{name} must be an integer in {low}..{high}')


def register_read_tx(address, register):
    """Prepare the three control bytes; the program stays data independent."""
    _integer(address, 0, 127, 'I2C address')
    _integer(register, 0, 255, 'I2C register')
    return bytes((address << 1, register, (address << 1) | 1))


def buffered_i2c_read(byte_count=4, phase_cycles=4, wait_cycles=32):
    """ACK/NACK, clock stretching, repeated START, and qualified STOP.

    Control ACK decisions use scratch slot zero, independent of appended RX.
    A NACK performs the fault STOP sequence before retaining a fault result.
    Wait timeout or lost-clock guard immediately releases outputs; neither is
    evidence that a STOP occurred or that the physical bus has recovered.
    """
    _integer(byte_count, 1, 8, 'I2C receive byte count')
    _integer(phase_cycles, 3, 256, 'I2C phase')
    _integer(wait_cycles, 4, 256, 'I2C wait budget')
    H, W = phase_cycles, wait_cycles
    I = BufferedInstruction
    B = lambda *items: BufferedBlock(tuple(items))
    S = lambda *parts: BufferedSequence(tuple(parts))

    def wait(enabled, *, preserve=0):
        return I('wait', enabled=enabled, preserve_enabled=preserve,
                 wait_input=0, wait_level=True, budget=W)

    def high(enabled, *, preserve=0, append=None, capture=None):
        return I('checked', H, enabled=enabled, preserve_enabled=preserve,
                 check_mask=1, check_value=1, append_input=append,
                 terminal_capture=capture)

    def stop(terminal):
        return B(I('drive', H, enabled=3), wait(2), high(2),
                 I('qualify', H, enabled=0, check_mask=3, check_value=3, budget=W),
                 I(terminal))

    # The common transmit byte's branch target is filled after layout. A None
    # false successor means this virtual position's next instruction, including
    # the next iteration of the enclosing counted byte body.
    def tx_byte(fault_stop):
        bit = B(I('shift', H, enabled=1, shift_pin=1,
                  shift_enabled=True, shift_invert=True),
                wait(0, preserve=2), high(0, preserve=2),
                I('checked', H, enabled=1, preserve_enabled=2))
        ack = B(I('drive', H, enabled=1), wait(0), high(0, capture=(1, 0)),
                I('checked', H, enabled=1, finish=(0, fault_stop, None)))
        return S(BufferedRepeat(8, bit), ack)

    read_bit = B(I('drive', H, enabled=1), wait(0), high(0, append=1),
                 I('checked', H, enabled=1))

    def rx_byte(nack):
        # SDA low for ACK, released for final NACK. Target owns all eight data
        # clocks, controller owns exactly the ninth clock for each byte.
        low, release = (1, 0) if nack else (3, 2)
        ack = B(I('drive', H, enabled=low), wait(release), high(release),
                I('checked', H, enabled=low))
        return S(BufferedRepeat(8, read_bit), ack)

    prefix = B(I('qualify', H, enabled=0, check_mask=3, check_value=3, budget=W),
               high(2), I('drive', H, enabled=3))
    repeated_start = B(I('drive', H, enabled=1), wait(0),
                       I('checked', H, enabled=0, check_mask=3, check_value=3),
                       high(2), I('drive', H, enabled=3))

    def layout(fault_stop):
        tx = tx_byte(fault_stop)
        reads = ((BufferedRepeat(byte_count - 1, rx_byte(False)),)
                 if byte_count > 1 else ())
        return S(prefix, BufferedRepeat(2, tx), repeated_start, tx,
                 *reads, rx_byte(True), stop('halt'), stop('fault'))

    provisional = layout(0)
    code = layout(provisional.span - 5)
    return BufferedProgram((), idle_enabled=0, wire_order='msb-per-byte',
                           protocol='i2c-register-read', schedule=code,
                           declared_tx_bits=24, declared_rx_bits=8 * byte_count,
                           max_rx_bits=8 * byte_count)


def run_witness(address=0x53, register=0xa6, reply=b'\x96\xa5\x55\x3c', *,
                ack_bits=(0, 0, 0), phase_cycles=4, wait_cycles=32,
                stretch_cycles=0, initially_stuck=False, never_after_bits=None,
                stop_sda_stuck=False):
    """Run one independently checked witness and return a serializable report."""
    from buffered_i2c_peer import BufferedI2CReadPeer
    from pinwheel_buffers import TransferSlot
    program = buffered_i2c_read(len(reply), phase_cycles, wait_cycles)
    payload = register_read_tx(address, register)
    peer = BufferedI2CReadPeer(address, register, reply, ack_bits,
                              phase_cycles=phase_cycles, stretch_cycles=stretch_cycles,
                              initially_stuck=initially_stuck,
                              never_after_bits=never_after_bits,
                              stop_sda_stuck=stop_sda_stuck)
    slot = TransferSlot(tx_capacity_bits=32, rx_capacity_bits=8 * len(reply))
    identity = slot.begin(program.key, program.encode_tx(payload), program.rx_bits)
    wire = BufferedWireSimulation(BufferedEngine(slot, identity, program), peer)
    completion = wire.run(200_000)
    # This fixture's release callback and two pre-edge sampler observations
    # consume two budget edges beyond its declared positive stretch interval.
    timeout = (initially_stuck or never_after_bits is not None or stop_sda_stuck or
               stretch_cycles > wait_cycles - 2)
    expected_outcome = 'timeout' if timeout else 'fault' if any(ack_bits) else 'complete'
    if completion.outcome != expected_outcome:
        raise AssertionError('I2C retained outcome differs from independent scenario')
    report = peer.check(completion.rx_bits, timeout=timeout)
    if completion.outcome == 'complete' and program.decode_rx(completion.rx_bits) != reply:
        raise AssertionError('I2C decoded reply differs from independent target bytes')
    frozen = slot.peek(identity)
    wire.step()
    if slot.peek(identity) != frozen:
        raise AssertionError('I2C terminal result changed on a later model edge')
    return dict(report, outcome=completion.outcome, tx_consumed_bits=completion.tx_consumed_bits,
                rx_valid_bits=len(completion.rx_bits), execution_edges=wire.cycle,
                storage=program.storage(), program_key=program.key,
                raw_rx_bits=list(completion.rx_bits), immutable_completion=True,
                hardware_upload=False)


def witnesses():
    """Diverse four-byte data, all NACK positions, and retained fault prefixes."""
    cases = []
    for lane in range(4):
        for value in range(256):
            reply = bytearray(b'\x96\xa5\x55\x3c')
            reply[lane] = value
            cases.append(run_witness(reply=bytes(reply)))
    for stage in range(3):
        ack = tuple(int(index == stage) for index in range(3))
        cases.append(run_witness(ack_bits=ack))
    for H, stretch in ((3, 0), (4, 1), (4, 15), (7, 28), (4, 30), (4, 31)):
        cases.append(run_witness(phase_cycles=H, wait_cycles=32, stretch_cycles=stretch))
    for scenario in (dict(initially_stuck=True), dict(never_after_bits=37),
                     dict(stop_sda_stuck=True)):
        cases.append(run_witness(**scenario))
    return cases
