"""UART sender and sampling oracle, independent of Lean states and instruction addresses."""


def receive(machine, period=16, pin=0, byte=0x53, stop=1, start=500,
            sender_period=None, false_start=False, initial_low=False):
    sender_period = sender_period or 100 * period
    detected = (start + 99) // 100
    complete = detected + period // 2 + 9 * period

    def wire(t):
        if initial_low and t < 10 or false_start and 5 <= t < 8:
            return 0
        if 100 * t < start:
            return 1
        symbol = (100 * t - start) // sender_period
        return 0 if symbol == 0 else (byte >> (symbol - 1)) & 1 if symbol <= 8 else stop if symbol == 9 else 1

    # These are premises about the externally generated waveform, not the receiver's state.
    assert wire(detected + period // 2) == 0
    assert all(wire(detected + period // 2 + (k + 1) * period) == (byte >> k) & 1 for k in range(8))
    assert wire(complete) == stop
    machine.edge(start=1, incoming=1 << pin)
    for t in range(1, complete + 1):
        incoming = wire(t) << pin | int(t % 3 == 0) << (1 - pin)
        machine.edge(incoming=incoming, write=1, bank=t % 3, address=t % 2,
                     data=(1 << 64) - 1, start=int(t % 17 == 0))
        assert machine.s[4:6] == [0, 0], ('RX output drive', t)
        assert (1 <= machine.s[0] <= 4) == (t < complete), ('RX completion', t, complete, machine.s)
        captured = sum(((byte >> k) & 1) << k for k in range(8)
                       if t >= detected + period // 2 + (k + 1) * period)
        assert machine.s[6] & 255 == captured, ('RX data sampling', t, machine.s[6], captured)
        assert machine.s[6] >> 10 == 0, ('RX reserved samples', t)
    assert machine.s[0] == 5 and (machine.s[6] >> 9) & 1 == stop
    retained = machine.s.copy()
    for incoming in range(4):
        machine.edge(incoming=incoming)
        assert machine.s == retained, 'RX result retention'
    return complete


def exercise(machine, images):
    """Reuse the same loaded instance for good frames, errors, rearm and replacement."""
    count = 0
    machine.load('uart-rx', *images['uart-rx'])
    for byte in [0, 0x53, 0xa6, 255]:
        receive(machine, byte=byte)
        count += 1
    receive(machine, byte=0xa6, stop=0)
    receive(machine, byte=0x53, start=4000, false_start=True)
    receive(machine, byte=0xa6, start=4000, initial_low=True)
    count += 3
    machine.load('uart-rx-split', *images['uart-rx-split'])
    receive(machine, period=257, pin=1, byte=0x53)
    receive(machine, period=257, pin=1, byte=0xa6, stop=0)
    return count + 2
