"""Core-edge stress for SRAM experiments, using the independent atomic oracle."""
import json
import random

from chip_oracle import loader, pack


class Small(loader['Atomic']):
    def __init__(self):
        super().__init__()
        self.read_addresses = set()

    def read(self, pc):
        self.read_addresses.add((self.read_bank, pc))
        return super().read(pc)

    def edge(self, init=0, reset=0, command=0, data=0, incoming=0):
        c = self.cursor
        fits = c < 32 or c < 64 and data == 4 or 64 <= c < 320 and data < 32 or c >= 320
        super().edge(init, reset, 6 if command == 2 and not fits else command, data, incoming)
        self.rows[-1][2] = command


def generate(out):
    m = Small()
    m.edge(init=1)
    branches = 0
    # Both branch responses are needed on every edge, including immediately
    # after start. Varying the captured input chooses each successor.
    words = [pack(dict(kind=2, finish=2, terminal=63, sample=15,
                       yes=(k+1) % 3, no=(k+2) % 3)) for k in range(3)]
    rng = random.Random(731)
    for trial in range(4):
        m.load(f'back-to-back-branches-{trial}', words, 2)
        m.edge(command=5)  # No quiet edge between commit and start.
        for _ in range(250):
            m.edge(incoming=rng.randrange(4))
            assert m.s[0] == 3
            branches += 1
        m.edge(reset=1)

    # Every physical dictionary location and every map address in both banks.
    for offset in (0, 3):
        dictionary = [pack(dict(kind=0, duration=k, levels=(k+offset) % 8, enabled=7)) for k in range(31)]
        program = [dictionary[k % 31] for k in range(255)] + [4]
        m.load(f'all-addresses-bank-{offset}', program, 255)
        m.edge(command=5)
        while 1 <= m.s[0] <= 4:
            m.edge(incoming=rng.randrange(4))
        assert m.s[0] == 5
        assert all((m.active, pc) in m.read_addresses for pc in range(256))
        # Partially overwrite the inactive program, abort it and restart the
        # still-active one. Direct SRAM must retain the saved start word even
        # when scratch and macro Q have changed during upload.
        m.edge(command=1)
        for _ in range(64):
            m.edge(command=2, data=4)
        for _ in range(77):
            m.edge(command=2, data=0)
        m.edge(command=4)
        m.edge(command=5)
        for _ in range(100):
            m.edge(incoming=3)
        m.edge(reset=1)

    m.load('halt-only-immediate-start', [4], 0)
    m.edge(command=5)
    assert m.s[0] == 5
    # An invalid dictionary word/index neither writes nor advances the cursor.
    m.edge(command=1)
    m.edge(command=2, data=1 << 63)
    assert m.cursor == 0 and m.gates[3]
    for _ in range(32): m.edge(command=2, data=4)
    m.edge(command=2, data=0)
    assert m.cursor == 32 and m.gates[3]
    for _ in range(32): m.edge(command=2, data=4)
    m.edge(command=2, data=32)
    assert m.cursor == 64 and m.gates[3]
    m.edge(reset=1)
    m.edge(command=5)
    assert m.s[0] == 5
    m.edge(init=1)
    result = dict(edges=len(m.rows), consecutive_branches=branches, cases=m.cases,
                  commands=dict(m.counters), seed=731,
                  read_addresses_by_bank=[sum(b == bank for b, _ in m.read_addresses) for bank in (0, 1)])
    (out/'core-vectors.txt').write_text(''.join(' '.join(map(str, row))+'\n' for row in m.rows))
    (out/'core-coverage.json').write_text(json.dumps(result, indent=2)+'\n')
    return result
