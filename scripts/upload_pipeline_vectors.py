"""Independent atomic-oracle cases for deferred upload writes and read priority."""
import json
from sram_core_vectors import Small, generate as baseline_vectors
from chip_oracle import pack


def generate(out):
    baseline = baseline_vectors(out)
    m = Small()
    m.edge(init=1)
    # A one-cycle instruction consumes its prefetched successor immediately.
    # A multi-cycle pulse would let the defective read-priority mutant recover.
    pulse = pack(dict(kind=0, duration=0, levels=5, enabled=7))
    # Seed the other bank with a distinguishable word. Otherwise a missed read
    # can accidentally hold the expected halt value from a previous upload.
    poison = pack(dict(kind=0, duration=0, levels=2, enabled=7))
    m.load('pipeline-poison-inactive-bank', [poison, 4], 1)
    m.load('pipeline-active-program', [pulse, 4], 1)
    m.edge(command=1)
    starts = 0
    # Every new dictionary entry is followed immediately by start. The pending
    # write must wait while the active program runs, then drain alongside the
    # next accepted push. The reference has no queue or SRAM implementation.
    for k in range(32):
        m.edge(command=2, data=4)
        assert m.gates[0] and m.cursor == k+1
        m.edge(command=5)
        assert m.gates[2]
        starts += 1
        count = 0
        while 1 <= m.s[0] <= 4:
            m.edge(command=2, data=4, incoming=count % 4)
            assert not m.gates[0] and m.gates[3]
            count += 1
            assert count < 20
    for _ in range(32):
        m.edge(command=2, data=4)
    for _ in range(258):
        m.edge(command=2, data=0)
    assert m.cursor == 322
    m.edge(command=3)
    m.edge(command=5)
    assert m.s[0] == 5
    # Repeated address reuse, abort/reset/init immediately after an enqueue,
    # followed by complete replacement. A stale bank/address must never leak.
    for cancellation in ('abort', 'reset', 'init', 'begin'):
        m.cases.append(dict(name='queued-'+cancellation, edge=len(m.rows)))
        m.edge(command=1)
        m.edge(command=2, data=pulse)
        if cancellation == 'reset':
            m.edge(reset=1)
        elif cancellation == 'init':
            m.edge(init=1)
        else:
            m.edge(command=4 if cancellation == 'abort' else 1)
        m.load('replacement-after-'+cancellation, [pulse, 4], 1)
        m.edge(command=5)
        while 1 <= m.s[0] <= 4:
            m.edge(incoming=3)
    with (out/'core-vectors.txt').open('a') as f:
        f.write(''.join(' '.join(map(str, row))+'\n' for row in m.rows))
    coverage=dict(edges=baseline['edges']+len(m.rows), baseline=baseline,
                  pipeline_edges=len(m.rows), immediate_start_after_push=starts,
                  cancellation_cases=4, cases=m.cases,
                  boundary='Expected handshakes and state come from the independent atomic oracle, which has no pipeline implementation.')
    with (out/'pipeline-coverage.json').open('x') as f:
        json.dump(coverage,f,indent=2);f.write('\n')
    return coverage
