"""Rebase a delayed Icarus dump and audit its declared 20 ns clock window.

No values are invented or removed. The one-picosecond settled preamble is kept.
This checks the waveform, not OpenSTA's annotation coverage (reported natively).
"""
import json
from pathlib import Path
import sys


def normalize(source, target, window):
    scope = []
    widths, names = {}, {}
    values, unknown_ids = {}, set()
    first = last = None
    clock = None
    transitions = 0
    declarations = 0
    with source.open() as inp, target.open('x') as out:
        for line in inp:
            fields = line.split()
            if fields[:1] == ['$scope']:
                scope.append(fields[2])
            elif fields[:1] == ['$upscope']:
                scope.pop()
            elif fields[:1] == ['$var']:
                _, _, width, ident, name, *_ = fields
                widths[ident] = int(width)
                names.setdefault(ident, []).append('.'.join([*scope, name]))
                declarations += 1
                if scope == ['power_tb', 'dut'] and name == 'clk':
                    clock = ident
            elif line.startswith('#'):
                stamp = int(line[1:])
                if first is None:
                    first = stamp
                if last is not None and stamp < last:
                    raise ValueError('Non-monotonic VCD')
                last = stamp
                line = f'#{stamp-first}\n'
            elif fields and not line.startswith('$'):
                if line[0] in '01xXzZ':
                    value, ident = line[0].lower(), line[1:].strip()
                elif line[0] in 'bB':
                    value, ident = fields[0][1:].lower(), fields[1]
                else:
                    out.write(line)
                    continue
                if ident not in widths:
                    raise ValueError('Undeclared VCD identifier')
                if 'x' in value or 'z' in value:
                    unknown_ids.add(ident)
                if ident == clock and ident in values:
                    old = values[ident]
                    if old in ('0', '1') and value in ('0', '1') and old != value:
                        transitions += 1
                values[ident] = value
            out.write(line)
    count = window['last'] - window['first']
    if first != window['first'] * 20000 or last != window['last'] * 20000:
        raise ValueError(f'Wrong 1 ps waveform timestamps: {first}, {last}')
    if transitions != count * 2 or clock is None:
        raise ValueError(f'Incorrect clock transitions: {transitions}')
    if len(values) != len(widths):
        raise ValueError('Missing initial waveform values')
    return dict(first_raw_ps=first, last_raw_ps=last, duration_ns=(last-first)/1000,
                clock_transitions=transitions, declarations=declarations,
                identifiers=len(widths), identifiers_ever_unknown=len(unknown_ids),
                unknown_names=sorted(n for k in unknown_ids for n in names[k]),
                qualification=False)


if __name__ == '__main__':
    case = Path(sys.argv[1])
    windows = json.loads((case / 'windows.json').read_text())['windows']
    reports = {}
    for name, window in windows.items():
        reports[name] = normalize(case / 'output' / f'{name}-raw.vcd',
                                  case / 'output' / f'{name}.vcd', window)
    (case / 'waveform-audit.json').write_text(json.dumps(reports, indent=2) + '\n')
    print(json.dumps({name: {k: v for k, v in r.items() if k != 'unknown_names'}
                      for name, r in reports.items()}, indent=2))
