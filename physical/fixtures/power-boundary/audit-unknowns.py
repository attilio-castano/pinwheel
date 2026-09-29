"""Check whether unknown VCD bits touch any port of the retained signal circuit."""
import collections
import json
from pathlib import Path
import sys


def audit(vcd, module):
    connected = collections.Counter()
    for cell in module['cells'].values():
        for bits in cell['connections'].values():
            connected.update(bit for bit in bits if isinstance(bit, int))
    for port in module['ports'].values():
        connected.update(bit for bit in port['bits'] if isinstance(bit, int))
    names, widths, unknown = {}, {}, collections.defaultdict(set)
    bindings = collections.defaultdict(list)
    scope = []
    with vcd.open() as stream:
        for line in stream:
            fields = line.split()
            if fields[:1] == ['$scope']:
                scope.append(fields[2].lstrip('\\'))
            elif fields[:1] == ['$upscope']:
                scope.pop()
            elif fields[:1] == ['$var']:
                _, _, width, ident, name, *_ = fields
                name = name.lstrip('\\')
                full_name = '.'.join([*scope, name])
                names.setdefault(ident, []).append(full_name)
                widths[ident] = int(width)
                if scope == ['power_tb', 'dut'] and name in module['netnames']:
                    bindings[ident].append((full_name, module['netnames'][name]['bits']))
                elif len(scope) == 3 and scope[:2] == ['power_tb', 'dut']:
                    cell = module['cells'].get(scope[2])
                    if cell and name in cell['connections']:
                        bindings[ident].append((full_name, cell['connections'][name]))
            elif fields and not line.startswith(('$', '#')):
                if line[0] in '01xXzZ':
                    value, ident = line[0].lower(), line[1:].strip()
                elif line[0] in 'bB':
                    value, ident = fields[0][1:].lower(), fields[1]
                else:
                    continue
                if 'x' in value or 'z' in value:
                    value = value.rjust(widths[ident], value[0] if value[0] in 'xz' else '0')
                    unknown[ident].update(i for i, v in enumerate(reversed(value)) if v in 'xz')
    witnesses, unmapped = [], []
    for ident, indices in unknown.items():
        if not bindings[ident]:
            unmapped.extend(names[ident])
        for name, bits in bindings[ident]:
            for index in sorted(indices):
                bit = bits[index]
                witnesses.append(dict(net=name, index=index, bit=bit, cell_or_port_connections=connected[bit]))
    return dict(unknown_bits=len(witnesses), connected_unknown_bits=sum(w['cell_or_port_connections'] > 0 for w in witnesses),
                unmapped_unknown_declarations=unmapped, witnesses=witnesses)


if __name__ == '__main__':
    case = Path(sys.argv[1])
    circuit = Path(sys.argv[2])
    module = json.loads(circuit.read_text())['modules']['tt_um_pinwheel']
    reports = {name: audit(case / 'output' / f'{name}.vcd', module)
               for name in ['idle', 'replacement', 'execution']}
    (case / 'unknown-bit-audit.json').write_text(json.dumps(reports, indent=2) + '\n')
    print(json.dumps({n: {**{k: v for k, v in r.items() if k not in ['witnesses', 'unmapped_unknown_declarations']},
                         'unmapped_unknown_declarations': len(r['unmapped_unknown_declarations'])}
                      for n, r in reports.items()}, indent=2))
    # Library simulation internals (for example timing notifiers) are not
    # physical cell pins. Retain their names; native annotation is independently
    # required to cover every actual signal pin before interpreting power.
    if any(r['connected_unknown_bits'] for r in reports.values()):
        raise SystemExit('Connected unknown activity: do not admit this trace for comparison')
