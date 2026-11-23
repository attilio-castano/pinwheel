"""Compare hand-kept copies of chip facts against the Lean chip manifest.

The manifest comes from test/StreamingReadyChipManifest.lean. This script only
reads files; it never rewrites a copy. Each finding names the copy, the field,
the manifest value and the value found. Exit status 1 means a copy disagrees.

A finding of kind "note" is a known, deliberate difference (for example the
committed 6x4 physical baseline that preparation patches to 8x4). A "warning"
is a gap the manifest cannot settle yet, such as a demo that assumes a core
clock with no Lean clock contract. Neither fails the check, but both are
printed so the difference stays visible.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))

DEFAULT_MANIFEST = ROOT / 'build/chip-manifest/streaming-ready-d2.json'
LEAN_MODULE = 'Pinwheel.Hardware.StreamingReady.ChipManifest'
LEAN_EMITTER = 'test/StreamingReadyChipManifest.lean'

# How info.yaml names each engine signal. This maps names, not positions:
# every bit position below comes from the manifest.
INFO_LABELS = {
    'csn': lambda bit: 'Host CSn', 'sck': lambda bit: 'Host SCK',
    'mosi': lambda bit: f'Host MOSI {bit}', 'raw_inputs': lambda bit: f'Protocol input {bit}',
    'miso': lambda bit: f'Host MISO {bit}', 'ready': lambda bit: 'Host READY',
    'busy': lambda bit: 'Engine BUSY', 'levels': lambda bit: f'Protocol output {bit}',
}


class Report:
    def __init__(self):
        self.rows = []

    def compare(self, copy, field, expected, actual):
        self.rows.append(dict(copy=copy, field=field, kind='ok' if expected == actual else 'mismatch',
                              expected=expected, actual=actual))

    def note(self, copy, field, expected, actual, reason):
        self.rows.append(dict(copy=copy, field=field, kind='note', expected=expected,
                              actual=actual, reason=reason))

    def warning(self, copy, field, expected, actual, reason):
        self.rows.append(dict(copy=copy, field=field, kind='warning', expected=expected,
                              actual=actual, reason=reason))

    def missing(self, copy, field, reason):
        self.rows.append(dict(copy=copy, field=field, kind='mismatch', expected='present',
                              actual=None, reason=reason))

    @property
    def mismatches(self):
        return [row for row in self.rows if row['kind'] == 'mismatch']


# ---------------------------------------------------------------- manifest views

def port_bits(manifest):
    """Every public bit name, e.g. ui_in[3], clk, with its direction."""
    result = {}
    for port in manifest['top_ports']:
        names = [port['name']] if port['width'] == 1 else [
            f"{port['name']}[{index}]" for index in range(port['width'])]
        for name in names:
            result[name] = port['direction']
    return result


def input_map(manifest):
    """Pad bit -> (signal, bit), e.g. ('ui_in', 0) -> ('csn', 0)."""
    return {(row['pad']['port'], row['pad']['bit']): (row['drives']['port'], row['drives']['bit'])
            for row in manifest['pins']['inputs']}


def output_map(manifest):
    """Pad bit -> (signal, bit), e.g. ('uo_out', 4) -> ('ready', 0)."""
    return {(row['drives']['port'], row['drives']['bit']): (row['signal']['port'], row['signal']['bit'])
            for row in manifest['pins']['outputs']}


def expected_info_pinout(manifest):
    inputs, outputs = input_map(manifest), output_map(manifest)
    result = {}
    for bit in range(8):
        signal = inputs.get(('ui_in', bit))
        result[f'ui[{bit}]'] = INFO_LABELS[signal[0]](signal[1]) if signal else ''
        signal = outputs.get(('uo_out', bit))
        result[f'uo[{bit}]'] = INFO_LABELS[signal[0]](signal[1]) if signal else ''
        signal = outputs.get(('uio_out', bit)) or inputs.get(('uio_in', bit))
        result[f'uio[{bit}]'] = INFO_LABELS[signal[0]](signal[1]) if signal else ''
    return result


# ---------------------------------------------------------------- Verilog bits

def verilog_bits(expression, widths):
    """Expand a simple Verilog bit expression to a list of (name, bit), LSB first.

    Accepts `name`, `name[i]`, `name[h:l]`, `N'b...` literals and `{...}`
    concatenations, which is all the Tiny Tapeout wrapper uses. Literal bits
    appear as ('0', None) or ('1', None). Anything else raises ValueError.
    """
    expression = expression.strip()
    if expression.startswith('{') and expression.endswith('}'):
        parts, depth, start = [], 0, 1
        for index, char in enumerate(expression[1:-1], start=1):
            depth += char == '{'
            depth -= char == '}'
            if char == ',' and depth == 0:
                parts.append(expression[start:index])
                start = index + 1
        parts.append(expression[start:-1])
        bits = []
        for part in reversed(parts):
            bits += verilog_bits(part, widths)
        return bits
    if match := re.fullmatch(r"(\d+)'b([01]+)", expression):
        value = match.group(2).rjust(int(match.group(1)), '0')
        return [(char, None) for char in reversed(value)]
    if match := re.fullmatch(r'([A-Za-z_]\w*)\[(\d+):(\d+)\]', expression):
        name, high, low = match.group(1), int(match.group(2)), int(match.group(3))
        return [(name, bit) for bit in range(low, high + 1)]
    if match := re.fullmatch(r'([A-Za-z_]\w*)\[(\d+)\]', expression):
        return [(match.group(1), int(match.group(2)))]
    if re.fullmatch(r'[A-Za-z_]\w*', expression):
        if expression not in widths:
            raise ValueError(f'Unknown width for {expression}')
        return [(expression, bit) for bit in range(widths[expression])]
    raise ValueError(f'Unsupported Verilog expression: {expression}')


# ---------------------------------------------------------------- checks

def check_info_yaml(report, manifest, text):
    copy = 'info.yaml'
    found = dict(re.findall(r'^\s*(top_module|tiles):\s*"([^"]*)"', text, re.M))
    report.compare(copy, 'top_module', manifest['top'], found.get('top_module'))
    report.compare(copy, 'tiles', manifest['targets']['tiles'], found.get('tiles'))
    pinout = dict(re.findall(r'^\s*((?:ui|uo|uio)\[\d\]):\s*"([^"]*)"', text, re.M))
    for pin, label in expected_info_pinout(manifest).items():
        report.compare(copy, f'pinout {pin}', label, pinout.get(pin))
    if match := re.search(r'^\s*clock_hz:\s*(\d+)', text, re.M):
        target = round(1e9 / manifest['targets']['clock_period_ns'])
        if int(match.group(1)) != target:
            report.note(copy, 'clock_hz', target, int(match.group(1)),
                        'declared 20 ns target; release clock left unset until timing is qualified')


def check_wrapper(report, manifest, text):
    """The release tt.sv text from streaming_ready_wrapper.tt_source.

    Its wiring is also certified by Yosys read-back against the Lean wrapper;
    this tool-free comparison only catches drift earlier."""
    copy = 'tt.sv (streaming_ready_wrapper.tt_source)'
    module = re.search(r'^module\s+(\w+)\(', text, re.M)
    report.compare(copy, 'module', manifest['top'], module and module.group(1))
    engine = manifest['hierarchy']['instances'][0]
    instance = re.search(r'^\s*(\w+)\s+(\w+)\(\s*\n\s*\.clk', text, re.M)
    report.compare(copy, 'engine instance', [engine['module'], engine['name']],
                   instance and [instance.group(1), instance.group(2)])
    widths = {port['name']: port['width'] for port in manifest['top_ports'] + manifest['engine_ports']}
    connections = dict(re.findall(r'\.(\w+)\(((?:[^()]|\{[^}]*\})*)\)', text))
    found_inputs = {}
    for port in manifest['engine_ports']:
        if port['direction'] != 'input' or port['name'] in ('clk', 'initialize'):
            continue
        if port['name'] not in connections:
            report.missing(copy, f'.{port["name"]}', 'engine input not connected')
            continue
        for bit, source in enumerate(verilog_bits(connections[port['name']], widths)):
            found_inputs[source] = (port['name'], bit)
    report.compare(copy, 'input wiring', sorted(input_map(manifest).items()), sorted(found_inputs.items()))
    found_outputs, zeros = {}, {}
    for pad in ('uo_out', 'uio_out', 'uio_oe'):
        assign = re.search(rf'assign\s+{pad}\s*=\s*active\s*\?\s*(\{{.*?\}})\s*:\s*8\'b0;', text)
        if not assign:
            report.missing(copy, f'assign {pad}', 'expected an ena/rst_n-gated assignment')
            continue
        for bit, source in enumerate(verilog_bits(assign.group(1), widths)):
            if source[1] is None:
                if source[0] == '0':
                    zeros.setdefault(pad, []).append(bit)
            else:
                found_outputs[(pad, bit)] = source
    report.compare(copy, 'output wiring', sorted(output_map(manifest).items()), sorted(found_outputs.items()))
    report.compare(copy, 'zero outputs', manifest['pins']['zero_outputs'], zeros)
    report.compare(copy, 'initialize', '!active', connections.get('initialize'))


def check_physical_config(report, manifest, name, config, other_tiles_reason=None):
    """`other_tiles_reason` explains a deliberate footprint other than the target."""
    report.compare(name, 'DESIGN_NAME', manifest['top'], config.get('DESIGN_NAME'))
    report.compare(name, 'CLOCK_PORT', manifest['clock'], config.get('CLOCK_PORT'))
    report.compare(name, 'CLOCK_PERIOD', manifest['targets']['clock_period_ns'], config.get('CLOCK_PERIOD'))
    tiles = manifest['targets']['tiles']
    template = config.get('FP_DEF_TEMPLATE', '')
    if tiles not in template and other_tiles_reason:
        report.note(name, 'FP_DEF_TEMPLATE', tiles, template, other_tiles_reason)
    else:
        report.compare(name, 'FP_DEF_TEMPLATE tiles', True, tiles in template)


def check_allocation(report, manifest, allocation, die_area, public_names):
    copy = 'physical/streaming_8x4/allocation.json'
    report.compare(copy, 'tiles', manifest['targets']['tiles'], allocation.get('tiles'))
    report.compare(copy, 'template tiles', True, manifest['targets']['tiles'] in allocation.get('template_path', ''))
    scale = allocation.get('dbu_per_micron', 1000)
    report.compare('prepared DIE_AREA vs allocation', 'die (dbu)', allocation.get('die_dbu'),
                   [round(value * scale) for value in die_area])
    report.compare('streaming_8x4_geometry.public_names', 'public pins',
                   sorted(port_bits(manifest)), sorted(public_names))
    report.compare(copy, 'public_pin_count', len(port_bits(manifest)), allocation.get('public_pin_count'))


def check_sdc(report, manifest, text):
    copy = 'physical/streaming-tt.sdc'
    ports = {name.split('[')[0]: direction for name, direction in port_bits(manifest).items()}
    clock = re.search(r'create_clock\b.*\[get_ports\s+(\w+)\]', text)
    report.compare(copy, 'clock port', manifest['clock'], clock and clock.group(1))
    for group in re.findall(r'get_ports\s+\{([^}]*)\}', text):
        for name in group.split():
            base = name.split('[')[0]
            report.compare(copy, f'input {name}', 'input', ports.get(base))


def check_release_workflow(report, manifest, text):
    copy = 'physical/streaming_8x4/ttihp27a-custom-gds.yml'
    top = re.search(r'top_module:\s*(\S+)', text)
    report.compare(copy, 'top_module', manifest['top'], top and top.group(1))
    for path in re.findall(r'release/(\S+)\.(?:gds|lef|v)\b', text):
        report.compare(copy, 'release file stem', manifest['top'], path)


def check_state_literals(report, manifest, files):
    """Hard-coded copies of the state-bit total. Only the value is compared;
    the occurrences are listed so step 3 can route them through the manifest."""
    total = manifest['state']['bits']
    pattern = re.compile(r'(?<![\w.])(\d{4})(?![\w.])')
    hits = {}
    for path, text in files:
        count = sum(1 for match in pattern.finditer(text) if match.group(1) == str(total))
        if count:
            hits[path] = count
    report.note('hard-coded state-bit total', f'{sum(hits.values())} literals in {len(hits)} files', total, total,
                'same value as the manifest census; not yet read from it')
    return hits


# Scripts whose clock constants have a Lean clock contract in the manifest.
CONTRACTED_CLOCKS = {'scripts/streaming_ready_can.py': 'can_receive',
                     'scripts/streaming_ready_ethernet.py': 'ethernet_sni_tx',
                     'scripts/streaming_ready_ps2.py': 'ps2_receive'}


def check_program_clocks(report, manifest, files):
    """Compare demo clock constants with the manifest's program clock contracts.

    `files` holds (path, text) for tracked scripts. A module-level CORE_HZ in a
    script without a contract is a warning, with the target excess called out."""
    contracts = {row['program']: row for row in manifest.get('program_clocks', [])}
    limit = manifest['targets']['max_core_hz']
    for path, text in files:
        constants = {name: int(value.replace('_', '')) for name, value in
                     re.findall(r'^(CORE_HZ|BIT_RATE|BIT_CYCLES)\s*=\s*([\d_]+)\s*$', text, re.M)}
        if 'CORE_HZ' not in constants:
            continue
        program = CONTRACTED_CLOCKS.get(path)
        if program in contracts:
            contract = contracts[program]
            report.compare(path, 'CORE_HZ', contract['core_hz'], constants['CORE_HZ'])
            continue
        core = constants['CORE_HZ']
        excess = f'; {core / 1e6:g} MHz exceeds the {limit / 1e6:g} MHz target' if core > limit else ''
        report.warning(path, 'CORE_HZ', None, core, 'no Lean clock contract' + excess)


def check_i2c_profile(report, manifest, i2c_image):
    """The Python builder's default profile must be the Lean standard profile."""
    import inspect
    stretch = manifest.get('i2c_clock_stretch')
    if stretch is None:
        report.missing('manifest', 'i2c_clock_stretch', 'manifest predates the I2C clock contract')
        return
    defaults = {name: parameter.default for name, parameter in inspect.signature(i2c_image).parameters.items()}
    copy = 'scripts/streaming_ready_compile.py i2c_image defaults'
    for name, value in stretch['standard_profile'].items():
        report.compare(copy, name, value, defaults.get(name))
    report.compare(copy, 'stretch tolerance (wait_budget - 3)', stretch['standard_tolerance_core_clocks'],
                   defaults.get('wait_budget', 0) - 3)


# ---------------------------------------------------------------- driver

def emit_manifest(path):
    subprocess.run(['lake', 'build', LEAN_MODULE], cwd=ROOT, check=True, stdout=subprocess.DEVNULL)
    subprocess.run(['lake', 'env', 'lean', '-DwarningAsError=true', '--run', LEAN_EMITTER, str(path)],
                   cwd=ROOT, check=True, stdout=subprocess.DEVNULL)


def run(manifest):
    import streaming_ready_wrapper
    import streaming_8x4_geometry as geometry
    import streaming_8x4_prepare as prepare

    report = Report()
    depth = manifest['depth']
    check_info_yaml(report, manifest, (ROOT / 'info.yaml').read_text())
    check_wrapper(report, manifest, streaming_ready_wrapper.tt_source(depth))

    allocation_path = ROOT / 'physical/streaming_8x4/allocation.json'
    allocation = json.loads(allocation_path.read_text())
    allocation['allocation_sha256'] = geometry.sha(allocation_path)
    # The release 8x4 config was prepared from a retained, hash-pinned parent
    # run (streaming_8x4_prepare.BASELINE_SHA256) that this checker cannot see.
    # The committed 6x4 config is checked as that baseline, and once more as
    # the recipe would transform it.
    config = json.loads((ROOT / 'physical/streaming-tt.json').read_text())
    check_physical_config(report, manifest, 'physical/streaming-tt.json', config,
                          '6x4 baseline; streaming_8x4_prepare.recipe swaps template and die for 8x4')
    prepared, _ = prepare.recipe(config, allocation)
    check_physical_config(report, manifest, 'physical/streaming-tt.json through streaming_8x4_prepare.recipe',
                          prepared)
    candidate = json.loads((ROOT / 'physical/streaming-tt-candidate.json').read_text())
    check_physical_config(report, manifest, 'physical/streaming-tt-candidate.json', candidate,
                          'historical 6x4 flow (streaming_tt_candidate.py), not the 8x4 release')
    check_allocation(report, manifest, allocation, prepared['DIE_AREA'], geometry.public_names())
    check_sdc(report, manifest, (ROOT / 'physical/streaming-tt.sdc').read_text())
    check_release_workflow(report, manifest, (ROOT / 'physical/streaming_8x4/ttihp27a-custom-gds.yml').read_text())

    import streaming_ready_compile
    check_i2c_profile(report, manifest, streaming_ready_compile.i2c_image)

    import streaming_8x4_bringup as bringup
    report.compare('scripts/streaming_8x4_bringup.py', 'TOP', manifest['top'], bringup.TOP)
    report.compare('scripts/streaming_8x4_bringup.py', 'DEPTH', depth, bringup.DEPTH)

    tracked = subprocess.run(['git', 'ls-files', 'scripts/*.py', 'test/*.py'], cwd=ROOT, check=True,
                             capture_output=True, text=True).stdout.split()
    texts = [(path, (ROOT / path).read_text()) for path in tracked]
    hits = check_state_literals(report, manifest, texts)
    check_program_clocks(report, manifest, [(path, text) for path, text in texts if path.startswith('scripts/')])
    limit = manifest['targets']['max_core_hz']
    for contract in manifest.get('program_clocks', []):
        if contract['core_hz'] > limit:
            report.warning('manifest program_clocks', contract['program'], limit, contract['core_hz'],
                           f"Lean contract needs {contract['core_hz'] / 1e6:g} MHz, above the "
                           f"{limit / 1e6:g} MHz target")
        else:
            report.compare('manifest program_clocks', f"{contract['program']} within target", True, True)
    return report, hits


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument('--manifest', type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument('--emit', action='store_true', help='rebuild the manifest from Lean first')
    parser.add_argument('--json', action='store_true', help='print every row as JSON')
    parser.add_argument('--all', action='store_true', help='also print matching rows')
    args = parser.parse_args(argv)
    if args.emit:
        emit_manifest(args.manifest)
    manifest = json.loads(args.manifest.read_text())
    if manifest.get('schema') != 'pinwheel.chip-manifest.v1':
        raise SystemExit('Unsupported chip manifest schema')
    report, hits = run(manifest)
    if args.json:
        print(json.dumps(dict(rows=report.rows, state_literal_files=hits), indent=1, default=str))
    else:
        for row in report.rows:
            if row['kind'] == 'ok' and not args.all:
                continue
            reason = f"  ({row['reason']})" if row.get('reason') else ''
            print(f"{row['kind'].upper():8} {row['copy']} :: {row['field']}: "
                  f"manifest={row['expected']!r} found={row['actual']!r}{reason}")
        counts = {kind: sum(row['kind'] == kind for row in report.rows)
                  for kind in ('ok', 'note', 'warning', 'mismatch')}
        print(f"{manifest['top']}: {counts['ok']} agree, {counts['note']} notes, "
              f"{counts['warning']} warnings, {counts['mismatch']} mismatches")
    return 1 if report.mismatches else 0


if __name__ == '__main__':
    sys.exit(main())
