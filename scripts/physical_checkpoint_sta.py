"""Fresh corner STA worker, run only inside the pinned physical-tool image."""
import json
from decimal import Decimal
from pathlib import Path
import re


def measurement_quality(checks, context, disconnected):
    """Reconcile missing wire estimates and fanout reports with actual net loads."""
    annotation = re.findall(r'Found (\d+) unannotated drivers\.\n(.*?)Found (\d+) partially unannotated drivers\.', checks, re.S)
    if len(annotation) != 1:
        raise ValueError('Missing or ambiguous wire annotation report')
    count, body, partial = annotation[0]
    names = body.split()
    if len(names) != int(count) or len(set(names)) != len(names):
        raise ValueError('Unannotated driver count differs from listed names')
    index = {}
    for name, net in context['nets'].items():
        for pin in [t['instance'] + '/' + t['pin'] for t in net['terminals']] + net['ports']:
            if pin in index:
                raise ValueError('Physical terminal belongs to multiple nets')
            index[pin] = (name, net)
    unused, consumed = [], []
    for driver in names:
        if driver in disconnected:
            if driver in index:
                raise ValueError('Disconnected output has a physical net')
            unused.append(driver)
            continue
        if driver not in index:
            raise ValueError('Unresolved unannotated driver: ' + driver)
        name, net = index[driver]
        loads = sum(t['direction'] == 'INPUT' for t in net['terminals']) + sum(p != driver for p in net['ports'])
        if loads:
            consumed.append(dict(driver=driver, net=name, loads=loads))
        else:
            unused.append(driver)
    fanout = re.findall(r'\nmax fanout\n(.*?)(?:\n\n\n|\nmax slew\n|\nmax capacitance\n)', checks, re.S)
    violations = []
    if fanout:
        if len(fanout) != 1:
            raise ValueError('Ambiguous fanout report')
        # Pinned OpenSTA can omit the unitless fanout slack column entirely.
        # Every violation line must still resolve; never silently drop a row.
        for line in fanout[0].splitlines():
            if '(VIOLATED)' not in line:
                continue
            row = re.fullmatch(r'\s*(\S+)\s+([\d.]+)\s+([\d.]+)(?:\s+(-?[\d.]+))?\s+\(VIOLATED\)\s*', line)
            if not row:
                raise ValueError('Malformed fanout violation row')
            pin, limit, actual, slack = row.groups()
            if float(actual) <= float(limit) or (slack is not None and
                    abs(float(slack) - (float(limit) - float(actual))) > 1e-6):
                raise ValueError('Inconsistent fanout violation')
            if pin not in index:
                raise ValueError('Unresolved fanout driver')
            name, net = index[pin]
            violations.append(dict(pin=pin, net=name, kind=net['type'], limit=float(limit), fanout=float(actual)))
    return dict(wire_annotation=dict(unannotated=int(count), partially_unannotated=int(partial),
        unused_drivers=unused, consumed_unannotated=consumed, complete_for_consumed_nets=not consumed and int(partial) == 0),
        fanout_violations=violations)


def analysis_tcl(request):
    lines = ['puts "PINWHEEL_ESTIMATION_GLOBAL_ROUTES [grt::have_routes]"',
             'puts "PINWHEEL_PROPAGATED_CLOCK [get_property [get_clocks clk] is_propagated]"']
    if request.get('verify_nominal_layer_rc'):
        lines += ['foreach {corner_name corner} [lln::get_corner_dict] {',
                  '  foreach layer [[ord::get_db_tech] getLayers] {',
                  '    if {[$layer getType] ne "ROUTING"} {continue}',
                  '    lassign [est::dblayer_wire_rc $layer] default_r default_c',
                  '    set actual_r [est::layer_resistance $layer $corner]',
                  '    set actual_c [est::layer_capacitance $layer $corner]',
                  '    if {$default_r <= 0 || $default_c <= 0 || abs($actual_r / $default_r - 1) > 1e-6 || abs($actual_c / $default_c - 1) > 1e-6} {error "Explicit layer RC differs from nominal LEF"}',
                  '    puts "PINWHEEL_NOMINAL_LAYER_RC $corner_name [$layer getName] $actual_r $actual_c"',
                  '  }', '}', 'puts "PINWHEEL_NOMINAL_LAYER_RC_VERIFIED"']
    pins = request.get('pins', [])
    if not isinstance(pins, list) or any(not isinstance(p, str) or
            not re.fullmatch(r'[A-Za-z0-9_./\[\]$-]+', p) for p in pins):
        raise ValueError('Expected literal physical pin names')
    if pins:
        lines += ['puts "%OL_CREATE_REPORT selected-loads.rpt"']
        for pin in pins:
            lines += ['set it [$::block findITerm {' + pin + '}]',
                      'if {$it eq "NULL" || [$it getNet] eq "NULL"} {error "Missing selected physical pin"}',
                      'puts {PINWHEEL_PIN {' + pin + '}}',
                      'report_net [[$it getNet] getName]']
        lines += ['puts "%OL_END_REPORT"']
    roles = request.get('path_roles', {})
    if not isinstance(roles, dict):
        raise ValueError('Expected named timing path roles')
    expected = request.get('path_expected', {n: True for n in roles})
    if not isinstance(expected, dict) or set(expected) != set(roles) or any(type(v) is not bool for v in expected.values()):
        raise ValueError('Incomplete target path reachability contract')
    if roles:
        lines += ['puts "%OL_CREATE_REPORT target-paths.rpt"']
    for name, role in roles.items():
        if (not re.fullmatch(r'[a-z_]+', name) or not isinstance(role, dict) or
                set(role) != {'delay', 'sources', 'sinks', 'sink_kind'} or
                role['delay'] not in ['max', 'min'] or role['sink_kind'] not in ['pin', 'port']):
            raise ValueError('Invalid target timing role')
        for key, kind in [('sources', 'pin'), ('sinks', role['sink_kind'])]:
            names = role[key]
            if (not isinstance(names, list) or not names or len(set(names)) != len(names) or
                    any(not isinstance(p, str) or not re.fullmatch(r'[A-Za-z0-9_./\[\]$-]+', p) for p in names)):
                raise ValueError('Invalid target timing endpoints')
            literals = '[list ' + ' '.join('{' + p + '}' for p in names) + ']'
            lines += [f'set {key} [get_{kind}s -quiet {literals}]', 'set actual_names {}',
                      f'foreach object ${key} {{lappend actual_names [get_full_name $object]}}',
                      f'if {{[lsort $actual_names] ne [lsort {literals}]}} {{error "Unresolved {name} {key}"}}']
        lines += [f'puts "PINWHEEL_PATH {name}"',
                  f'report_checks -from $sources -to $sinks -path_delay {role["delay"]} -group_path_count 3 -digits 6 -fields {{slew cap fanout}} -format full_clock_expanded']
    if roles:
        lines += ['puts "%OL_END_REPORT"']
    return '\n'.join(lines) + '\n'


def main():
    from librelane.flows.classic import Classic
    from librelane.state import State
    from librelane.steps.openroad import STAMidPNR

    out = Path('/probe')
    request = json.loads((out / 'request.json').read_text())
    config_data = json.loads(Path(request['config']).read_text())
    if request.get('nominal_layer_rc'):
        if config_data.get('LAYERS_RC') or config_data.get('VIAS_R'):
            raise ValueError('Cannot replace explicit RC with nominal defaults')
        config_data['LAYERS_RC'] = request['nominal_layer_rc']
    extra = out / 'analysis-mode.tcl'
    extra.write_text(analysis_tcl(request))
    results, path_results = {}, {}
    for corner in config_data['STA_CORNERS']:
        cfg = dict(config_data, DEFAULT_CORNER=corner, STA_CORNERS=[corner],
                   STA_EXTRA_CORNER_TCL_FILE=str(extra), OPENROAD_THREADS=2)
        config = Classic(cfg, pdk_root='/work/pdk', pdk='ihp-sg13cmos5l',
                         design_dir='/work/core').config
        # Carry only the database: an inherited SDF/SPEF or older corner metric
        # must not substitute for the explicitly requested physical checkpoint.
        fresh = State.load({'odb': request['database'], 'metrics': {}})
        after = STAMidPNR(config=config, state_in=fresh).start(step_dir=str(out / corner))
        measured = {k: float(v) if isinstance(v, Decimal) else v for k, v in after.metrics.items()}
        if any('__corner:' in k and not k.endswith('__corner:' + corner) for k in measured):
            raise ValueError('Inherited or wrong-corner timing in fresh measurement')
        for key in ('timing__setup__ws', 'timing__hold__ws'):
            if key + '__corner:' + corner not in measured:
                raise ValueError('Missing fresh corner measurement')
        results[corner] = measured
        if request.get('path_roles'):
            reports = list((out / corner).rglob('target-paths.rpt'))
            if len(reports) != 1:
                raise ValueError('Missing target path timing report')
            sections = re.split(r'PINWHEEL_PATH ([a-z_]+)\n', reports[0].read_text())
            values = {}
            for index in range(1, len(sections), 2):
                slacks = re.findall(r'^\s*(-?\d+(?:\.\d+)?)\s+slack\s', sections[index+1], re.M)
                expected = request.get('path_expected', {}).get(sections[index], True)
                if bool(slacks) != expected:
                    raise ValueError('Measured paths differ from mapped reachability: ' + sections[index])
                values[sections[index]] = min(map(float, slacks)) if slacks else None
            if set(values) != set(request['path_roles']):
                raise ValueError('Incomplete target path measurements')
            path_results[corner] = values
            (out / 'target-path-timing.json').write_text(json.dumps(path_results, indent=2) + '\n')
        (out / 'fresh-timing.json').write_text(json.dumps(results, indent=2) + '\n')


if __name__ == '__main__':
    main()
