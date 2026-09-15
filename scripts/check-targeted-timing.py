#!/usr/bin/env python3
"""Query each launch family in a retained extracted design, without timing exceptions."""
import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / 'build/physical/core'
CORNER = 'nom_slow_1p08V_125C'


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--run', required=True)
    parser.add_argument('--tag', required=True)
    args = parser.parse_args()
    for value in [args.run, args.tag]:
        if not value.replace('-', '').replace('_', '').isalnum():
            parser.error('Use alphanumeric names, hyphens and underscores')
    stages = list((BASE / 'runs' / args.run).glob('*-openroad-stapostpnr'))
    if len(stages) != 1:
        raise RuntimeError('Expected exactly one retained final STA stage')
    stage = stages[0]
    state_path = stage / 'state_out.json'
    state = json.loads(state_path.read_text())
    envs = list((stage / CORNER).glob('_env*.tcl'))
    if len(envs) != 1:
        raise RuntimeError('Expected one retained corner environment')
    env = envs[0]
    out = BASE / 'targeted-sta' / args.tag
    if out.exists():
        raise RuntimeError('Use a fresh tag to preserve evidence')
    invocation = json.loads((ROOT / f'build/physical/{args.run}-invocation.json').read_text())
    image = invocation['image_id']
    image_info = json.loads(subprocess.check_output(['docker', 'image', 'inspect', image], text=True))[0]
    if image_info['Id'] != image:
        raise RuntimeError('Retained container identity mismatch')
    def host(path):
        if path.startswith('/work/core/'):
            return BASE / path.removeprefix('/work/core/')
        if path.startswith('/work/pdk/'):
            return ROOT / 'build/physical/pdk' / path.removeprefix('/work/pdk/')
        raise RuntimeError(f'Unrecognized retained input: {path}')
    oldlog = (stage / CORNER / 'sta.log').read_text()
    libs = re.findall(r"Reading cell library .*? at '([^']+)'", oldlog)
    sdc = re.search(r"Reading design constraints file at '([^']+)'", oldlog)[1]
    spef = state['spef']['nom_*']
    if len(libs) != 2:
        raise RuntimeError('Expected the two retained process libraries')
    source_paths = [state_path, env, stage / CORNER / 'max.rpt', host(state['nl']),
                    host(spef), host(sdc), *map(host, libs), Path(__file__).resolve()]
    hashes = {str(p.relative_to(ROOT)): sha(p) for p in source_paths}
    out.mkdir(parents=True)
    script = '\n'.join([
        f'source /work/core/{env.relative_to(BASE)}',
        'set_cmd_units -time ns -capacitance pF -current mA -voltage V -resistance kOhm -distance um',
        'set sta_report_default_digits 6', f'define_corners {CORNER}',
        *[f'read_liberty -corner {CORNER} {lib}' for lib in libs],
        f'read_verilog {state["nl"]}', 'link_design pinwheel_atomic_small_dense_cached',
        f'read_sdc {sdc}', f'read_spef -corner {CORNER} {spef}',
        'foreach {name ports} {protocol {incoming[*]} loader_data {data[*]} loader_command {command[*]} reset {init reset}} {',
        '  set starts [get_ports $ports]',
        '  if {[llength $starts] == 0} {error "Empty launch family: $name"}',
        f'  report_checks -from $starts -sort_by_slack -path_delay max -fields {{slew cap input net fanout}} -format full_clock_expanded -group_path_count 1000 -corner {CORNER} > /out/$name.rpt',
        '}',
        f'report_checks -from [all_registers -clock_pins] -sort_by_slack -path_delay max -fields {{slew cap input net fanout}} -format full_clock_expanded -group_path_count 1000 -corner {CORNER} > /out/registers.rpt',
        f'report_checks -sort_by_slack -path_delay max -fields {{slew cap input net fanout}} -format full_clock_expanded -group_path_count 1000 -corner {CORNER} > /out/all.rpt',
    ])
    (out / 'targeted.tcl').write_text('if {[catch {\n' + script + '\n} message]} {puts stderr $message; exit 1}\nexit 0\n')
    command = ['docker', 'run', '--rm', '--network', 'none', '--cpus', '4', '--memory', '6g',
               '--mount', f'type=bind,source={BASE},target=/work/core,readonly',
               '--mount', f'type=bind,source={ROOT / "build/physical/pdk"},target=/work/pdk,readonly',
               '--mount', f'type=bind,source={out},target=/out', '--workdir', '/out', image,
               'sta', '-no_splash', '-exit', '/out/targeted.tcl']
    with (out / 'sta.log').open('w') as log:
        subprocess.run(command, stdout=log, stderr=subprocess.STDOUT, check=True)
    results = {}
    for path in sorted(out.glob('*.rpt')):
        blocks = re.split(r'(?=^Startpoint:)', path.read_text(), flags=re.M)[1:]
        paths = [dict(start=b.splitlines()[0].removeprefix('Startpoint: ').split(' (')[0],
                      endpoint=re.search(r'^Endpoint: (\S+)', b, re.M)[1],
                      slack_ns=float(re.search(r'([\d.-]+)\s+slack \(', b)[1])) for b in blocks]
        if not paths:
            raise RuntimeError(f'Empty path family: {path}')
        worst = min(paths, key=lambda p: p['slack_ns'])
        results[path.stem] = dict(worst=worst, reported_paths=len(paths),
                                  reported_negative_paths=sum(p['slack_ns'] < 0 for p in paths))
    expected = state['metrics'][f'timing__setup__ws__corner:{CORNER}']
    if abs(results['all']['worst']['slack_ns'] - expected) > 0.000002:
        raise RuntimeError('Targeted STA did not reproduce retained all-path slack')
    for path in source_paths:
        if sha(path) != hashes[str(path.relative_to(ROOT))]:
            raise RuntimeError('Retained timing input changed during analysis')
    receipt = dict(run=args.run, tag=args.tag, corner=CORNER, results=results,
                   baseline_reproduced=True, command=command, source_sha256=hashes,
                   artifact_sha256={p.name: sha(p) for p in out.iterdir() if p.is_file()},
                   boundary='Extracted setup timing under unchanged SDC. Each family is independently queried; '
                            'reported path counts are capped at 1000 and are not total violation counts. '
                            'No false paths, case analysis, or timing exceptions added.')
    (out / 'report.json').write_text(json.dumps(receipt, indent=2)+'\n')
    print(json.dumps(results, indent=2))


if __name__ == '__main__':
    main()
