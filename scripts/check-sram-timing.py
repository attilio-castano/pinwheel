#!/usr/bin/env python3
"""Pre-layout STA of the complete comparison chips, including SRAM arcs.

Uses the already installed pinned image, with no network and read-only mounts.
It is a cell-delay screen under explicit I/O assumptions, not physical closure.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import time

from validation_run import Commands, fresh_directory, sha

ROOT = Path(__file__).resolve().parents[1]


def run_sta(run, folder, image_id, container, containers, label):
    """Run one capped analysis and independently verify container termination."""
    containers[container] = 'unconfirmed'
    try:
        return run(['docker', 'run', '--rm', '--pull', 'never', '--name', container,
            '--network', 'none', '--read-only', '--cpus', '2', '--memory', '2g',
            '--tmpfs', '/tmp:rw,size=64m', '--mount',
            f'type=bind,source={folder},target=/work,readonly', '--workdir', '/work',
            image_id, 'sta', '-exit', 'timing.tcl'], label, timeout=120)
    except BaseException:
        cleanup = subprocess.run(['docker', 'stop', '--time', '2', container],
                                 capture_output=True, text=True, timeout=15)
        (folder / 'cleanup.log').write_text(cleanup.stdout + cleanup.stderr)
        raise
    finally:
        result = subprocess.run(['docker', 'inspect', '--type', 'container', container],
                                capture_output=True, text=True, timeout=15)
        if result.returncode:
            if 'No such ' in result.stderr and container in result.stderr:
                containers[container] = 'absent'
            else:
                raise RuntimeError('Cannot confirm timing container termination: ' + result.stderr)
        elif json.loads(result.stdout)[0]['State']['Running']:
            raise RuntimeError('Timing container still running: ' + container)
        else:
            containers[container] = 'stopped'


def fetch_paths(netlist, module, reg):
    from tiled_chip import FF
    bits = module['netnames'][reg]['bits']
    q_bits = {c['connections']['Q'][0] for c in module['cells'].values() if c['type'] == FF}
    indices = {k for k, bit in enumerate(bits) if bit in q_bits}
    # write_verilog renames private cell identifiers. Select actual saved
    # Verilog instances and check their Q connections against JSON state bits.
    pins, found = [], set()
    for cell, body in re.findall(re.escape(FF) + r'\s+(\S+)\s*\((.*?)\);', netlist.read_text(), re.S):
        q = re.search(r'\.Q\(\s*\\' + re.escape(reg) + r'\s+\[(\d+)\]\s*\)', body)
        if q:
            found.add(int(q[1]))
            pins.append(cell.removeprefix('\\') + '/Q')
    if found != indices or len(pins) != 58 or any(any(x in p for x in '{}\\[]\n\r') for p in pins):
        raise ValueError('Unexpected saved Verilog cached-word drivers')
    text = 'set cached [get_pins [list ' + ' '.join('{' + p + '}' for p in pins) + ']]\n'
    return text + '''if {[llength $cached] != 58} { error "Missing cached-word launch pins" }
puts "PINWHEEL_CACHED_TO_ADDRESS"
report_checks -from $cached -to $addresses -path_delay max -group_path_count 4 -fields {slew cap fanout} -format full_clock_expanded
puts "PINWHEEL_ADDRESS_PATHS"
report_checks -to $addresses -path_delay max -group_path_count 4 -fields {slew cap fanout} -format full_clock_expanded
'''


def timing_script(macro, extra=''):
    text = '''read_liberty cells.lib
'''+('read_liberty macro.lib\n' if macro else '')+'''read_verilog design.v
link_design tt_um_pinwheel
create_clock -name clk -period 20.0 [get_ports clk]
set pins [get_ports {ui_in[*] uio_in[*] ena rst_n}]
set_input_delay -clock clk -max 4.0 $pins
set_input_delay -clock clk -min 0.2 $pins
set_output_delay -clock clk -max 4.0 [all_outputs]
set_output_delay -clock clk -min 0.2 [all_outputs]
set_driving_cell -lib_cell sg13cmos5l_buf_2 -pin X $pins
set_load 0.010 [all_outputs]
set_clock_uncertainty 0.2 [get_clocks clk]
set_clock_transition 0.15 [get_clocks clk]
puts "PINWHEEL_SETUP_CHECK"
check_setup -verbose
puts "PINWHEEL_MAX_SLACK"
report_worst_slack -max
puts "PINWHEEL_MIN_SLACK"
report_worst_slack -min
puts "PINWHEEL_SETUP_PATHS"
report_checks -path_delay max -group_path_count 5 -fields {slew cap fanout} -format full_clock_expanded
puts "PINWHEEL_HOLD_PATHS"
report_checks -path_delay min -group_path_count 3 -fields {slew cap fanout} -format full_clock_expanded
puts "PINWHEEL_ELECTRICAL"
report_check_types -max_slew -max_capacitance -max_fanout -min_pulse_width -min_period -violators
'''
    if macro:
        text += '''set responses [get_pins {memory.storage*/A_DOUT*}]
set addresses [get_pins {memory.storage*/A_ADDR*}]
if {[llength $responses] != 128 || [llength $addresses] == 0} { error "Missing SRAM timing ports" }
puts "PINWHEEL_SRAM_TO_SRAM"
report_checks -from $responses -to $addresses -path_delay max -group_path_count 3 -fields {slew cap fanout} -format full_clock_expanded
'''
    return 'if {[catch {\n'+text+extra+'''} message]} {
  puts stderr $message
  exit 1
}
puts "PINWHEEL_STA_COMPLETE"
exit 0
'''


def parse_timing(log, require_fetch_paths=False):
    """Reject incomplete analysis while retaining genuine timing violations."""
    if log.count('PINWHEEL_STA_COMPLETE') != 1 or re.search(r'(^|\n)Error:', log):
        raise ValueError('Incomplete STA run')
    markers = ['PINWHEEL_SETUP_CHECK', 'PINWHEEL_MAX_SLACK', 'PINWHEEL_MIN_SLACK',
               'PINWHEEL_ELECTRICAL']
    fetch_markers = ['PINWHEEL_SRAM_TO_SRAM', 'PINWHEEL_CACHED_TO_ADDRESS', 'PINWHEEL_ADDRESS_PATHS']
    if require_fetch_paths:
        markers += fetch_markers
    if any(log.count(marker) != 1 for marker in markers):
        raise ValueError('Missing or repeated timing section')
    setup = log.split('PINWHEEL_SETUP_CHECK', 1)[1].split('PINWHEEL_MAX_SLACK', 1)[0]
    if 'Warning:' in setup:
        raise ValueError('Incomplete constraints: ' + setup)
    result = {}
    for key, marker in [('setup_slack_ns', 'PINWHEEL_MAX_SLACK'), ('hold_slack_ns', 'PINWHEEL_MIN_SLACK')]:
        section = log.split(marker, 1)[1].split('PINWHEEL_', 1)[0]
        match = re.search(r'worst slack (?:max|min)\s+(-?\d+(?:\.\d+)?)', section)
        if not match:
            raise ValueError('Missing numeric timing slack')
        result[key] = float(match[1])
    section = log.split('PINWHEEL_ELECTRICAL', 1)[1].split('PINWHEEL_', 1)[0]
    types = ['max fanout', 'max slew', 'max capacitance', 'min pulse width', 'min period']
    counts = dict.fromkeys(types, 0)
    category = None
    for line in section.splitlines():
        line = line.strip()
        if line in types:
            category = line
        elif not line or set(line) == {'-'} or line.startswith(('Pin ', 'Clock ')):
            continue
        elif '(VIOLATED)' in line and category is not None:
            counts[category] += 1
        else:
            raise ValueError('Unrecognized electrical violation section: ' + line)
    result['electrical_violations'] = counts
    for marker in fetch_markers:
        if marker in log:
            section = log.split(marker, 1)[1].split('PINWHEEL_', 1)[0]
            slacks = re.findall(r'(-?\d+(?:\.\d+)?)\s+slack \((?:MET|VIOLATED)\)', section)
            if 'Startpoint:' not in section or not slacks:
                raise ValueError('Missing requested timing paths: ' + marker)
            result[marker.removeprefix('PINWHEEL_').lower() + '_slack_ns'] = min(map(float, slacks))
    return result


def retained_timing(args):
    """Analyze hash-bound, independently checked tiled-chip artifacts as saved.

    A later proof-only source edit does not invalidate an immutable netlist's
    timing. This mode verifies its selected receipt and every consumed artifact,
    and explicitly records that it is timing the retained mapping.
    """
    from tiled_chip import chip_metrics
    out = fresh_directory(ROOT / 'build/storage/sram-timing', args.tag)
    started = time.monotonic()
    run = Commands(ROOT, out, default_timeout=120)
    report = {'schema': 1, 'status': 'running', 'commands': run.records, 'metrics': {},
              'containers': {}, 'inputs_sha256': {}, 'per_command_timeout_seconds': 120}
    frozen = report['inputs_sha256']
    def freeze(path):
        path = Path(path).resolve()
        frozen[str(path.relative_to(ROOT)) if path.is_relative_to(ROOT) else str(path)] = sha(path)
        return path
    try:
        selected_path = freeze(args.retained)
        selected = json.loads(selected_path.read_text())
        path = freeze(ROOT / selected['report'])
        if sha(path) != selected['report_sha256']:
            raise ValueError('Changed selected comparison')
        current = json.loads(path.read_text())
        if current['status'] != 'passed' or current.get('organization') != 'combined':
            raise ValueError('Require a validated combined chip comparison')
        previous_path = freeze(ROOT / current['previous_comparison']['report'])
        if sha(previous_path) != current['previous_comparison']['report_sha256']:
            raise ValueError('Changed previous chip comparison')
        previous = json.loads(previous_path.read_text())
        if previous['status'] != 'passed' or previous['libraries_sha256'] != current['libraries_sha256']:
            raise ValueError('Unmatched previous comparison')
        freeze(Path(__file__))
        for rel in ('scripts/tiled_chip.py', 'scripts/validation_run.py', 'scripts/process_group.py',
                    'tools/physical-toolchain.json', 'tools/storage-macros.json'):
            freeze(ROOT / rel)
        lock = json.loads((ROOT / 'tools/physical-toolchain.json').read_text())
        info = json.loads(run(['docker', 'image', 'inspect', lock['container_tag']], 'image-inspect'))[0]
        runtime = {k: v for k, v in info['Config'].items() if v is not None}
        runtime_hash = hashlib.sha256(json.dumps(runtime, sort_keys=True).encode()).hexdigest()
        if (info['Architecture'] != 'arm64' or info['Os'] != 'linux' or
                info['RootFS']['Layers'] != lock['container_rootfs_diff_ids'] or
                runtime_hash != lock['container_runtime_config_sha256']):
            raise ValueError('Unpinned timing tool image')
        report.update(tool_image=info['Id'], runtime_config_sha256=runtime_hash)
        for name, receipt, source, variant in (
                ('baseline', current, path.parent, 'baseline'),
                ('separate', previous, previous_path.parent, 'tiled'),
                ('combined', current, path.parent, 'tiled')):
            report['metrics'][name] = {}
            for corner, suffix in [('typical', 'typ_1p20V_25C'), ('slow', 'slow_1p08V_125C')]:
                prefix = f'{variant}-{corner}'
                netlist, mapped = freeze(source / (prefix + '.v')), freeze(source / (prefix + '.json'))
                for artifact in (netlist, mapped):
                    if sha(artifact) != receipt['artifacts_sha256'][artifact.name]:
                        raise ValueError('Changed retained mapped artifact')
                data = json.loads(mapped.read_text())
                if chip_metrics(data) != receipt['variants'][corner][variant]:
                    raise ValueError('Retained mapped metrics do not reproduce')
                module = data['modules']['tt_um_pinwheel']
                reg = 'controller.' + ('' if variant == 'baseline' else 'engine.') + 'r_cached_word'
                extra = fetch_paths(netlist, module, reg)
                folder = out / f'{name}-{corner}'
                folder.mkdir()
                shutil.copyfile(netlist, folder / 'design.v')
                lib = freeze(ROOT / f'build/tools/ihp-cmos5l/sg13cmos5l_stdcell_{suffix}.lib')
                macro = freeze(ROOT / f'build/storage/macros/RM_IHPSG13_1P_64x64_c2_bm_bist_{suffix}.lib')
                if sha(lib) != receipt['libraries_sha256'][corner] or sha(macro) != receipt['macro_views_sha256']['lib/' + macro.name]:
                    raise ValueError('Changed timing library')
                shutil.copyfile(lib, folder / 'cells.lib')
                shutil.copyfile(macro, folder / 'macro.lib')
                (folder / 'timing.tcl').write_text(timing_script(True, extra))
                container = f'pinwheel-retained-sta-{args.tag}-{name}-{corner}'
                log = run_sta(run, folder, info['Id'], container, report['containers'], f'{name}-{corner}')
                report['metrics'][name][corner] = parse_timing(log, require_fetch_paths=True)
                print(name, corner, report['metrics'][name][corner], flush=True)
        if any(sha(ROOT / p) != h for p, h in frozen.items()):
            raise ValueError('Timing inputs changed during analysis')
        report.update(status='passed', boundary='Retained complete-chip cell and SRAM Liberty timing; ideal clock and actual pin loads, no wire parasitics or placement. Includes setup, hold and electrical violations without repairs or false paths. Not extracted timing or physical fit.',
            assumptions=dict(period_ns=20, input_output_delay_max_ns=4, input_output_delay_min_ns=0.2,
                             uncertainty_ns=0.2, clock_transition_ns=0.15, output_load_pf=0.010))
    except BaseException as error:
        report.update(status='failed', error=f'{type(error).__name__}: {error}')
        raise
    finally:
        report['elapsed_seconds'] = round(time.monotonic() - started, 3)
        report['artifacts_sha256'] = {str(p.relative_to(out)): sha(p) for p in sorted(out.rglob('*'))
                                    if p.is_file() and p.name != 'report.json'}
        (out / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
        print(out / 'report.json', flush=True)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    mode = p.add_mutually_exclusive_group(required=True)
    mode.add_argument('--comparison', type=Path, help='Completed check-sram-chip.py report')
    mode.add_argument('--retained', type=Path, help='Selected combined-chip receipt; compare retained baseline/separate/combined mappings')
    p.add_argument('--tag', required=True)
    args = p.parse_args()
    if args.retained:
        return retained_timing(args)
    receipt = json.loads(args.comparison.read_text())
    comparison = args.comparison.resolve().parent
    for path, digest in receipt['source_sha256'].items():
        if sha(ROOT/path) != digest: raise RuntimeError(f'Stale comparison source: {path}')
    out = fresh_directory(ROOT/'build/storage/sram-timing', args.tag)
    started = time.monotonic()
    lock = json.loads((ROOT/'tools/physical-toolchain.json').read_text())
    info = json.loads(subprocess.check_output(['docker', 'image', 'inspect', lock['container_tag']],
                                              text=True, timeout=30))[0]
    runtime = {k:v for k,v in info['Config'].items() if v is not None}
    runtime_hash = hashlib.sha256(json.dumps(runtime, sort_keys=True).encode()).hexdigest()
    if (info['Architecture'] != 'arm64' or info['Os'] != 'linux' or
        info['RootFS']['Layers'] != lock['container_rootfs_diff_ids'] or
        runtime_hash != lock['container_runtime_config_sha256']):
        raise RuntimeError('Unpinned physical tool image')
    (out/'image.json').write_text(json.dumps(info, indent=2)+'\n')
    run = Commands(ROOT, out, default_timeout=120)
    metrics = {}
    for variant, data in receipt['variants'].items():
        metrics[variant] = {}
        for corner, suffix in [('typical', 'typ_1p20V_25C'), ('slow', 'slow_1p08V_125C')]:
            folder = out/(variant+'-'+corner)
            folder.mkdir()
            netlist = comparison/variant/(corner+'.v')
            if sha(netlist) != data['metrics'][corner]['netlist_sha256']: raise RuntimeError('Changed mapped netlist')
            shutil.copyfile(netlist, folder/'design.v')
            name = f'sg13cmos5l_stdcell_{suffix}.lib'
            lib = ROOT/'build/tools/ihp-cmos5l'/name
            expected = receipt['compatibility']['mapping_libraries_identical_to_physical_pdk'][name]
            if sha(lib) != expected: raise RuntimeError('Changed standard-cell timing library')
            shutil.copyfile(lib, folder/'cells.lib')
            macro = variant != 'ff'
            if macro:
                name = 'RM_IHPSG13_1P_'+('512x64' if variant == 'direct' else '64x64')+'_c2_bm_bist_'+suffix+'.lib'
                lib = ROOT/'build/storage/macros'/name
                if sha(lib) != receipt['compatibility']['macro_views']['lib/'+name]['sha256']:
                    raise RuntimeError('Changed SRAM timing library')
                shutil.copyfile(lib, folder/'macro.lib')
            (folder/'timing.tcl').write_text(timing_script(macro))
            # No persistent container, shared PDK mutation, network or writable
            # host mount. OpenSTA reads only this verified input snapshot.
            container = 'pinwheel-sram-sta-'+args.tag+'-'+variant+'-'+corner
            try:
                log = run(['docker', 'run', '--rm', '--name', container, '--network', 'none', '--read-only',
                           '--cpus', '2', '--memory', '2g', '--tmpfs', '/tmp:rw,size=64m',
                           '--mount', f'type=bind,source={folder},target=/work,readonly',
                           '--workdir', '/work', info['Id'], 'sta', '-exit', 'timing.tcl'], variant+'-'+corner)
            except BaseException:
                # Stopping the attached Docker client alone is insufficient
                # evidence that the container stopped after a host timeout.
                cleanup = subprocess.run(['docker', 'stop', '--time', '2', container],
                                         capture_output=True, text=True, timeout=15)
                (out/(variant+'-'+corner+'-cleanup.log')).write_text(cleanup.stdout+cleanup.stderr)
                raise
            if 'PINWHEEL_STA_COMPLETE' not in log or re.search(r'(^|\n)Error:', log):
                raise RuntimeError('Incomplete STA run')
            if macro and 'Startpoint:' not in log.split('PINWHEEL_SRAM_TO_SRAM', 1)[1]:
                raise RuntimeError('Missing SRAM response-to-request timing paths')
            setup = log.split('PINWHEEL_SETUP_CHECK', 1)[1].split('PINWHEEL_MAX_SLACK', 1)[0]
            if 'Warning:' in setup: raise RuntimeError('Incomplete constraints: '+setup)
            def slack(marker):
                return float(re.search(r'worst slack (?:max|min)\s+(-?[\d.]+)', log.split(marker, 1)[1])[1])
            electrical = log.split('PINWHEEL_ELECTRICAL', 1)[1].split('PINWHEEL_SRAM_TO_SRAM', 1)[0]
            types = ['max fanout', 'max slew', 'max capacitance', 'min pulse width', 'min period']
            sections = re.split(r'^(max fanout|max slew|max capacitance|min pulse width|min period)\s*$',
                                electrical, flags=re.M)
            violations = dict.fromkeys(types, 0)
            for name, section in zip(sections[1::2], sections[2::2]):
                violations[name] = section.count('(VIOLATED)')
            metrics[variant][corner] = dict(setup_slack_ns=slack('PINWHEEL_MAX_SLACK'),
                                            hold_slack_ns=slack('PINWHEEL_MIN_SLACK'),
                                            electrical_violations=violations,
                                            inputs_sha256={p.name:sha(p) for p in folder.iterdir() if p.is_file()})
    report = dict(comparison_sha256=sha(args.comparison), metrics=metrics,
                  script_sha256=sha(Path(__file__)), tool_image=info['Id'], runtime_config_sha256=runtime_hash,
                  commands=run.records, elapsed_seconds=round(time.monotonic()-started, 3),
                  assumptions=dict(period_ns=20, input_output_delay_max_ns=4, input_output_delay_min_ns=0.2,
                                   uncertainty_ns=0.2, clock_transition_ns=0.15, output_load_pf=0.010),
                  boundary='OpenSTA includes standard-cell and synchronous SRAM Liberty arcs. '
                           'Ideal clocks, no wire parasitics or placement. I/O delays are comparison '
                           'assumptions, not analog synchronizer or board guarantees. Electrical '
                           'violations are reported, not repaired. No extracted timing or physical fit.')
    (out/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    print(out/'report.json')


if __name__ == '__main__':
    main()
