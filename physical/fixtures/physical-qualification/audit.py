#!/usr/bin/env python3
"""Reproduce the bounded physical-qualification inventory; never accept a chip.

Reads the retained inputs and public captures. Writes one new JSON assessment.
No network, CAD, supplied-view editing, or acceptance-policy changes.
"""
import argparse
from collections import Counter, defaultdict
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[3]
BASE = ROOT / 'build/validation/physical-qualification-01'
files = {}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def read(path, expected=None):
    path = ROOT / path
    body = path.read_bytes()
    digest = hashlib.sha256(body).hexdigest()
    require(expected is None or digest == expected, f'Changed evidence: {path}')
    key = str(path.relative_to(ROOT)) if path.is_relative_to(ROOT) else str(path)
    record = dict(sha256=digest, bytes=len(body))
    require(key not in files or files[key] == record, f'Changed during audit: {path}')
    files[key] = record
    return body


def load(path, expected=None):
    return json.loads(read(path, expected))


def blob(body):
    return hashlib.sha1(b'blob ' + str(len(body)).encode() + b'\0' + body).hexdigest()


def tree(path):
    data = load(path)
    require(data['truncated'] is False, f'Incomplete source inventory: {path}')
    result = {entry['path']: entry for entry in data['tree']}
    require(len(result) == len(data['tree']), 'Duplicate source paths')
    # The API can echo the requested commit in `sha`. Reconstruct Git tree
    # objects, including every subtree, instead of mistaking that alias for
    # the root tree object named by the commit.
    children = defaultdict(list)
    for entry in data['tree']:
        parent, _, name = entry['path'].rpartition('/')
        children[parent].append(dict(entry, name=name))
    hashes = {}
    for parent, entries in children.items():
        entries.sort(key=lambda e: (e['name'] + ('/' if e['type'] == 'tree' else '')).encode())
        body = b''.join(e['mode'].lstrip('0').encode() + b' ' + e['name'].encode() +
                        b'\0' + bytes.fromhex(e['sha']) for e in entries)
        hashes[parent] = hashlib.sha1(b'tree ' + str(len(body)).encode() + b'\0' + body).hexdigest()
    for entry in data['tree']:
        if entry['type'] == 'tree':
            require(hashes.get(entry['path']) == entry['sha'], f'Incomplete subtree: {entry["path"]}')
    return hashes[''], result


def library(path, source_path, pinned):
    body = read(path)
    require(blob(body) == pinned[source_path]['sha'], f'Library differs from pin: {path}')
    text = body.decode()
    groups = re.findall(r'operating_conditions\s*\(([^)]+)\)\s*\{([^}]+)\}', text)
    require(len(groups) == 1, f'Ambiguous operating conditions: {path}')
    name, group = groups[0]
    values = {}
    for key in ('process', 'voltage', 'temperature'):
        found = re.findall(r'\b' + key + r'\s*:\s*([-+\d.eE]+)\s*;', group)
        require(len(found) == 1, f'Missing or repeated {key}: {path}')
        values[key] = float(found[0])
    for key in ('voltage', 'temperature'):
        nominal = re.findall(r'\bnom_' + key + r'\s*:\s*([-+\d.eE]+)\s*;', text)
        require(len(nominal) == 1 and float(nominal[0]) == values[key], f'Nominal {key} mismatch')
    default = re.findall(r'default_operating_conditions\s*:\s*([^;]+);', text)
    require(len(default) == 1 and default[0].strip().strip('"') == name.strip().strip('"'),
            f'Unexpected default conditions: {path}')
    return dict(path=str(path), upstream_path=source_path, git_blob=blob(body),
                conditions=values, temperature_scaling_tokens=re.findall(r'\bk_temp_\w+', text),
                internal_power_groups=len(re.findall(r'\binternal_power\s*\(', text)))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    require(not args.output.exists(), 'Preserve earlier assessments; choose a new output')
    read(Path(__file__))
    acceptance = load('physical/experiments/design-acceptance-readback-results.json')
    report = load(**{'path': acceptance['report']['path'], 'expected': acceptance['report']['sha256']})
    require(report['A_accepted'] is False, 'This assessment targets the refused A checkpoint')
    for record in acceptance['candidate'].values():
        read(record['path'], record['sha256'])
    contract = load('physical/fixtures/sram-trust/contract.json')
    load('physical/experiments/sram-trust-results.json')
    load('physical/experiments/sram-tile-results.json')
    request = load('build/validation/sram-trust-01/request.json')
    pdk = Path(request['pdk_root'])
    lock = load('tools/physical-toolchain.json')
    pinned_sha, pinned = tree('build/physical/upstream/pdk-tree.json')
    commit = load('build/validation/sram-trust-01/sources-01/pdk-pinned-commit.json')
    require(commit['sha'] == lock['pdk_revision'] == contract['pdk_revision'], 'PDK revision mismatch')
    require(commit['commit']['tree']['sha'] == pinned_sha, 'Pinned tree mismatch')
    for capture_dir in ('sources', 'tool-sources'):
        receipt = load(BASE / capture_dir / 'receipt.json')
        if isinstance(receipt, dict):
            require(receipt['status'] == 'completed', 'Incomplete public capture')
            rows = receipt['sources']
        else:
            rows = receipt
        for row in rows:
            require(row['status'] == 200, 'Failed public source capture')
            path = BASE / row['path'] if capture_dir == 'sources' else BASE / capture_dir / row['path']
            read(path, row['sha256'])

    prefix = 'ihp-sg13cmos5l/libs.ref/sg13cmos5l_stdcell/lib/'
    cell_paths = sorted(p for p in pinned if p.startswith(prefix) and p.endswith('.lib'))
    macro_paths = sorted(p for p in pinned if p.startswith(
        'ihp-sg13g2/libs.ref/sg13g2_sram/lib/' + contract['macro']) and p.endswith('.lib'))
    require(len(cell_paths) == 6 and len(macro_paths) == 3, 'Library inventory changed')
    libraries = [library(pdk / p, p, pinned) for p in cell_paths]
    for p in macro_paths:
        record = next(x for x in contract['supplied_views'] if x['upstream_path'] == p)
        read(record['path'], record['sha256'])
        libraries.append(library(record['path'], p, pinned))
    for record in contract['supplied_views'] + [contract['behavioral_dependency']]:
        body = read(record['path'], record['sha256'])
        require(blob(body) == record['git_blob'] == pinned[record['upstream_path']]['sha'],
                'Supplied view is not the pinned Git blob')

    upstream = {}
    identity_paths = [x['upstream_path'] for x in contract['supplied_views']] + cell_paths
    for branch in ('main', 'dev'):
        head = load(BASE / 'sources' / f'{branch}-head.json')
        tree_sha, inventory = tree(BASE / 'sources' / f'{branch}-tree.json')
        require(tree_sha == head['commit']['tree']['sha'], 'Public commit/tree mismatch')
        available = {p: inventory[p]['sha'] for p in inventory if
                     (p.startswith(prefix) or p.startswith('ihp-sg13g2/libs.ref/sg13g2_sram/lib/' + contract['macro']))
                     and p.endswith('.lib')}
        upstream[branch] = dict(revision=head['sha'], committed_at=head['commit']['committer']['date'],
            inventory=available, identities={p: dict(pinned=pinned[p]['sha'],
                captured=inventory[p]['sha'] if p in inventory else None,
                equal=p in inventory and pinned[p]['sha'] == inventory[p]['sha']) for p in identity_paths})

    pr = load(BASE / 'sources/pr-1121.json')
    changes = load(BASE / 'sources/pr-1121-files.json')
    require(len(changes) == pr['changed_files'], 'Incomplete pull-request file inventory')
    target = next(x for x in changes if x['filename'].endswith('/' + contract['macro'] + '.cdl'))
    require(pr['head']['sha'] in target['raw_url'], 'Pull-request file is from a different revision')
    patch = target['patch']
    bit_resistors = [line for line in patch.splitlines() if re.match(r'^\+R[012] (BLC_BOT BLC_TOP|BLT_BOT BLT_TOP|RWL LWL) ', line)]
    require(len(bit_resistors) == 3, 'Could not isolate proposed single-port bit-cell changes')

    final = ROOT / 'build/validation/chip-finalization-01'
    power_dir = final / 'finalize-01/output/flow/05-openroad-irdropreport'
    config = load(power_dir / 'config.json')
    read(power_dir / '_env.tcl')
    power_text = read(power_dir / 'irdrop.rpt').decode()
    power_report = {}
    for part in power_text.split('Net              : ')[1:]:
        net = part.splitlines()[0].strip()
        values = {}
        for name, label in [('total_power_w', 'Total power'), ('supply_v', 'Supply voltage'),
                            ('worst_drop_v', 'Worstcase IR drop')]:
            found = re.findall(re.escape(label) + r'\s*:\s*([-+\d.eE]+)', part)
            require(len(found) == 1, f'Missing power metric: {net}/{label}')
            values[name] = float(found[0])
        power_report[net] = values
    require(set(power_report) == {'VPWR', 'VGND'}, 'Incomplete rail analysis')
    power_summary = read(final / 'inspect-02/output/sta/nom_typ_1p20V_25C/power.rpt').decode()
    power_groups = {}
    for group in ('Total', 'Macro'):
        row = re.findall(r'^' + group + r'\s+([\d.eE+-]+)\s+([\d.eE+-]+)\s+([\d.eE+-]+)\s+([\d.eE+-]+)', power_summary, re.M)
        require(len(row) == 1, f'Missing power group: {group}')
        power_groups[group] = dict(zip(('internal_w', 'switching_w', 'leakage_w', 'total_w'), map(float, row[0])))
    def_text = read(acceptance['candidate']['def']['path']).decode()
    pins = re.search(r'^PINS\s+(\d+)\s*;(.*?)^END PINS', def_text, re.M | re.S)
    require(pins is not None, 'Missing DEF pins')
    entries = re.findall(r'^\s*- (.*?)\s*;', pins[2], re.M | re.S)
    require(len(entries) == int(pins[1]), 'DEF pin parse incomplete')
    power_pins = {}
    for entry in entries:
        if re.search(r'\+ USE (POWER|GROUND)', entry):
            power_pins[entry.split()[0]] = dict(
                port_count=entry.count('+ PORT'),
                shape_layers=dict(Counter(re.findall(r'\+ LAYER (\S+)', entry))))
    require(set(power_pins) == {'VPWR', 'VGND'}, 'Missing physical power terminals')
    min_report = read(final / 'inspect-02/output/sta/nom_fast_1p32V_m40C/min.rpt').decode()
    first_path = min_report.split('Startpoint: ', 1)[1].split('Startpoint: ', 1)[0]
    hold_text = read(final / 'inspect-02/output/sta/nom_fast_1p32V_m40C/write-hold.rpt').decode()
    hold = []
    for bit, body in re.findall(r'PINWHEEL_WRITE (\d+)\n(.*?)(?=PINWHEEL_WRITE |\Z)', hold_text, re.S):
        match = re.search(r'([-\d.]+)\s+slack \(', body)
        require(match is not None, 'Missing write hold path')
        hold.append(dict(bit=int(bit), slack_ns=float(match[1])))
    require(sorted(x['bit'] for x in hold) == list(range(64)), 'Missing or duplicate SRAM write bits')
    tool_root = pdk.parent / 'librelane'
    for p in ['nix/openroad.nix', 'nix/opensta.nix', 'librelane/scripts/openroad/irdrop.tcl',
              'librelane/scripts/openroad/common/io.tcl', 'librelane/steps/openroad.py']:
        read(tool_root / p)
    read('build/validation/sram-trust-01/sources-02/pdk-pinned/ihp-sg13g2/libs.ref/sg13g2_sram/doc/' + contract['macro'] + '.txt')
    issues = {}
    for number in (239, 794):
        issue = load(BASE / 'sources' / f'issue-{number}.json')
        comments = load(BASE / 'sources' / f'issue-{number}-comments.json')
        require(len(comments) == issue['comments'], 'Incomplete discussion')
        issues[number] = dict(state=issue['state'], updated_at=issue['updated_at'],
                              captured_comments=len(comments), url=issue['html_url'])

    result = dict(schema=1, status='inventory_audited', cad_seconds=0,
        A_accepted=False, B_admitted=False, complete_design_iteration=False,
        acceptance_checkpoint=acceptance['report'], candidate=acceptance['candidate'],
        inherited_blockers=acceptance['blockers'], libraries=libraries, upstream=upstream,
        issues=issues, lvsres_proposal=dict(url=pr['html_url'], state=pr['state'], draft=pr['draft'],
            merged_at=pr['merged_at'], revision=pr['head']['sha'], updated_at=pr['updated_at'],
            complete_changed_file_count=len(changes), target_git_blob=target['sha'],
            proposed_bitcell_resistor_lines=bit_resistors),
        retained_timing=dict(global_fast_hold_start=first_path.splitlines()[0],
            global_fast_hold_slack_ns=float(re.search(r'([-\d.]+)\s+slack \(', first_path)[1]),
            sram_write_hold_paths=len(hold), worst_sram_write_hold=min(hold, key=lambda x: x['slack_ns'])),
        retained_power=dict(default_corner=config['DEFAULT_CORNER'], clock_period_ns=config['CLOCK_PERIOD'],
            explicit_source_files=config['VSRC_LOC_FILES'], reports=power_report, block_pin_shapes=power_pins,
            sta_power_groups=power_groups,
            runtime_source_count_measured=False, activity_waveforms_replayed=False),
        boundary='Read-only inventory and source interpretation. No new CAD, qualification, acceptance, or physical replay.',
        inputs=files.copy())
    for path, record in files.items():
        require(hashlib.sha256((ROOT / path).read_bytes()).hexdigest() == record['sha256'], 'Inputs changed during audit')
    with args.output.open('x') as stream:
        json.dump(result, stream, indent=2)
        stream.write('\n')
    print(json.dumps(dict(status=result['status'], files=len(files), libraries=len(libraries),
                          A_accepted=False, cad_seconds=0)))


if __name__ == '__main__':
    main()
