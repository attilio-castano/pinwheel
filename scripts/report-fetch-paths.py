#!/usr/bin/env python3
"""Break down retained OpenSTA setup paths without changing implementation data.

Cell delay includes the effect of output load and slew. Wire arc delay alone
therefore does not measure the complete cost of interconnect or fanout.
"""
import argparse
import hashlib
import json
import re
from collections import Counter
from pathlib import Path
from statistics import median

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / 'build/physical/core'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def parse_path(block):
    header = block.splitlines()
    start = header[0].removeprefix('Startpoint: ').split(' (')[0]
    endpoint = next(s for s in header if s.startswith('Endpoint: ')).removeprefix('Endpoint: ').split(' (')[0]
    data = block.split('data arrival time', 1)[0]
    arrival = float(re.search(r'([-\d.]+)\s*$', data)[1])
    required = float(re.search(r'([-\d.]+)\s+data required time', block)[1])
    slack = float(re.search(r'([-\d.]+)\s+slack \(', block)[1])
    rows = []
    read_b_time = None
    for line in data.splitlines():
        if re.search(r'read_b\[\d+\] \(net\)', line) and rows:
            read_b_time = rows[-1]['time_ns']
        match = re.fullmatch(r'\s*([\d.\s-]+)\s+[\^v]\s+(\S+)\s+\((\S+)\)\s*', line)
        if not match:
            continue
        fields = match[1].split()
        if len(fields) not in (3, 5):
            raise RuntimeError(f'Unexpected timing row: {line}')
        delay, time = map(float, fields[-2:])
        category = ('wire' if len(fields) == 3 else 'port' if match[3] == 'in'
                    else 'buffer' if '_buf_' in match[3]
                    else 'delay_cell' if '_dlygate' in match[3] else 'logic')
        rows.append(dict(pin=match[2], cell=match[3], category=category, delay_ns=delay,
                         time_ns=time, slew_ns=float(fields[-3]),
                         fanout=int(fields[0]) if len(fields) == 5 else None))
    external_match = re.search(r'([-\d.]+)\s+([-\d.]+)\s+[\^v] input external delay', data)
    external = float(external_match[1]) if external_match else None
    launch_clock = None
    if external is None:
        # Separate the launch clock tree from the data path. Keep clock-to-Q as
        # its own contribution rather than counting the launch FF as logic.
        launch = next((n for n, r in enumerate(rows)
                       if r['pin'].startswith(start + '/') and r['fanout'] is not None), None)
        if launch is None:
            raise RuntimeError(f'Cannot identify launch register output for {start}')
        rows = rows[launch:]
        launch_clock = rows[0]['time_ns'] - rows[0]['delay_ns']
        rows[0]['category'] = 'clock_to_q'
    sums = {k: sum(r['delay_ns'] for r in rows if r['category'] == k)
            for k in ['logic', 'buffer', 'delay_cell', 'wire', 'port', 'clock_to_q']}
    origin = external if external is not None else launch_clock
    if abs(origin + sum(sums.values()) - arrival) > 0.0001:
        raise RuntimeError(f'Timing accounting mismatch for {start} -> {endpoint}')
    return dict(start=start, endpoint=endpoint, arrival_ns=arrival, required_ns=required, slack_ns=slack,
                external_delay_ns=external, launch_clock_arrival_ns=launch_clock, delay_ns=sums,
                output_cell_arcs=sum(r['category'] in ('buffer', 'logic', 'delay_cell', 'clock_to_q') for r in rows),
                max_slew_ns=max(r['slew_ns'] for r in rows),
                max_data_fanout=max((r['fanout'] or 0) for r in rows),
                before_read_b_ns=read_b_time - origin if read_b_time is not None else None,
                after_read_b_ns=arrival - read_b_time if read_b_time is not None else None,
                slowest_arcs=sorted(rows, key=lambda r: r['delay_ns'], reverse=True)[:5])


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--tag', default='routed4')
    parser.add_argument('--corner', default='nom_slow_1p08V_125C')
    args = parser.parse_args()
    run = BASE / 'runs' / args.tag
    stages = sorted(run.glob('*-openroad-stapostpnr'))
    if len(stages) != 1:
        raise RuntimeError('Expected one final extracted-STA stage')
    report_path = stages[0] / args.corner / 'max.rpt'
    blocks = re.split(r'(?=^Startpoint:)', report_path.read_text(), flags=re.M)[1:]
    paths = [parse_path(block) for block in blocks]
    if not paths:
        raise RuntimeError('No setup paths found')
    state = json.loads((stages[0] / 'state_out.json').read_text())
    netlist = BASE / state['nl'].removeprefix('/work/core/')
    text = netlist.read_text()
    top20 = sorted(paths, key=lambda p: p['slack_ns'])[:20]
    for path in top20:
        match = re.search(r'\b' + re.escape(path['endpoint']) + r'\s*\((.*?)\);', text, re.S)
        q = re.search(r'\.Q\(\s*(.*?)\s*\)', match[1]) if match else None
        path['endpoint_q'] = q[1] if q else None
    worst = min(paths, key=lambda p: p['slack_ns'])
    report = dict(tag=args.tag, corner=args.corner, reported_paths=len(paths),
                  violating_reported_paths=sum(p['slack_ns'] < 0 for p in paths),
                  startpoints=dict(Counter(p['start'] for p in paths)),
                  median_slack_ns=median(p['slack_ns'] for p in paths), worst=worst,
                  top20=top20,
                  source_sha256={str(p.relative_to(ROOT)): digest(p) for p in
                                 [report_path, netlist, run / 'resolved.json', Path(__file__).resolve()]},
                  boundary='Retained maximum-path report, potentially truncated by STA reporting limits. '
                           'Path counts are not unique violating-endpoint counts. Delays use report precision; '
                           'cell delays include loading effects. The read_b split is an observed named-net boundary, '
                           'not a complete separation of address-map and dictionary logic.')
    out = ROOT / 'build/successor-fetch' / args.tag
    out.mkdir(parents=True, exist_ok=True)
    filename = 'paths.json' if args.corner == 'nom_slow_1p08V_125C' else f'paths-{args.corner}.json'
    (out / filename).write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items() if k not in ['top20', 'source_sha256']}, indent=2))


if __name__ == '__main__':
    main()
