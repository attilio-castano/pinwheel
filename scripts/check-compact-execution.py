#!/usr/bin/env python3
"""Bounded model comparison. No RTL emission, synthesis, Docker or physical run."""
import argparse
from datetime import datetime, timezone
import json
from pathlib import Path
import re
import runpy
import shutil
import sys
import time

from compact_execution import uart_image, spi_image, branch_image, lower_e64, resource_budget
from validation_run import Commands, fresh_directory, sha

ROOT = Path(__file__).resolve().parents[1]


def write_json(path, value):
    with path.open('x') as stream:
        stream.write(json.dumps(value, indent=2) + '\n')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--tag', required=True)
    args = parser.parse_args()
    out = fresh_directory(ROOT / 'build/validation', args.tag)
    started = time.monotonic()
    inputs = [ROOT / p for p in [
        'scripts/compact_execution.py', 'scripts/check-compact-execution.py',
        'scripts/validation_run.py', 'scripts/process_group.py',
        'scripts/reactive-core-vectors.py', 'scripts/execution-vectors.py',
        'scripts/uart_rx_oracle.py', 'test/test_compact_execution.py',
        'test/CompactSchedule.lean', 'lean-toolchain', 'lakefile.toml',
        'tools/storage-macros.json', 'physical/experiments/chip-architecture-results.json',
        'physical/experiments/word-region-results.json',
        'physical/experiments/local-slew-results.json']]
    hardware = [ROOT / 'Pinwheel.lean', *sorted((ROOT / 'Pinwheel').rglob('*.lean'))]
    # Retained receipts are data, not commands or authority for another run.
    retained = {}
    for name in ('chip-architecture', 'word-region', 'local-slew'):
        path = ROOT / f'physical/experiments/{name}-results.json'
        manifest = json.loads(path.read_text())
        report = ROOT / manifest['report']
        if sha(report) != manifest['report_sha256']:
            raise ValueError('retained receipt differs: ' + name)
        inputs.append(report)
        retained[name] = dict(path=str(report.relative_to(ROOT)), sha256=sha(report))
    hashes = {str(p.relative_to(ROOT)): sha(p) for p in inputs + hardware}
    write_json(out / 'inputs.json', hashes)
    commands = Commands(ROOT, out, default_timeout=120)
    log = commands([sys.executable, '-B', '-m', 'unittest', 'discover', '-s', 'test',
                    '-p', 'test_compact_execution.py', '-v'], 'models')
    match = re.search(r'Ran (\d+) tests in ([0-9.]+)s\s+OK', log)
    if not match:
        raise ValueError('missing successful independent test summary')
    lake = shutil.which('lake')
    if not lake:
        raise ValueError('pinned Lean toolchain unavailable')
    proof_log = commands([lake, 'env', 'lean', 'test/CompactSchedule.lean'], 'schedule')
    if 'standard axioms only' not in proof_log:
        raise ValueError('missing compiled-environment axiom audit')
    text = (ROOT / 'test/CompactSchedule.lean').read_text()
    mutant = text.replace('end CompactSchedule',
                          'axiom forbidden : False\ntheorem bad : False := forbidden\nend CompactSchedule')
    if mutant == text:
        raise ValueError('missing axiom mutation anchor')
    mutant_path = out / 'ScheduleMutant.lean'
    mutant_path.write_text(mutant)
    commands([lake, 'env', 'lean', mutant_path], 'axiom-negative',
             reject='Unapproved compact schedule axioms')

    # Reuse the independent workload constructors, not candidate expected states.
    fixture = runpy.run_path(str(ROOT / 'test/test_compact_execution.py'))
    baseline = json.loads((ROOT / 'physical/experiments/chip-architecture-results.json').read_text())
    images = dict(uart=uart_image(), spi=spi_image(), branches=branch_image())
    programs = {}
    for name, image in images.items():
        artifact = out / f'{name}-image.json'
        write_json(artifact, dict(format='experimental-paired32-model-only',
                                 rows=list(image.rows), idle=image.idle,
                                 used_rows=image.used_rows))
        programs[name] = dict(used_rows=image.used_rows,
                              used_macro_bits=image.used_rows*64, upload_words=len(image.upload()))
    for name in ('uart', 'spi'):
        images_per_payload = [fixture[name + '_words'](byte) for byte in range(256)]
        unique = [len(set(ws + [4])) for ws in images_per_payload]
        programs[name]['baseline'] = dict(logical_instructions=len(images_per_payload[0]),
            distinct_E64_records_min=min(unique), distinct_E64_records_max=max(unique),
            per_image_index_bits=256*5, per_image_metadata_bits=14,
            upload_words=322, resident_payload_supported=False)
    counterexamples = []
    pack, fields, valid = (fixture[k] for k in ('pack', 'fields', 'valid'))
    cases = {
        '32-repeated-full-duration-actions': [pack(dict(levels=1, enabled=1, duration=255))]*32+[4],
        'qualifying-wait': [pack(dict(kind=3, duration=4, budget=7, check=1)), 4],
        'checked-guard': [pack(dict(kind=2, check=1)), 4],
        'independent-capture-slots': [pack(dict(kind=2, entry=1, terminal=7,
                                              finish=2, sample=2, yes=0, no=1)), 4],
    }
    for name, words in cases.items():
        if not all(valid(w) for w in words) or len(words) > 256 or len(set(words+[4])) > 32:
            raise ValueError('counterexample not admitted by current E64 capacity')
        try:
            lower_e64([fields(w) for w in words])
        except ValueError as error:
            counterexamples.append(dict(name=name, E64_words=words, reason=str(error),
                                        current_distinct_records=len(set(words+[4]))))
        else:
            raise ValueError('claimed counterexample accepted')
    write_json(out / 'counterexamples.json', counterexamples)
    comparison = dict(
        decision='retain-current-engine; reject-paired32-as-equivalent-replacement',
        next_gate='cost net3533 SRAM-only bit-41 buffering with both replicas and existing hold chain',
        candidate=resource_budget(), programs=programs, counterexamples=counterexamples,
        baseline=dict(mapped_register_bits=baseline['variants']['hybrid']['mapped_metrics']['flip_flops'],
                      declared_register_bits=2901, macro_count=2, macro_array_bits=8192,
                      index_map_bits=2560, macro= 'RM_IHPSG13_1P_64x64_c2_bm_bist'),
        branch_schedule=dict(
            before_edge='old Q holds both successors; terminal capture selects a half; entered word supplies its row',
            at_edge='latch entered operation and state; one SRAM read samples that row address',
            after_edge='new Q supplies both possible successors for the following edge',
            critical_dependency='SRAM Q -> input-dependent half selection -> 5-bit row -> SRAM address',
            independent_read_ports=1, hidden_combinational_reads=0,
            timing_claim='logical availability only; clock-to-Q, setup, hold and wires unmeasured'),
        evidence_boundary=[
            'Python clocked execution/command model; delivered commands and sampled inputs only.',
            'Independent wire formulas and existing E64 oracle; current code is specialized per payload.',
            'Two Lean schedule lemmas assume Closed image correspondence; no Python/Lean correspondence proof.',
            'Retained 12+76+35 wrapper bits are budgeted; package sampler/serial/mailbox RTL is not composed.',
            'Logical state budget includes all declared owners; no synthesized area or physical benefit claim.',
            'Encoding and loader format differ; no compatibility with identical raw E64 upload histories.',
            'One concrete compiler/layout rejected; no impossibility claim for all compact engines.'])
    write_json(out / 'comparison.json', comparison)
    changed = [name for name, digest in hashes.items() if sha(ROOT/name) != digest]
    if changed:
        raise ValueError('inputs changed during study: ' + ', '.join(changed))
    artifacts = {str(p.relative_to(ROOT)): sha(p) for p in sorted(out.iterdir()) if p.is_file()}
    report = dict(status='passed', date=datetime.now(timezone.utc).isoformat(),
                  scope='model comparison only', comparison=comparison,
                  focused_tests=int(match[1]), model_test_seconds=float(match[2]),
                  schedule_theorems=['CompactSchedule.step_related', 'CompactSchedule.trace_related'],
                  axiom_negative_rejected=True, behavioral_mutants_rejected=4,
                  coverage=dict(uart_payloads=256, spi_tx_rx_cases=256,
                                branch_histories=4096, branch_edges_per_history=6,
                                additional_consecutive_branch_edges=128,
                                uart_reset_positions=40,
                                wait_pins=2, wait_budgets=[0,1,7,255]),
                  commands=commands.records, source_sha256=hashes, artifact_sha256=artifacts,
                  preserved_receipts=retained, unchanged_hardware_sources=len(hardware),
                  seconds=round(time.monotonic()-started, 3))
    write_json(out / 'report.json', report)
    print(json.dumps({k: report[k] for k in ('status','focused_tests','seconds','unchanged_hardware_sources')}))
    print(comparison['decision'])


if __name__ == '__main__':
    main()
