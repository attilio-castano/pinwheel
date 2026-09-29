#!/usr/bin/env python3
"""Kernel-check concrete paired images and meaningful corruptions without CAD.

This checks canonical E64 image/dispatch correspondence, not complete controller
refinement. Optional protocol fixtures must be supplied with their expected hash.
"""
import argparse
from dataclasses import replace
from datetime import datetime, timezone
import json
from pathlib import Path
import sys
import time

from paired_execution import compile_e64, GRAMMAR
from paired_image_certificate import render
from validation_run import Commands, fresh_directory, sha

ROOT = Path(__file__).resolve().parents[1]
MARKER = 'Paired image certificate: kernel checked; standard axioms only.'


def fixtures():
    pack = GRAMMAR['pack']
    branch = [pack(dict(kind=2, levels=3, enabled=7, duration=255, entry=63,
                        terminal=61, check=15, finish=2, sample=15, yes=0, no=2)),
              pack(dict(kind=3, duration=255, budget=255, check=15)),
              pack(dict(kind=1, duration=255, check=3))]
    return [
        ('halt', [4], 0, (0, 0)),
        ('linear', [pack(dict(levels=1, duration=1)),
                    pack(dict(levels=2, duration=2)), 4], 2, (5, 7)),
        ('branch_capture_wait_qualify', branch, 2, (7, 3)),
        ('last_address_fault', [pack(dict(kind=2, finish=1, yes=255)), 4], 1, (0, 0)),
        ('padded_address_halt', [pack(dict(kind=2, finish=1, yes=255)), 4], 255, (0, 0)),
        ('all_positions_parameters', [pack(dict(entry=1+2*(k//16)+4*(k%16)))
                                      for k in range(32)]*8, 255, (7, 7)),
    ]


def corruptions(words, last, idle, image):
    def changed(name, candidate):
        return name, words, last, idle, candidate, candidate.upload()
    yield changed('boot_levels', replace(image, boot=image.boot ^ 8))
    yield changed('reserved_token_bit', replace(image, boot=image.boot | 1 << 31))
    params = list(image.parameters)
    params[image.boot >> 17 & 31] ^= 1 << 6  # terminal-capture descriptor
    yield changed('parameter_capture', replace(image, parameters=tuple(params)))
    rows = list(image.rows)
    rows[0] = rows[0] >> 32 | (rows[0] & 0xffffffff) << 32
    yield changed('branch_halves_swapped', replace(image, rows=tuple(rows)))
    rows = list(image.rows)
    rows[0] ^= 1 << (32+22)  # true successor's address
    yield changed('successor_address', replace(image, rows=tuple(rows)))
    rows = list(image.rows)
    rows[-1] = 7 | 7 << 32
    yield changed('unused_row', replace(image, rows=tuple(rows)))
    yield changed('idle', replace(image, idle=(idle[0] ^ 1, idle[1])))
    raw = list(image.upload())
    raw[0] |= 1 << 63
    yield 'upload_reserved_bits', words, last, idle, image, raw
    yield 'upload_truncated', words, last, idle, image, image.upload()[:-1]
    bad_words = [words[0] | 1 << 63, *words[1:]]
    yield 'noncanonical_source', bad_words, last, idle, image, image.upload()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--tag', required=True)
    parser.add_argument('--images', type=Path)
    parser.add_argument('--images-sha256')
    args = parser.parse_args()
    if bool(args.images) != bool(args.images_sha256):
        parser.error('--images and --images-sha256 must be used together')
    out = fresh_directory(ROOT/'build/validation', args.tag)
    run = Commands(ROOT, out, default_timeout=120)
    started = time.monotonic()
    report = dict(schema=1, status='running', date=datetime.now(timezone.utc).isoformat(),
                  commands=run.records, positive=[], corruptions=[], cad_seconds=0,
                  scope='Canonical E64 bytes to exact paired upload words and all finite '
                        'successor-choice histories. Not timed controller, loader, RTL, '
                        'physical SRAM or resident SHIFT/KEEP refinement.')
    try:
        inputs = [ROOT/'Pinwheel.lean', *sorted((ROOT/'Pinwheel').rglob('*.lean')),
                  *[ROOT/p for p in ['scripts/check-paired-image.py',
                    'scripts/paired_image_certificate.py', 'scripts/paired_execution.py',
                    'scripts/execution-vectors.py', 'scripts/validation_run.py',
                    'scripts/process_group.py', 'lean-toolchain', 'lakefile.toml',
                    'lake-manifest.json']]]
        cases = fixtures()
        if args.images:
            if sha(args.images) != args.images_sha256:
                raise ValueError('Protocol fixture hash mismatch')
            inputs.append(args.images.resolve())
            for number, line in enumerate(args.images.read_text().splitlines()):
                label, *raw = line.split()
                last, levels, enabled, *words = map(int, raw)
                cases.append((f'protocol_{number}_{label.replace("-", "_")}',
                              words, last, (levels, enabled)))
        report['inputs_sha256'] = {str(p): sha(p) for p in inputs}
        run(['lake', 'build', 'Pinwheel.Hardware.Storage.PairedImage'], 'build')
        lean = ['lake', 'env', 'lean', '-DwarningAsError=true']
        for name, words, last, idle in cases:
            image = compile_e64(words, idle, last)
            path = out/(name+'.lean')
            path.write_text(render(name, words, last, idle, image, image.upload()))
            if MARKER not in run([*lean, path], name):
                raise ValueError('Missing certificate axiom audit')
            report['positive'].append(dict(name=name, positions=last+1,
                parameters=image.used_parameters, upload_words=len(image.upload()),
                certificate_sha256=sha(path)))
        _, words, last, idle = fixtures()[2]
        image = compile_e64(words, idle, last)
        for name, src, end, pins, candidate, raw in corruptions(words, last, idle, image):
            text = render(name, src, end, pins, candidate, raw)
            path = out/(name+'.lean')
            path.write_text(text)
            run([*lean, path], name, reject='error: Tactic `decide` failed for proposition')
            # A failed tactic alone is not evidence of a semantic corruption.
            # Also prove the exact acceptance proposition false in the kernel.
            negated = text.replace('theorem accepted : Execution.imageWords',
                                   'theorem rejected : ¬ (Execution.imageWords')
            negated = negated.replace('check source image uploaded = true := by',
                                     'check source image uploaded = true) := by')
            negated = negated.replace(f'.{name}.accepted', f'.{name}.rejected')
            negated_path = out/(name+'_rejected.lean')
            negated_path.write_text(negated)
            if MARKER not in run([*lean, negated_path], name+'_false'):
                raise ValueError('Missing corruption axiom audit')
            report['corruptions'].append(dict(name=name, rejected=True,
                negation_kernel_checked=True, certificate_sha256=sha(negated_path)))
        for path, digest in report['inputs_sha256'].items():
            if sha(path) != digest:
                raise ValueError('Source changed during check: '+path)
        report['status'] = 'passed'
    except BaseException as error:
        report.update(status='failed', error=str(error))
        raise
    finally:
        report['elapsed_seconds'] = round(time.monotonic()-started, 3)
        report['artifacts_sha256'] = {str(p.relative_to(out)): sha(p)
            for p in sorted(out.iterdir()) if p.is_file() and p.name != 'report.json'}
        (out/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    print('Paired image gate passed: '+str(out/'report.json'), flush=True)


if __name__ == '__main__':
    main()
