#!/usr/bin/env python3
"""Kernel-check resident uploads and prove meaningful corruptions false."""
import argparse
from dataclasses import replace
import json
from pathlib import Path
import time

from paired_execution import compile_resident
from pinwheel_program import resident_uart, resident_spi
from resident_image_certificate import render, MARKER
from validation_run import Commands, fresh_directory, sha

ROOT = Path(__file__).resolve().parents[1]


def corruptions(source, image):
    yield 'boot_level', source.words, replace(image, boot=image.boot ^ 8), None
    rows = list(image.rows)
    rows[0] ^= 1 << 22
    yield 'successor_row', source.words, replace(image, rows=tuple(rows)), None
    rows = list(image.rows)
    rows[-1] = 7 | 7 << 32
    yield 'unused_row', source.words, replace(image, rows=tuple(rows)), None
    yield 'idle', source.words, replace(image, idle=(source.idle_levels ^ 1, source.idle_enabled)), None
    words = list(source.words)
    words[1] |= 1 << 63
    yield 'reserved_source', words, image, None
    words = list(source.words)
    words[1] = (words[1] & ~(3 << 29)) | 3 << 29
    yield 'invalid_shift_pin', words, image, None
    params = list(image.parameters)
    shift = image.rows[0] & 0xffffffff
    params[shift >> 17 & 31] ^= 4
    yield 'shift_order', source.words, replace(image, parameters=tuple(params)), None
    yield 'truncated_upload', source.words, image, image.upload()[:-1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--tag', required=True)
    args = parser.parse_args()
    out = fresh_directory(ROOT/'build/validation', args.tag)
    run = Commands(ROOT, out, default_timeout=120)
    report = dict(schema=1, status='running', commands=run.records, positive=[], negative=[], cad_seconds=0,
                  scope='Resident source grammar, operands, successor histories and exact upload bytes; '
                        'not whole timed package refinement or physical SRAM qualification.')
    start = time.monotonic()
    sources = [ROOT/'Pinwheel/Hardware/Storage/PairedResidentImage.lean',
               ROOT/'Pinwheel/Hardware/Storage/PairedImage.lean',
               *[ROOT/'scripts'/name for name in ('check-resident-image.py', 'resident_image_certificate.py',
                'paired_image_certificate.py', 'paired_execution.py', 'pinwheel_program.py',
                'pinwheel_host.py', 'execution-vectors.py', 'validation_run.py', 'process_group.py')],
               ROOT/'lean-toolchain', ROOT/'lakefile.toml']
    report['source_sha256'] = {str(p.relative_to(ROOT)): sha(p) for p in sources}
    try:
        run(['lake', 'build', 'Pinwheel.Hardware.Storage.PairedResidentImage'], 'build')
        lean = ['lake', 'env', 'lean', '-DwarningAsError=true']
        for name, source in [('uart', resident_uart()), ('spi', resident_spi())]:
            image = compile_resident(source.words, (source.idle_levels, source.idle_enabled), source.last)
            path = out/(name+'.lean')
            path.write_text(render(name, source.words, source.last,
                                   (source.idle_levels, source.idle_enabled), image, source.upload_words()))
            if MARKER not in run([*lean, path], name):
                raise RuntimeError('Missing resident certificate audit')
            report['positive'].append(dict(name=name, certificate_sha256=sha(path)))
        source = resident_uart()
        image = compile_resident(source.words, (source.idle_levels, source.idle_enabled), source.last)
        for name, words, candidate, uploaded in corruptions(source, image):
            text = render(name, words, source.last, (source.idle_levels, source.idle_enabled),
                          candidate, candidate.upload() if uploaded is None else uploaded)
            path = out/(name+'.lean')
            path.write_text(text)
            run([*lean, path], name, reject='error: Tactic `decide` proved that the proposition')
            negated = text.replace('theorem accepted : check source image uploaded = true',
                                   'theorem rejected : check source image uploaded = false')
            negated = negated.replace(f'.{name}.accepted', f'.{name}.rejected')
            path = out/(name+'_rejected.lean')
            path.write_text(negated)
            if MARKER not in run([*lean, path], name+'_false'):
                raise RuntimeError('Missing corruption negation audit')
            report['negative'].append(dict(name=name, negation_kernel_checked=True, certificate_sha256=sha(path)))
        for name, digest in report['source_sha256'].items():
            if sha(ROOT/name) != digest:
                raise RuntimeError('Source changed during resident certificate gate: '+name)
        report['status'] = 'passed'
    except BaseException as error:
        report.update(status='failed', error=str(error))
        raise
    finally:
        report['elapsed_seconds'] = round(time.monotonic()-start, 3)
        report['artifacts_sha256'] = {p.name: sha(p) for p in out.iterdir() if p.is_file() and p.name != 'report.json'}
        (out/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    print('Resident image gate passed: '+str(out/'report.json'), flush=True)


if __name__ == '__main__':
    main()
