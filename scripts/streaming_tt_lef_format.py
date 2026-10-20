#!/usr/bin/env python3
"""Preserve actual LEF geometry while spelling micrometer coordinates as FP3.

The pinned official pin checker left-pads short decimal fractions and requires
single spaces inside geometry statements. This derivative changes numeric and
whitespace spelling only; original geometry/checker bytes remain unchanged.
"""
import argparse
from decimal import Decimal, InvalidOperation
import hashlib
from pathlib import Path
import re
import subprocess

import streaming_tt_native_layout_diagnostic as D
from streaming_tt_intake import dependency_closure
from streaming_tt_signoff import read, regular, require, sha, unchanged, write
from validation_run import fresh_directory

P = D.P
ENTRIES = ('scripts/streaming_tt_lef_format.py',)
NUMBER = re.compile(r'-?(?:0|[1-9][0-9]*)(?:\.[0-9]+)?\Z')
FIELDS = {'CUTSIZE': (1, 2), 'CUTSPACING': (1, 2),
          'ENCLOSURE': (1, 2, 3, 4), 'ORIGIN': (1, 2),
          'RECT': (1, 2, 3, 4), 'SIZE': (1, 3), 'FOREIGN': (2, 3)}
ARITIES = {'CUTSIZE': 4, 'CUTSPACING': 4, 'ENCLOSURE': 6, 'ORIGIN': 4,
           'RECT': 6, 'SIZE': 5, 'FOREIGN': 5}
BOUNDARY = ('Exact Decimal identity of every supported emitted LEF coordinate, '
    'with unchanged pin membership, types, layer names and all other tokens. '
    'Numeric spelling is padded to three fractional digits and geometry-statement '
    'inter-token whitespace becomes one space and geometry trailing whitespace '
    'is removed for the unchanged official checker. Indentation and LF endings '
    'are preserved; all nongeometry lines remain byte-identical. '
    'No geometry, design, DRC/LVS result, '
    'candidate flow completion or physical acceptance is changed.')


def coordinate(raw):
    require(type(raw) is str and NUMBER.fullmatch(raw), 'Unsupported LEF coordinate literal')
    try:
        value = Decimal(raw)
        require(value.is_finite() and len(value.as_tuple().digits) <= 24 and
            value * 1000 == (value * 1000).to_integral_value(),
            'LEF coordinate is not an exact finite nanometer value')
        return value
    except InvalidOperation as error:
        raise ValueError('Invalid LEF coordinate') from error


def model(text):
    require(type(text) is str and text and '\r' not in text and '\x00' not in text,
        'Expected emitted UTF-8 LEF text with LF line endings')
    signature = []
    records = []
    macros = []
    pins = []
    sizes = []
    for line in text.splitlines(keepends=True):
        tokens = list(re.finditer(r'\S+', line))
        if not tokens:
            signature.append(('literal', line)); continue
        words = [token.group() for token in tokens]
        keyword = words[0]
        require(keyword not in ('POLYGON', 'PATH', 'ITERATE'),
            'Unsupported geometry directive in emitted LEF')
        if keyword == 'MACRO':
            require(len(words) == 2, 'Malformed LEF macro'); macros.append(words[1])
        if keyword == 'PIN':
            require(len(words) == 2, 'Malformed LEF pin'); pins.append(words[1])
        if keyword not in FIELDS:
            signature.append(('literal', line)); continue
        require(len(words) == ARITIES[keyword] and words[-1] == ';' and
            (keyword != 'SIZE' or words[2] == 'BY'), 'Malformed emitted LEF geometry statement')
        indices = FIELDS[keyword]
        values = tuple(coordinate(words[index]) for index in indices)
        require(keyword != 'RECT' or values[0] <= values[2] and values[1] <= values[3],
            'Reversed emitted LEF rectangle')
        normalized = list(words)
        for index, value in zip(indices, values):
            normalized[index] = ('coordinate', value)
        signature.append(('geometry', tuple(normalized)))
        records.append((line, tokens, indices, values))
        if keyword == 'SIZE': sizes.append(values)
    require(len(macros) == 1 and len(sizes) == 1 and pins and len(pins) == len(set(pins)),
        'Expected one macro/size and unique nonempty emitted pin membership')
    return dict(signature=tuple(signature), records=records, top=macros[0],
        pins=tuple(pins), size=sizes[0])


def canonicalize(text):
    parsed = model(text)
    output = []
    changed = 0
    count = 0
    whitespace_changed = 0
    for line in text.splitlines(keepends=True):
        tokens = list(re.finditer(r'\S+', line))
        if not tokens or tokens[0].group() not in FIELDS:
            output.append(line); continue
        words = [token.group() for token in tokens]
        for index in FIELDS[tokens[0].group()]:
            token = tokens[index]
            value = format(coordinate(token.group()), '.3f')
            words[index] = value
            changed += value != token.group(); count += 1
        prefix = line[:tokens[0].start()]
        suffix = '\n' if line.endswith('\n') else ''
        whitespace_changed += prefix + ' '.join(token.group() for token in tokens) + suffix != line
        output.append(prefix + ' '.join(words) + suffix)
    derived = ''.join(output)
    require(model(derived)['signature'] == parsed['signature'], 'LEF canonicalization changed exact geometry/type/text')
    return derived, dict(coordinate_literals=count, changed_literals=changed,
        whitespace_changed_statements=whitespace_changed,
        top=parsed['top'], pins=list(parsed['pins']), pin_count=len(parsed['pins']),
        size_um=[str(value) for value in parsed['size']])


def validate_equivalence(original, derived):
    expected, summary = canonicalize(original)
    require(type(derived) is str and model(original)['signature'] == model(derived)['signature'],
        'Derived LEF changed geometry, type, pin membership or noncoordinate tokens')
    require(derived == expected, 'Derived LEF differs from exact deterministic FP3 spelling')
    return summary


def run(export_path, tag):
    values, packet = D.actual_inputs(export_path)
    _, _, top, _, _, frozen = values
    source = regular(Path(export_path).parent/'native/implemented.lef')
    require(packet['signoff_views']['artifacts_sha256'].get('implemented.lef') == sha(source),
        'Actual native LEF differs from closed signoff export')
    original = source.read_bytes()
    text = original.decode('ascii')
    derived, summary = canonicalize(text)
    require(summary['top'] == top and summary['pin_count'] == 45 and
        {'VPWR', 'VGND'} <= set(summary['pins']), 'Actual TT LEF top/pin inventory differs')
    closure = dependency_closure(P.ROOT, ENTRIES)
    commit = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=P.ROOT, text=True).strip()
    producer = {name: hashlib.sha256(P.committed(P.ROOT/name)).hexdigest() for name in closure['files']}
    frozen.update({str(P.ROOT/name): value for name, value in producer.items()})
    frozen[str(source)] = sha(source)
    out = fresh_directory(P.ROOT/'build/streaming-tt-lef-format', tag).resolve()
    target = out/'implemented.fp3.lef'
    target.write_bytes(derived.encode('ascii'))
    validate_equivalence(text, target.read_text())
    unchanged(frozen)
    require(source.read_bytes() == original, 'Original native LEF changed')
    write(out/'report.json', dict(schema='pinwheel.streaming-tt-lef-format-diagnostic.v1',
        passed=True, qualified=False, physical_acceptance_claim=False,
        geometry_changed=False, exact_decimal_identity=True, pin_membership_identical=True,
        noncoordinate_tokens_identical=True, nongeometry_text_identical=True,
        geometry_intertoken_whitespace='single-space', geometry_trailing_whitespace='removed',
        geometry_indentation_and_lf_endings='preserved', canonical_fractional_digits=3,
        producer_commit=commit, producer_sha256=producer, producer_dependency_closure=closure,
        source_gds_export_report=str(regular(export_path)), source_gds_export_report_sha256=sha(export_path),
        actual_database_sha256=packet['actual_database_sha256'],
        original_native_lef=str(source), original_native_lef_sha256=sha(source),
        canonical_lef=str(target), canonical_lef_sha256=sha(target), summary=summary,
        input_sha256_before=frozen, input_sha256_after=frozen, inputs_unchanged=True,
        boundary=BOUNDARY))
    return out/'report.json'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--gds-export-report', required=True, type=Path)
    parser.add_argument('--tag', required=True)
    args = parser.parse_args()
    print(run(args.gds_export_report, args.tag), flush=True)


if __name__ == '__main__': main()
