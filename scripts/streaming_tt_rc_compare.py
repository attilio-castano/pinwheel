"""Read frozen RC research inputs as data; compare stacks without executing tools.

This is a host arithmetic/provenance review, not a field-solver calibration or
permission to install the draft models in a PDK.  Decimal division uses 50 digits.
"""
import argparse
from datetime import datetime, timezone
from decimal import Decimal, localcontext
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import subprocess


COMMITS = {1251: '9182b4ff461d90948ade30b1614d5000128cb9f7',
           1237: 'ffdafdbb4abb17316fa0ffd221ea99c0475c4734'}
METALS = ('Metal1', 'Metal2', 'Metal3', 'Metal4', 'TopMetal1')
ITF_DIR = 'ihp-sg13cmos5l/libs.tech/parasitics/itf/'
PROCESS_DIR = 'ihp-sg13cmos5l/libs.tech/librelane/openrcx/'
TOKEN = re.compile(r'\s+|[A-Za-z_][A-Za-z_0-9]*|[+-]?(?:[0-9]+(?:\.[0-9]*)?|\.[0-9]+)(?:[eE][+-]?[0-9]+)?|[{}=]')
NUMBER = re.compile(r'[+-]?(?:[0-9]+(?:\.[0-9]*)?|\.[0-9]+)(?:[eE][+-]?[0-9]+)?\Z')


def require(value, message):
    if not value:
        raise ValueError(message)


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, 'Duplicate JSON key: ' + key)
        result[key] = value
    return result


def read_json(path):
    return json.loads(path.read_text(), object_pairs_hook=unique_object)


def parse_stack(text):
    """Strict small grammar shared by the selected ITF and .process inputs.

    No eval, import, source rewriting, or invocation of downloaded code occurs.
    Unknown punctuation, duplicate fields/blocks, and nonnumeric numeric fields
    are errors.  A block's insertion order is retained for process metal indices.
    """
    clean = '\n'.join(re.split(r'[#$]', line, maxsplit=1)[0] for line in text.splitlines())
    tokens, offset = [], 0
    while offset < len(clean):
        match = TOKEN.match(clean, offset)
        require(match is not None, 'Unsupported stack token near: ' + clean[offset:offset + 30])
        token = match.group()
        if not token.isspace():
            tokens.append(token)
        offset = match.end()
    index = 0
    result = {}
    if tokens[:2] == ['TECHNOLOGY', '=']:
        require(len(tokens) >= 3 and tokens[2] == 'sg13cmos5l', 'Unsupported technology')
        index = 3
    numeric_fields = {
        'CONDUCTOR': {'THICKNESS', 'WMIN', 'SMIN', 'RPSQ', 'distance', 'thickness',
                      'min_width', 'min_spacing', 'resistivity', 'width_delta'},
        'DIELECTRIC': {'THICKNESS', 'ER', 'epsilon', 'thickness', 'next_met', 'met'},
        'VIA': {'AREA', 'RPV'},
    }
    string_fields = {'CONDUCTOR': {'LAYER_TYPE'}, 'DIELECTRIC': set(), 'VIA': {'FROM', 'TO'}}
    while index < len(tokens):
        require(index + 2 < len(tokens), 'Truncated stack block')
        kind, name, brace = tokens[index:index + 3]
        require(kind in numeric_fields and re.fullmatch(r'[A-Za-z_]\w*', name) and brace == '{',
                'Unsupported stack block')
        require((kind, name) not in result, 'Duplicate stack block: ' + name)
        index += 3
        fields = {}
        while index < len(tokens) and tokens[index] != '}':
            key = tokens[index]
            index += 1
            if index < len(tokens) and tokens[index] == '=':
                index += 1
            require(index < len(tokens), 'Truncated stack field')
            token = tokens[index]
            index += 1
            require(key not in fields, 'Duplicate stack field: ' + key)
            if key in numeric_fields[kind]:
                require(NUMBER.fullmatch(token), 'Nonnumeric stack field: ' + key)
                value = Decimal(token)
                require(value.is_finite() and (key == 'width_delta' or value > 0),
                        'Invalid numeric stack field: ' + key)
                if key in ('met', 'next_met'):
                    require(value == value.to_integral_value(), 'Noninteger metal index')
            else:
                require(key in string_fields[kind] and re.fullmatch(r'[A-Za-z_]\w*', token),
                        'Unsupported stack field: ' + key)
                value = token
            fields[key] = value
        require(index < len(tokens) and fields, 'Unclosed/empty stack block')
        index += 1
        result[(kind, name)] = fields
    require(result, 'Empty stack')
    return result


def checked_intake(base):
    """Verify all 21 selected Git blobs and both frozen intake producers."""
    base = Path(base).resolve()
    results, files, seen = [], {}, set()
    for filename, schema, count, producer in [
        ('report.json', 'pinwheel.rc-upstream-source-intake.v1', 18, 'fetch.py'),
        ('rules-intake.json', 'pinwheel.rc-draft-rules-intake.v1', 3, 'fetch-rules.py'),
    ]:
        intake_data = (base / filename).read_bytes()
        document = json.loads(intake_data, object_pairs_hook=unique_object)
        require(document['schema'] == schema and document['qualified'] is False and
                document['native_executed'] is False, 'Unexpected intake scope')
        require(len(document['files']) == count, 'Unexpected intake membership count')
        producer_data = (base / producer).read_bytes()
        require(sha256(producer_data) == document['producer_sha256'], 'Intake producer changed')
        results.append({'path': filename, 'sha256': sha256(intake_data),
                        'producer': producer, 'producer_sha256': sha256(producer_data), 'files': count})
        for row in document['files']:
            pr = row.get('pr', 1237)
            path = PurePosixPath(row['path'])
            require(pr in COMMITS and row['commit'] == COMMITS[pr], 'Unexpected upstream commit')
            require(not path.is_absolute() and '..' not in path.parts and str(path) == row['path'],
                    'Unsafe/noncanonical intake path')
            key = (pr, str(path))
            require(key not in seen, 'Duplicate intake file')
            seen.add(key)
            local = base / ('pr' + str(pr)) / str(path)
            require(local.resolve().is_relative_to(base) and not local.is_symlink(), 'Escaping/symlinked intake file')
            data = local.read_bytes()
            blob = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
            require(type(row['bytes']) is int and len(data) == row['bytes'] and
                    sha256(data) == row['sha256'] and blob == row['git_blob_sha1'],
                    'Intake file hash/size mismatch: ' + str(path))
            expected_url = 'https://raw.githubusercontent.com/IHP-GmbH/IHP-Open-PDK/' + COMMITS[pr] + '/' + str(path)
            require(row['url'] == expected_url, 'Unexpected source URL')
            files[key] = dict(row, pr=pr, local_path=str(local), verified_git_blob_sha1=blob)
    require(sum(pr == 1251 for pr, _ in files) == 3 and len(files) == 21, 'Unexpected PR membership')
    return results, files


def itf_metal_geometry(itf):
    """Silicon-surface reference explicitly stated in the draft process input.

    The lower M1 gap is fox + nitride + dummyOx.  Poly, active, and trench are
    not added as stacked metal heights.  oxN includes its lower metal thickness.
    This interprets the given stack convention; it does not establish foundry
    process geometry independently of the source descriptions.
    """
    gaps = [sum(itf['DIELECTRIC', name]['THICKNESS'] for name in ('fox', 'nitride', 'dummyOx'))]
    for below, dielectric in zip(METALS[:-1], ('ox1', 'ox2', 'ox3', 'ox4')):
        gaps.append(itf['DIELECTRIC', dielectric]['THICKNESS'] - itf['CONDUCTOR', below]['THICKNESS'])
    rows, height = {}, Decimal(0)
    for name, gap in zip(METALS, gaps):
        metal = itf['CONDUCTOR', name]
        require(gap > 0, 'Nonpositive derived ITF metal gap')
        bottom = height + gap
        height = bottom + metal['THICKNESS']
        rows[name] = {'gap_um': gap, 'bottom_um': bottom, 'top_um': height,
                      'thickness_um': metal['THICKNESS'], 'minimum_width_um': metal['WMIN'],
                      'minimum_spacing_um': metal['SMIN'], 'sheet_resistance_ohm': metal['RPSQ'],
                      'rho_ohm_um': metal['RPSQ'] * metal['THICKNESS']}
    return rows


def compare_corner(itf, process, corner, typ_geometry):
    require([name for kind, name in process if kind == 'CONDUCTOR'] == list(METALS),
            'Unexpected conductor membership/order')
    reference = itf_metal_geometry(itf)
    height, rows = Decimal(0), []
    for index, name in enumerate(METALS, 1):
        metal = process['CONDUCTOR', name]
        gap, thick, width, space, rho = (metal[field] for field in
                                        ('distance', 'thickness', 'min_width', 'min_spacing', 'resistivity'))
        delta = metal.get('width_delta', Decimal(0))
        require(width + delta > 0 and space - delta > 0, 'Invalid width-biased geometry')
        gap_dielectrics = [value for (kind, _), value in process.items()
                           if kind == 'DIELECTRIC' and value.get('next_met') == index]
        require(gap_dielectrics, 'Missing next_met dielectric gap')
        dielectric_sum = sum(value['thickness'] for value in gap_dielectrics)
        bottom = height + gap
        height = bottom + thick
        ref = reference[name]
        row = {'metal': name, 'merged_itf': ref,
               'draft_process': {'gap_um': gap, 'bottom_um': bottom, 'top_um': height,
                                 'thickness_um': thick, 'minimum_width_um': width, 'minimum_spacing_um': space,
                                 'rho_ohm_um': rho, 'width_delta_um': delta,
                                 'solver_wire_width_um_at_minimum_drawn_width': width + delta,
                                 'solver_spacing_um_at_minimum_drawn_spacing': space - delta,
                                 'same_rho_resistance_at_solver_width_ohm_per_um': rho / thick / (width + delta),
                                 'next_met_dielectric_thickness_sum_um': dielectric_sum},
               'matches_itf': {'gap': gap == ref['gap_um'], 'bottom': bottom == ref['bottom_um'],
                               'thickness': thick == ref['thickness_um'], 'width': width == ref['minimum_width_um'],
                               'spacing': space == ref['minimum_spacing_um'], 'rho_exact': rho == ref['rho_ohm_um']},
               'rho_difference_ohm_um': rho - ref['rho_ohm_um'],
               'rho_relative_difference_percent': 100 * (rho / ref['rho_ohm_um'] - 1),
               'dielectric_sum_minus_declared_gap_um': dielectric_sum - gap}
        if corner != 'TYP':
            numerator, denominator = ((37, 31 if corner == 'MIN' else 43) if index == 1 else
                                      (68, 54 if corner == 'MIN' else 82))
            expected = typ_geometry[name]['gap_um'] * Decimal(numerator) / Decimal(denominator)
            row['plate_fit'] = {'scale_ratio': f'{numerator}/{denominator}', 'expected_gap_um': expected,
                                'stored_minus_expected_gap_um': gap - expected,
                                'relative_rounding_percent': 100 * (gap / expected - 1)}
        rows.append(row)
    return rows


def inventory_rules(text, corner):
    """Inventory width support and first resistance grid only, not full RC syntax."""
    require(re.findall(r'^LayerCount\s+(\d+)\s*$', text, re.M) == ['5'], 'Wrong RC rule layer count')
    require(re.findall(r'^Corners\s+1\s*:\s*(\w+)\s*$', text, re.M) == [corner], 'Wrong RC rule corner')
    headers = list(re.finditer(r'^Metal (\d+) (\w+)\s*\nWIDTH Table (\d+) entries:([^\n]*)$', text, re.M))
    require(headers, 'No RC width tables')
    widths, empty, res = {}, [], {}
    for header in headers:
        metal, section, count, values = header.groups()
        values = values.split()
        require(len(values) == int(count) and
                all(NUMBER.fullmatch(value) and Decimal(value) > 0 for value in values), 'Bad RC width table')
        if not values:
            empty.append({'metal_index': int(metal), 'section': section})
        widths.setdefault(metal, set()).update(Decimal(value) for value in values)
    for metal in range(1, 6):
        matches = re.findall(r'^Metal ' + str(metal) + r' RESOVER 0\s*\nDIST count (\d+) width (\S+)\s*\n(.*?)^END DIST\s*$',
                             text, re.M | re.S)
        require(len(matches) == 1, 'Missing/duplicate first RC resistance grid')
        count, width, body = matches[0]
        require(NUMBER.fullmatch(width) and Decimal(width) > 0, 'Bad RC resistance grid width')
        rows = [line.split() for line in body.splitlines() if line.strip()]
        require(len(rows) == int(count) and rows and
                all(len(row) == 4 and all(NUMBER.fullmatch(value) for value in row) for row in rows),
                'Bad RC resistance grid')
        resistances = {Decimal(row[3]) for row in rows}
        require(len(resistances) == 1, 'Nonuniform first RC resistance grid')
        res[str(metal)] = {'width_um': Decimal(width), 'rows': len(rows), 'resistance_ohm_per_nm': resistances.pop()}
    return {'scope': 'width-table inventory and first RESOVER grid; not full model validity',
            'widths_um_by_metal_index': {key: sorted(value) for key, value in widths.items()},
            'empty_width_tables': empty, 'first_resover_grid_by_metal_index': res}


def stringify(value):
    if isinstance(value, Decimal):
        return str(value)
    if isinstance(value, dict):
        return {key: stringify(item) for key, item in value.items()}
    if isinstance(value, (list, tuple)):
        return [stringify(item) for item in value]
    return value


def compare(base):
    intake, files = checked_intake(base)
    def read_verified(pr, path):
        row = files[pr, path]
        data = Path(row['local_path']).read_bytes()
        require(sha256(data) == row['sha256'] and len(data) == row['bytes'], 'Source changed during comparison')
        return data.decode('utf-8')
    def stack(pr, path):
        return parse_stack(read_verified(pr, path))
    typ = itf_metal_geometry(stack(1251, ITF_DIR + 'sg13cmos5l_typ.itf'))
    corners = {}
    with localcontext() as context:
        context.prec = 50
        for corner in ('TYP', 'MIN', 'MAX'):
            itf = stack(1251, ITF_DIR + 'sg13cmos5l_' + corner.lower() + '.itf')
            process = stack(1237, PROCESS_DIR + 'sg13cmos5l.' + corner + '.process')
            rows = compare_corner(itf, process, corner, typ)
            rules = inventory_rules(read_verified(1237, PROCESS_DIR + 'sg13cmos5l.' + corner + '.rules'), corner)
            for index, row in enumerate(rows, 1):
                grid = rules['first_resover_grid_by_metal_index'][str(index)]
                ref = row['merged_itf']
                expected = ref['sheet_resistance_ohm'] / grid['width_um'] / 1000
                grid['merged_itf_sheet_R_over_drawn_width_ohm_per_nm'] = expected
                grid['difference_ohm_per_nm'] = grid['resistance_ohm_per_nm'] - expected
            corners[corner] = {'metals': rows, 'rules_inventory': rules,
                              'itf_dielectric_ER': {name: fields['ER'] for (kind, name), fields in itf.items() if kind == 'DIELECTRIC'},
                              'process_dielectric_epsilon': {name: fields['epsilon'] for (kind, name), fields in process.items() if kind == 'DIELECTRIC'}}
        lower = stack(1237, PROCESS_DIR + 'sg13cmos5l.TYP.process')
        lower_gap = [fields for (kind, _), fields in lower.items() if kind == 'DIELECTRIC' and fields.get('next_met') == 1]
        series_epsilon = sum(fields['thickness'] for fields in lower_gap) / sum(fields['thickness'] / fields['epsilon'] for fields in lower_gap)
        result = {'schema': 'pinwheel.rc-independent-stack-comparison.v1', 'qualified': False,
                  'physical_acceptance': False, 'native_executed': False, 'downloaded_code_executed': False,
                  'host_arithmetic_and_provenance_checked': True, 'decimal_division_precision_digits': 50,
                  'intakes': intake, 'verified_source_files': list(files.values()),
                  'geometry_reference': 'Draft silicon surface: fox + nitride + dummyOx below M1; oxN includes lower metal. Poly/active/trench not stacked into metal height.',
                  'corners': corners, 'typ_M1_gap_series_epsilon_1D': series_epsilon,
                  'typ_TopMetal1_bottom_um': typ['TopMetal1']['bottom_um'],
                  'qualification': {'process_stack_description_compared': True, 'field_solver_calibrated': False,
                                    'model_corner_envelope_validated': False, 'extractor_consumer_validated': False,
                                    'full_model_syntax_validated': False, 'draft_rule_generation_provenance_available': False},
                  'note': 'Arithmetic agreement under the stated convention does not qualify extraction tables; corner strategies differ and generator numerical acceptance remains unvalidated.'}
    return stringify(result)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True, help='New, absent report JSON path')
    args = parser.parse_args()
    source = Path(__file__).resolve()
    source_digest = sha256(source.read_bytes())
    head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip()
    committed_source = subprocess.check_output(['git', 'show', head + ':scripts/streaming_tt_rc_compare.py'])
    require(sha256(committed_source) == source_digest, 'Comparison producer must be committed before receipt creation')
    require(not args.output.exists(), 'Refusing to replace an existing report')
    result = compare(args.input)
    result['producer_sha256'] = source_digest
    result['source_commit'] = head
    result['created_utc'] = datetime.now(timezone.utc).isoformat()
    require(sha256(source.read_bytes()) == source_digest, 'Producer changed during review')
    require(subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip() == head, 'HEAD changed during review')
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open('x') as handle:
        json.dump(result, handle, indent=2, sort_keys=True, allow_nan=False)
        handle.write('\n')
    print(json.dumps({'report': str(args.output), 'sha256': sha256(args.output.read_bytes()), 'qualified': False}))


if __name__ == '__main__':
    main()
