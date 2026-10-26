"""Fixed26-net geometry and exact local LEF adapter for the new R study.

Copied route mathematics retain the reviewed via-exit-only normalization under
new scope/count authority. No old checker or evidence is changed.
"""
from decimal import Decimal as D
import re

import streaming_8x4_rc_route_semantics as S

N, R, need, digest, point, TOKEN = S.N, S.R, S.need, S.digest, S.point, S.TOKEN
SCHEMA = 'pinwheel.streaming-8x4-rc-R-length-width-route-invariance.v1'
ORIGINAL_R = dict(zip(N.METALS, ('0.135', '0.103', '0.103', '0.103', '0.021')))


def resistance_fields(text):
    result = {}
    for match in re.finditer(r'^LAYER\s+(\S+)\s*\n(.*?)^END\s+\1\s*$', text, re.M | re.S):
        if not re.search(r'^\s*TYPE\s+ROUTING\s*;', match[2], re.M): continue
        fields = list(re.finditer(r'^\s*RESISTANCE\s+RPERSQ\s+([0-9.eE+-]+)\s*;', match[2], re.M))
        need(len(fields) == 1 and match[1] not in result, 'Exactly one sheet-R field per routing layer required')
        field = fields[0]; value = D(field[1]); need(value.is_finite() and value > 0, 'Invalid sheet resistance')
        result[match[1]] = dict(value=field[1], start=match.start(2) + field.start(1), end=match.start(2) + field.end(1))
    need(tuple(result) == N.METALS, 'Complete exact five-layer sheet-R membership required')
    return result


def replace_values(text, values):
    fields = resistance_fields(text); need(set(values) == set(fields), 'Complete selected sheet-R values required')
    for name, row in reversed(list(fields.items())):
        value = str(values[name]); need(D(value).is_finite() and D(value) > 0, 'Nonpositive selected sheet resistance')
        text = text[:row['start']] + value + text[row['end']:]
    return text


def restore_original(tech):
    original = replace_values(tech, ORIGINAL_R)
    need(digest(original.encode()) == S.TECH_SHA, 'Non-routing-resistance technology bytes changed')
    return original


def local_lef(original, sheets):
    need(digest(original.encode()) == S.TECH_SHA, 'Exact original technology required')
    result = replace_values(original, sheets)
    need(restore_original(result) == original, 'Local candidate changed non-resistance LEF bytes')
    return result, dict(schema='pinwheel.streaming-8x4-rc-R-local-LEF-witness.v1',
        original_sha256=digest(original.encode()), local_sha256=digest(result.encode()),
        routing_sheet_R_ohm={n: str(sheets[n]) for n in N.METALS}, all_other_bytes_identical=True,
        explicit_via_and_cut_layer_resistances_unchanged=True, shared_PDK_modified=False)


def via_layers(tech): return S.via_layers(restore_original(tech))


def rows():
    result = []
    for layer, width in N.C.WIDTHS.items():
        for length in ('50', '100', '150'):
            result.append(dict(name=layer + '_L' + length, segments=[[layer, length, str(width)]], via=None))
    for layer, width in (('Metal1', '.32'), ('Metal2', '.40')):
        for length in ('50', '100', '150'):
            result.append(dict(name=layer + '_wide_L' + length, segments=[[layer, length, width]], via=None))
    for name in N.C.VIA_FIXTURES:
        pair = {'Via1_XX': ('Metal1', 'Metal2'), 'Via1_DC1B': ('Metal1', 'Metal2'),
                'Via2_XX': ('Metal2', 'Metal3'), 'Via3_XX': ('Metal3', 'Metal4'), 'TopVia1EWNS': ('Metal4', 'TopMetal1')}[name]
        result.append(dict(name=name, segments=[[m, '50', str(N.C.WIDTHS[m])] for m in pair], via=name))
    need(len(result) == 26 and len({r['name'] for r in result}) == 26, 'Fixed26-net universe differs')
    return result


def fixture(tech, widths):
    original = restore_original(tech); block, rules = N.declarations(original, widths)
    pins, nets = [], []
    for index, row in enumerate(rows()):
        x, y = 10000, (20 + index * 20) * 1000
        last = x + sum(int(D(s[1]) * 1000) for s in row['segments'])
        for suffix, direction, layer, px in [('A', 'INPUT', row['segments'][0][0], x), ('B', 'OUTPUT', row['segments'][-1][0], last)]:
            pins.append(f'- {row["name"]}_{suffix} + NET {row["name"]} + DIRECTION {direction} + USE SIGNAL\n'
                f' + PORT + LAYER {layer} ( -50 -50 ) ( 50 50 ) + FIXED ( {px} {y} ) N ;')
        ndr = ' + NONDEFAULTRULE WIDE_' + row['segments'][0][0] if '_wide_' in row['name'] else ''
        route = f' + ROUTED {row["segments"][0][0]} ( {x} {y} )'
        for i, (layer, length, _) in enumerate(row['segments']):
            x += int(D(length) * 1000); route += f' ( {x} {y} )'
            if i + 1 < len(row['segments']): route += f' {row["via"]}\n NEW {row["segments"][i+1][0]} ( {x} {y} )'
        nets.append(f'- {row["name"]} ( PIN {row["name"]}_B ) ( PIN {row["name"]}_A ) + USE SIGNAL{ndr}\n{route} ;')
    text = 'VERSION 5.8 ;\nDIVIDERCHAR "/" ;\nBUSBITCHARS "[]" ;\nDESIGN rc_R_length ;\nUNITS DISTANCE MICRONS 1000 ;\nDIEAREA ( 0 0 ) ( 200000 600000 ) ;\n' + block
    text += 'COMPONENTS 0 ;\nEND COMPONENTS\nPINS 52 ;\n' + '\n'.join(pins) + '\nEND PINS\nNETS 26 ;\n' + '\n'.join(nets) + '\nEND NETS\nEND DESIGN\n'
    return text, dict(rules=rules)


def headers(text):
    stripped = text
    for section, count in [('NONDEFAULTRULES', 2), ('PINS', 52), ('NETS', 26)]:
        pattern = r'^' + section + r'\s+' + str(count) + r'\s*;\n.*?^END\s+' + section + r'\s*$'
        matches = list(re.finditer(pattern, stripped, re.M | re.S)); need(len(matches) == 1, 'Missing/extra fixed section')
        stripped = stripped[:matches[0].start()] + stripped[matches[0].end():]
    target = 'VERSION 5.8 ; DIVIDERCHAR "/" ; BUSBITCHARS "[]" ; DESIGN rc_R_length ; UNITS DISTANCE MICRONS 1000 ; DIEAREA ( 0 0 ) ( 200000 600000 ) ; COMPONENTS 0 ; END COMPONENTS END DESIGN'
    need(stripped.split() == target.split(), 'Initial fixed header/diearea/component/extra-section authority differs')
    return dict(DBU_per_um=1000, design='rc_R_length', diearea_dbu=[0, 0, 200000, 600000], components=0)


def expected(rows):
    need(len(rows) == 26 and len({r['name'] for r in rows}) == 26, 'Exact26 fixture rows required')
    result = {}
    for index, row in enumerate(rows):
        x, y = 10000, (20 + index * 20) * 1000; segments = []; vias = []
        for i, (layer, length, width) in enumerate(row['segments']):
            size = N.U.Fraction(length) * 1000; w = N.U.Fraction(width) * 1000
            need(size.denominator == w.denominator == 1 and size > 0 and w > 0, 'Nonintegral selected physical fixture')
            end = x + int(size); segments.append(dict(layer=layer, start=[x, y], end=[end, y], width_dbu=int(w)))
            x = end
            if i + 1 < len(row['segments']):
                vias.append(dict(name=row['via'], point=[x, y], entry_layer=layer, exit_layer=row['segments'][i + 1][0]))
        need(len(vias) == (1 if row['via'] else 0), 'Unsupported selected fixture topology')
        result[row['name']] = dict(segments=segments, vias=vias,
            NDR='WIDE_' + row['segments'][0][0] if '_wide_' in row['name'] else None)
    return result


def ports(text, wanted):
    blocks = re.findall(r'^PINS 52 ;\n(.*?)^END PINS\s*$', text, re.M | re.S)
    need(len(blocks) == 1, 'Complete52 fixture ports required')
    pattern = re.compile(r'\s*- (\w+) \+ NET (\w+) \+ DIRECTION (INPUT|OUTPUT) \+ USE SIGNAL\s+\+ PORT\s+\+ LAYER (\w+) \( -50 -50 \) \( 50 50 \)\s+\+ FIXED \( (\d+) (\d+) \) N ;')
    matches = list(pattern.finditer(blocks[0])); cursor = 0; result = {}
    for match in matches:
        need(not blocks[0][cursor:match.start()].strip(), 'Unsupported fixture port syntax'); cursor = match.end()
        name, net, direction, layer, x, y = match.groups()
        need(name not in result, 'Duplicate fixture port'); result[name] = [net, direction, layer, int(x), int(y)]
    need(not blocks[0][cursor:].strip() and len(result) == 52, 'Missing/unsupported fixture port')
    target = {}
    for name, row in wanted.items():
        for suffix, direction, segment, end in [('A', 'INPUT', row['segments'][0], 'start'), ('B', 'OUTPUT', row['segments'][-1], 'end')]:
            target[name + '_' + suffix] = [name, direction, segment['layer'], *segment[end]]
    need(result == target, 'Actual fixture port layer/placement/connectivity changed')
    return result


def parse(text, tech, witness, rows):
    need(type(text) is str and text.isascii() and '\r' not in text, 'Only exact ASCII LF DEF is supported')
    defaults = N.default_widths(tech); layers = via_layers(tech); target = expected(rows)
    need(rows == globals()['rows'](), 'Exact declared26-net fixture required'); header = headers(text)
    rules = R.definitions(text); need(rules == witness['rules'], 'Actual local NDR definitions differ')
    ndr = dict(block_local_rules=rules); port_rows = ports(text, target)
    blocks = list(re.finditer(r'^NETS 26 ;\n(.*?)^END NETS\s*$', text, re.M | re.S))
    need(len(blocks) == 1, 'Complete26-net route section required')
    body = blocks[0][1]; offset = blocks[0].start(1); cursor = 0; result = {}; removals = []
    entries = list(re.finditer(r'\s*- (\w+) \( PIN (\w+) \) \( PIN (\w+) \) \+ USE SIGNAL(?: \+ NONDEFAULTRULE (\w+))?\s+\+ ROUTED (\w+) (.*?);', body, re.S))
    for entry in entries:
        need(not body[cursor:entry.start()].strip(), 'Unsupported/extra fixture net syntax'); cursor = entry.end()
        name, b, a, rule, layer, route = entry.groups()
        need(name in target and name not in result and (b, a) == (name + '_B', name + '_A') and layer in defaults
            and rule == target[name]['NDR'], 'Fixture net/port/NDR membership changed')
        tokens = list(TOKEN.finditer(route)); end = 0; current = None; segments = []; vias = []; last_via = None; index = 0
        while index < len(tokens):
            token = tokens[index]; need(not route[end:token.start()].strip(), 'Unsupported route token/attribute'); end = token.end()
            if token[1] is not None:
                value = point(token, current)
                if current is not None:
                    need(value[1] == current[1] and value[0] > current[0], 'Nonpositive/nonhorizontal/reversed fixture segment')
                    width = ndr['block_local_rules'][rule][layer]['width_dbu'] if rule else defaults[layer]
                    segments.append(dict(layer=layer, start=list(current), end=list(value), width_dbu=width))
                current = value; last_via = None
            elif token[3] is not None:
                need(last_via is not None and token[3] == layer and index + 2 < len(tokens), 'Only redundant NEW after selected named via is allowed')
                first = tokens[index + 1]
                need(not route[end:first.start()].strip() and first[1] is not None and '*' not in first.group(1, 2)
                    and point(first, None) == current and tokens[index + 2][1] is not None,
                    'NEW exit layer/junction or following segment changed')
                start = offset + entry.start(6) + last_via.end(); stop = offset + entry.start(6) + first.end()
                removals.append(dict(net=name, exit_layer=layer, junction=list(current), start=start, end=stop,
                    removed_sha256=digest(text[start:stop].encode())))
                end = first.end(); index += 1; last_via = None
            else:
                via = token[4]
                need(current is not None and via in layers and last_via is None and not vias, 'Unsupported/multiple/missing-point via')
                pair = layers[via]; need(layer in (pair['bottom'], pair['top']), 'Named via does not touch current route layer')
                exit_layer = pair['top'] if layer == pair['bottom'] else pair['bottom']
                vias.append(dict(name=via, point=list(current), entry_layer=layer, exit_layer=exit_layer)); layer = exit_layer; last_via = token
            index += 1
        need(not route[end:].strip() and current is not None and last_via is None, 'Incomplete/unsupported route suffix')
        row = dict(segments=segments, vias=vias, NDR=rule)
        need(row == target[name], 'Actual segment/layer/effective-width/via/junction differs from selected physical fixture')
        result[name] = row
    need(not body[cursor:].strip() and result == target, 'Missing/extra26-net physical route')
    canonical = text
    for row in reversed(removals): canonical = canonical[:row['start']] + canonical[row['end']:]
    return dict(routes=result, ports=port_rows, headers=header, native_NDR=ndr, removed_NEW_clauses=removals), canonical


def compare(before, after, tech, witness, rows):
    left, canonical_before = parse(before, tech, witness, rows); right, canonical_after = parse(after, tech, witness, rows)
    need(all(left[k] == right[k] for k in ('routes', 'ports', 'headers', 'native_NDR')), 'Complete physical route/port/NDR facts changed')
    need(canonical_before == canonical_after, 'Bytes outside proven redundant NEW clauses changed')
    return dict(schema=SCHEMA, passed=True, qualified=False, model_qualified=False,
        before_DEF_sha256=digest(before.encode()), after_DEF_sha256=digest(after.encode()),
        technology_LEF_sha256=digest(tech.encode()), byte_identical=before == after,
        all26_routes_checked=True, segment_count=sum(len(r['segments']) for r in left['routes'].values()),
        named_via_count=sum(len(r['vias']) for r in left['routes'].values()), all52_ports_checked=True,
        non_normalized_bytes_identical=True, canonical_DEF_sha256=digest(canonical_before.encode()),
        before=left, after=right, numerical_tolerances_unchanged=True,
        scope='Exact controlled26-net R fixture only; no DRC, whole-design, RC accuracy or model qualification claim.')
