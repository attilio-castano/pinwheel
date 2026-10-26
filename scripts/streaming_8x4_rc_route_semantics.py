"""Narrow HOST physical-invariance gate for the unchanged17-net R fixture.

Only a redundant NEW at the exact exit layer/junction of a named LEF via may
disappear. All physical events must match the selected fixture; every other
byte, including ports and NDR declarations, must remain identical. This is
neither a general DEF equivalence engine nor a numerical acceptance change.
"""
import hashlib
import json
from pathlib import Path
import re
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import streaming_8x4_rc_consumer_ndr as N
import streaming_8x4_rc_consumer_ndr_readback as R

SCHEMA = 'pinwheel.streaming-8x4-rc-consumer-route-invariance.v1'
SOURCE_SHA = 'b83762c171b157c8c0de868e9b171e9fc7247ba8873c6b0afd77484a8d042be3'
WRITER_SHA = 'a81f028054a03466ff67755b8bc203adb0ea97b89136efebb92f690ace7eae7d'
WRITER_BLOB = '277a7a3475e45679382a147b72d4161d89fd9bdf'
TECH_SHA = '3edd5a1ad31e8307be537d0d1b85c3258fefeb21aac04aaa476e4f72de4cffd5'
TOKEN = re.compile(r'\(\s*(-?\d+|\*)\s+(-?\d+|\*)\s*\)|\bNEW\s+([A-Za-z][A-Za-z0-9_]*)\b|([A-Za-z][A-Za-z0-9_]*)')


def need(value, message): N.need(value, message)


def digest(raw): return hashlib.sha256(raw).hexdigest()


def source_evidence(writer, reader):
    need(N.C.P.sha(writer / 'manifest.json') == SOURCE_SHA, 'Exact DEF writer intake changed')
    manifest = json.loads((writer / 'manifest.json').read_text())
    need(manifest == dict(schema='pinwheel.streaming-8x4-rc-route-source-intake.v1',
        openroad_commit=N.COMMIT, native_executed=False, files=[dict(name='defout_impl.cpp',
        repository_path='src/odb/src/defout/defout_impl.cpp', bytes=53139, sha256=WRITER_SHA,
        git_blob=WRITER_BLOB, url='https://api.github.com/repos/The-OpenROAD-Project/OpenROAD/contents/src/odb/src/defout/defout_impl.cpp?ref=' + N.COMMIT)]),
        'DEF writer source metadata changed')
    data = (writer / 'defout_impl.cpp').read_bytes()
    need(digest(data) == WRITER_SHA and hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest() == WRITER_BLOB
        and N.file_inventory(writer) == {'manifest.json': SOURCE_SHA, 'defout_impl.cpp': WRITER_SHA}, 'DEF writer source bytes/membership changed')
    return dict(writer=N.file_inventory(writer), reader=N.source_evidence(reader), openroad_commit=N.COMMIT)


def via_layers(tech):
    need(digest(tech.encode()) == TECH_SHA, 'Exact selected technology LEF changed')
    result = {}; types = {}
    for match in re.finditer(r'^LAYER\s+(\S+)\s*\n(.*?)^END\s+\1\s*$', tech, re.M | re.S):
        kinds = re.findall(r'^\s*TYPE\s+(\S+)\s*;', match[2], re.M)
        need(len(kinds) == 1 and match[1] not in types, 'Ambiguous technology layer type')
        types[match[1]] = kinds[0]
    for name in N.C.VIA_FIXTURES:
        matches = list(re.finditer(r'^\s*(?i:VIA)\s+' + re.escape(name) + r'(?:\s+DEFAULT)?\s*\n(.*?)^\s*END\s+' + re.escape(name) + r'\s*$', tech, re.M | re.S))
        need(len(matches) == 1, 'Missing/duplicate selected named LEF via')
        layers = re.findall(r'^\s*LAYER\s+(\S+)\s*;', matches[0][1], re.M)
        route = [x for x in layers if types.get(x) == 'ROUTING']; cut = {x for x in layers if types.get(x) == 'CUT'}
        need(len(set(layers)) == 3 and len(route) == 2 and len(cut) == 1
            and all(x in N.METALS for x in route) and N.METALS.index(route[1]) == N.METALS.index(route[0]) + 1,
            'Selected named via does not join exactly adjacent routing layers')
        result[name] = dict(bottom=route[0], top=route[1], cut_layer=next(iter(cut)))
    return result


def point(token, previous):
    values = token.group(1, 2)
    need(values[0] is not None and (previous is not None or '*' not in values), 'Missing initial/unsupported route point')
    return tuple(previous[i] if value == '*' else int(value) for i, value in enumerate(values))


def expected(rows):
    need(len(rows) == 17 and len({r['name'] for r in rows}) == 17, 'Exact17 fixture rows required')
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
    blocks = re.findall(r'^PINS 34 ;\n(.*?)^END PINS\s*$', text, re.M | re.S)
    need(len(blocks) == 1, 'Complete34 fixture ports required')
    pattern = re.compile(r'\s*- (\w+) \+ NET (\w+) \+ DIRECTION (INPUT|OUTPUT) \+ USE SIGNAL\s+\+ PORT\s+\+ LAYER (\w+) \( -50 -50 \) \( 50 50 \)\s+\+ FIXED \( (\d+) (\d+) \) N ;')
    matches = list(pattern.finditer(blocks[0])); cursor = 0; result = {}
    for match in matches:
        need(not blocks[0][cursor:match.start()].strip(), 'Unsupported fixture port syntax'); cursor = match.end()
        name, net, direction, layer, x, y = match.groups()
        need(name not in result, 'Duplicate fixture port'); result[name] = [net, direction, layer, int(x), int(y)]
    need(not blocks[0][cursor:].strip() and len(result) == 34, 'Missing/unsupported fixture port')
    target = {}
    for name, row in wanted.items():
        for suffix, direction, segment, end in [('A', 'INPUT', row['segments'][0], 'start'), ('B', 'OUTPUT', row['segments'][-1], 'end')]:
            target[name + '_' + suffix] = [name, direction, segment['layer'], *segment[end]]
    need(result == target, 'Actual fixture port layer/placement/connectivity changed')
    return result


def parse(text, tech, witness, rows):
    need(type(text) is str and text.isascii() and '\r' not in text, 'Only exact ASCII LF DEF is supported')
    defaults = N.default_widths(tech); layers = via_layers(tech); target = expected(rows)
    ndr = R.native_ndr(text, witness, rows); port_rows = ports(text, target)
    blocks = list(re.finditer(r'^NETS 17 ;\n(.*?)^END NETS\s*$', text, re.M | re.S))
    need(len(blocks) == 1, 'Complete17-net route section required')
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
    need(not body[cursor:].strip() and result == target, 'Missing/extra17-net physical route')
    canonical = text
    for row in reversed(removals): canonical = canonical[:row['start']] + canonical[row['end']:]
    return dict(routes=result, ports=port_rows, native_NDR=ndr, removed_NEW_clauses=removals), canonical


def compare(before, after, tech, witness, rows):
    left, canonical_before = parse(before, tech, witness, rows); right, canonical_after = parse(after, tech, witness, rows)
    need(all(left[k] == right[k] for k in ('routes', 'ports', 'native_NDR')), 'Complete physical route/port/NDR facts changed')
    need(canonical_before == canonical_after, 'Bytes outside proven redundant NEW clauses changed')
    return dict(schema=SCHEMA, passed=True, qualified=False, model_qualified=False,
        before_DEF_sha256=digest(before.encode()), after_DEF_sha256=digest(after.encode()),
        technology_LEF_sha256=digest(tech.encode()), byte_identical=before == after,
        all17_routes_checked=True, segment_count=sum(len(r['segments']) for r in left['routes'].values()),
        named_via_count=sum(len(r['vias']) for r in left['routes'].values()), all34_ports_checked=True,
        non_normalized_bytes_identical=True, canonical_DEF_sha256=digest(canonical_before.encode()),
        before=left, after=right, numerical_tolerances_unchanged=True,
        scope='Exact controlled17-net R fixture only; no DRC, whole-design, RC accuracy or model qualification claim.')
