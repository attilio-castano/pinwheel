"""Narrow dimensional adapter for the supplied 32-bit tile; original is refused."""
from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
TOP = 'RM_IHPSG13_1P_BITKIT_16x2_SRAM'
CELL = 'RM_IHPSG13_512x64_c2_1P_BITKIT_CELL'
MAPPING = {
    'R1': ('BLC_BOT', 'BLC_TOP', 'res_metal2', '10/29'),
    'R0': ('BLT_BOT', 'BLT_TOP', 'res_metal2', '10/29'),
    'R2': ('RWL', 'LWL', 'res_metal3', '30/29'),
}

def require(ok, message):
    if not ok:
        raise RuntimeError(message)

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def validate_geometry(geometry):
    for layer, count in [('10/29', 2), ('30/29', 1)]:
        rows = geometry['markers'][layer]
        require(len(rows) == count and all(r['rectangular'] and r['fully_on_conductor']
                and r['width_um'] == 0.2 and r['length_um'] == 0.6 for r in rows),
                'Unsupported physical marker geometry')
    for a, b, model, layer in MAPPING.values():
        rows = [d for d in geometry['native_resistors'] if d['model'] == model
                and {n['name'] for n in d['terminals'].values()} == {a, b}]
        require(len(rows) == 1 and rows[0]['parameters']['W'] == 0.2
                and rows[0]['parameters']['L'] == 0.6, 'Ambiguous physical resistor correspondence')

def translate(text, geometry):
    validate_geometry(geometry)
    matches = list(re.finditer(r'^\.SUBCKT ' + re.escape(CELL) + r'\b.*?^\.ENDS[^\n]*', text, re.M | re.S))
    require(len(matches) == 1, 'Missing or duplicate bit-cell source')
    match = matches[0]
    block = match[0]
    lines = [line for line in block.splitlines() if line.startswith('R')]
    require(len(lines) == 3 and {line.split()[0] for line in lines} == set(MAPPING),
            'Unknown resistor inventory')
    for line in lines:
        tokens = line.split()
        a, b, model, layer = MAPPING[tokens[0]]
        require(tokens[1:4] == [a, b, 'lvsres'] and len(tokens) == 6,
                'Unknown resistor nodes/model/parameters')
        dims = dict(token.split('=') for token in tokens[4:])
        require(set(dims) == {'w', 'l'}, 'Missing or duplicate dimension')
        require(abs(float(dims['w']) * 1e6 - 0.2) < 1e-12
                and abs(float(dims['l']) * 1e6 - 0.6) < 1e-12,
                'SOURCE_GEOMETRY_DIMENSION_MISMATCH: ' + tokens[0])
        block = block.replace(line, line.replace(' lvsres ', ' ' + model + ' '))
    return text[:match.start()] + block + text[match.end():]

def prepare_counterfactual():
    """Return a diagnostic copy. Never admit the original or change its file."""
    identities = json.loads((HERE / 'inputs.json').read_text())
    for name, digest in identities['files_sha256'].items():
        require(sha(HERE / name) == digest, 'Changed pinned fixture: ' + name)
    geometry = json.loads((HERE / 'geometry.json').read_text())
    source = (HERE / (TOP + '.cdl')).read_text()
    try:
        translate(source, geometry)
    except RuntimeError as exc:
        require('SOURCE_GEOMETRY_DIMENSION_MISMATCH' in str(exc), 'Unexpected source refusal')
        refusal = str(exc)
    else:
        raise RuntimeError('Supplied dimension disagreement silently admitted')
    require(source.count('w=2.6e-07') == 3, 'Unexpected counterfactual target')
    counterfactual = source.replace('w=2.6e-07', 'w=2e-07')
    adapted = translate(counterfactual, geometry)
    require(hashlib.sha256(adapted.encode()).hexdigest() == identities['counterfactual_cdl_sha256'],
            'Changed diagnostic interpretation')
    return adapted, {'source_admission': False, 'source_refusal': refusal,
                     'supplied_tile_qualification': False, 'counterfactual_only': True,
                     'width_tokens_changed': 3, 'expanded_resistors_affected': 96}

if __name__ == '__main__':
    _, result = prepare_counterfactual()
    print(json.dumps(result, indent=2))
