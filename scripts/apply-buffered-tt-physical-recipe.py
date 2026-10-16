#!/usr/bin/env python3
"""Apply a SHA-bound physical-only recipe to an unused prepared TT candidate.

This changes only explicitly admitted optimization knobs. It preserves the
RTL, constraints, pin template, macro views, PDN and historical preparation
helpers, retains the original configuration/intake, and launches no CAD.
"""
import argparse
from copy import deepcopy
import hashlib
import json
import math
from pathlib import Path
import re
import signal
import tempfile

import buffered_tt_physical as physical


ROOT = physical.ROOT
SOURCE = Path(__file__).resolve()
ALLOWLIST = {
    'PL_TIMING_DRIVEN': 'true',
    'PL_KEEP_RESIZE_BELOW_OVERFLOW': 'zero',
    'DESIGN_REPAIR_BUFFER_OUTPUT_PORTS': 'true',
    'PL_RESIZER_SETUP_SLACK_MARGIN': 'margin',
    'GRT_RESIZER_SETUP_SLACK_MARGIN': 'margin',
    'PL_RESIZER_SETUP_REPAIR_TNS_PCT': 'hundred',
    'GRT_RESIZER_SETUP_REPAIR_TNS_PCT': 'hundred',
    'PL_RESIZER_FIX_HOLD_FIRST': 'true',
    'SYNTH_STRATEGY': 'delay',
    'PL_TARGET_DENSITY_PCT': 'density',
    'meta': 'capacity_flow',
}
BASE_META = {'flow': 'Classic', 'substituting_steps': {
    '+OpenROAD.GeneratePDN': 'Project.BufferedSramPower'}}
CAPACITY_META = {'flow': 'Classic', 'substituting_steps': {
    '+OpenROAD.GeneratePDN': 'Project.BufferedSramPower',
    'OpenROAD.GlobalPlacement': 'Project.BufferedCapacityPlacement'}}
CAPACITY_TCL = 'physical/buffered_tt/gpl_capacity.tcl'
DEFAULT_MARGINS = {'PL_RESIZER_SETUP_SLACK_MARGIN': 0.05,
                   'GRT_RESIZER_SETUP_SLACK_MARGIN': 0.025}
SNAPSHOTS = ('pre-recipe-inputs.json', 'pre-recipe-core.json',
             'physical-recipe-request.json', 'physical-recipe-receipt.json')
REQUIRED_FILES = {'core.json', 'core.sdc', 'design.sv', 'pdn.tcl',
                  'tt_block_6x4_pgvdd.def', 'macro-geometry.json',
                  'power-columns.json', 'connect_sram_power.py',
                  'librelane_plugin_buffered_tt.py'} | {
    'macro/' + physical.MASTER + suffix for suffix in
    ('.bb.v', '.cdl', '.gds', '.lef', '.v', '_typ_1p20V_25C.lib',
     '_slow_1p08V_125C.lib', '_fast_1p32V_m55C.lib')}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def encode(value):
    return (json.dumps(value, indent=2, allow_nan=False) + '\n').encode()


def checked_ref(ref):
    require(isinstance(ref, dict) and set(ref) == {'path', 'sha256'},
            'Evidence references require exactly path and sha256')
    name, expected = ref['path'], ref['sha256']
    require(isinstance(name, str) and name and not Path(name).is_absolute()
            and '..' not in Path(name).parts,
            'Evidence must name a repository-relative file')
    require(isinstance(expected, str) and re.fullmatch('[0-9a-f]{64}', expected),
            'Evidence requires a SHA256 digest')
    path = (ROOT / name).resolve()
    require(path.is_relative_to(ROOT.resolve()) and path.is_file(),
            'Evidence file is outside the repository or missing')
    require(physical.sha(path) == expected, 'Changed recipe evidence: ' + name)
    return path, expected


def updated_config(before, knobs):
    require(isinstance(knobs, dict) and knobs, 'A nonempty physical knob map is required')
    require(not (set(knobs) - set(ALLOWLIST)),
            'Forbidden physical knob: ' + ', '.join(sorted(set(knobs) - set(ALLOWLIST))))
    after = deepcopy(before)
    for name, value in knobs.items():
        kind = ALLOWLIST[name]
        numeric = type(value) in (int, float) and math.isfinite(value)
        if kind == 'true':
            require(value is True, name + ' admits only true')
        elif kind == 'zero':
            require(numeric and value == 0, name + ' admits only numeric zero')
        elif kind == 'hundred':
            require(numeric and value == 100, name + ' admits only numeric 100')
        elif kind == 'delay':
            require(value == 'DELAY 1', name + ' admits only DELAY 1')
        elif kind == 'density':
            require(numeric and value == 55, name + ' admits only numeric 55')
        elif kind == 'capacity_flow':
            require(value == CAPACITY_META, 'Only the exact capacity placement flow is admitted')
        elif kind == 'margin':
            prior = before.get(name, DEFAULT_MARGINS[name])
            require(type(prior) in (int, float) and math.isfinite(prior),
                    'Invalid previous setup margin: ' + name)
            require(numeric and max(prior, DEFAULT_MARGINS[name]) <= value <= 2,
                    name + ' must preserve prior headroom and be at most 2 ns')
        after[name] = value
    protected = lambda config: {k: v for k, v in config.items() if k not in ALLOWLIST}
    require(protected(before) == protected(after), 'Protected physical configuration changed')
    require(before != after, 'Recipe makes no physical configuration change')
    physical.validate_flow_config(after)
    return after


def require_unused(design):
    def occupied(path):
        return path.exists() or path.is_symlink()
    require(not occupied(design / 'runs'), 'Cannot apply a recipe after any run directory exists')
    require(not any(occupied(design / name) for name in (*SNAPSHOTS, 'gpl_capacity.tcl')),
            'Recipe was already applied or a receipt/profile path is occupied')


def atomic_replace(path, data):
    path = Path(path)
    temporary = None
    try:
        with tempfile.NamedTemporaryFile(prefix='.physical-recipe-', suffix='.tmp',
                                         dir=path.parent, delete=False) as stream:
            temporary = Path(stream.name)
            stream.write(data)
            stream.flush()
        temporary.replace(path)
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)


def apply_recipe(design, recipe_path):
    design, recipe_path = Path(design).resolve(), Path(recipe_path).resolve()
    require(design.parent == (ROOT / 'build/physical').resolve(),
            'Recipe target must be one prepared build/physical directory')
    require(recipe_path.is_relative_to(ROOT.resolve()) and recipe_path.is_file(),
            'Recipe must be a saved repository file')
    require_unused(design)
    intake = physical.verify_prepared(design)
    require(intake.get('status') == 'ready' and not intake.get('missing_macro_views'),
            'Recipe requires a ready, complete prepared candidate')
    require('physical_recipe' not in intake, 'Recipe reapplication is forbidden')
    require(set(intake['files_sha256']) == REQUIRED_FILES,
            'Recipe requires the exact seventeen prepared input files')
    require(not any((design / name).is_symlink() for name in (*REQUIRED_FILES, 'inputs.json')),
            'Prepared files must be ordinary files, not symlinks')
    original_inputs = (design / 'inputs.json').read_bytes()
    original_config = (design / 'core.json').read_bytes()
    recipe_bytes = recipe_path.read_bytes()
    recipe = json.loads(recipe_bytes)
    require(isinstance(recipe, dict) and set(recipe) == {
        'schema', 'source_inputs_sha256', 'source_config_sha256',
        'physical_knobs', 'evidence', 'rationale'}, 'Unexpected physical recipe schema/fields')
    require(recipe['schema'] == 'pinwheel-buffered-tt-physical-recipe-v1',
            'Unexpected physical recipe schema')
    require(recipe['source_inputs_sha256'] == digest(original_inputs)
            and recipe['source_config_sha256'] == digest(original_config),
            'Recipe does not bind this original prepared intake/configuration')
    require(isinstance(recipe['rationale'], str) and recipe['rationale'].strip(),
            'A concrete recipe rationale is required')
    require(isinstance(recipe['evidence'], list) and recipe['evidence'],
            'At least one SHA-bound measurement is required')
    evidence = [checked_ref(ref) for ref in recipe['evidence']]
    require(len({path for path, _ in evidence}) == len(evidence), 'Duplicate recipe evidence')
    mutable_paths = {design / 'core.json', design / 'inputs.json'} | {design / n for n in SNAPSHOTS}
    require(recipe_path not in mutable_paths and all(path not in mutable_paths for path, _ in evidence),
            'Recipe/evidence cannot reference an input changed by this application')
    before = json.loads(original_config)
    require(isinstance(before, dict) and before.get('meta') == BASE_META,
            'Recipe requires the exact original power-only flow configuration')
    after = updated_config(before, recipe['physical_knobs'])
    new_config = encode(after)
    source = SOURCE.resolve()
    require(source.is_relative_to(ROOT.resolve()), 'Recipe helper must belong to this repository')
    sources = {str(source.relative_to(ROOT)): physical.sha(source),
               str(recipe_path.relative_to(ROOT)): digest(recipe_bytes),
               **{str(path.relative_to(ROOT)): expected for path, expected in evidence}}
    profile_payload = {}
    if after['meta'] == CAPACITY_META:
        profile_source = ROOT / CAPACITY_TCL
        require(profile_source.is_file() and not profile_source.is_symlink(),
                'Exact capacity placement source is unavailable')
        profile_payload['gpl_capacity.tcl'] = profile_source.read_bytes()
        sources[CAPACITY_TCL] = digest(profile_payload['gpl_capacity.tcl'])
    application = dict(schema='pinwheel-buffered-tt-physical-recipe-application-v1', status='applied',
                       original_inputs_sha256=digest(original_inputs),
                       original_config_sha256=digest(original_config),
                       updated_config_sha256=digest(new_config),
                       physical_knobs=recipe['physical_knobs'], rationale=recipe['rationale'],
                       evidence=recipe['evidence'], source_sha256=sources,
                       added_profile_files={name: digest(data) for name, data in profile_payload.items()},
                       unchanged_staged_files={name: sha for name, sha in intake['files_sha256'].items()
                                               if name != 'core.json'},
                       scope='Physical optimization settings only; unchanged RTL, timing constraints, '
                             'template, macro views and PDN. No CAD or acceptance claim.')
    payloads = dict(zip(SNAPSHOTS, (original_inputs, original_config, recipe_bytes, encode(application))))
    payloads.update(profile_payload)
    updated_intake = deepcopy(intake)
    for name, expected in sources.items():
        require(name not in updated_intake['source_sha256'] or updated_intake['source_sha256'][name] == expected,
                'Recipe source conflicts with inherited custody: ' + name)
        updated_intake['source_sha256'][name] = expected
    updated_intake['files_sha256'].update({name: digest(data) for name, data in payloads.items()})
    updated_intake['files_sha256']['core.json'] = digest(new_config)
    updated_intake['physical_recipe'] = dict(request='physical-recipe-request.json',
                                           request_sha256=digest(recipe_bytes),
                                           receipt='physical-recipe-receipt.json',
                                           receipt_sha256=digest(payloads['physical-recipe-receipt.json']))
    # Recheck every inherited and added source immediately before any mutation.
    physical.verify_prepared(design)
    require((design / 'inputs.json').read_bytes() == original_inputs,
            'Prepared intake changed during recipe validation')
    for name, expected in sources.items():
        require(physical.sha(ROOT / name) == expected, 'Recipe source changed before application: ' + name)
    require_unused(design)
    created = []
    try:
        for name, data in payloads.items():
            path = design / name
            with path.open('xb') as stream:
                created.append(path)
                stream.write(data)
        atomic_replace(design / 'core.json', new_config)
        atomic_replace(design / 'inputs.json', encode(updated_intake))
        physical.verify_prepared(design)
    except BaseException:
        atomic_replace(design / 'core.json', original_config)
        atomic_replace(design / 'inputs.json', original_inputs)
        for path in reversed(created):
            path.unlink(missing_ok=True)
        raise
    return application


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--design', required=True, type=Path)
    parser.add_argument('--recipe', required=True, type=Path)
    args = parser.parse_args()
    previous = signal.getsignal(signal.SIGTERM)

    def interrupt(signum, frame):
        signal.signal(signal.SIGTERM, signal.SIG_IGN)
        raise KeyboardInterrupt('signal ' + str(signum))

    signal.signal(signal.SIGTERM, interrupt)
    try:
        result = apply_recipe(args.design, args.recipe)
    finally:
        signal.signal(signal.SIGTERM, previous)
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
