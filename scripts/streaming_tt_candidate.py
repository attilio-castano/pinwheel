"""Separate optimized whole-device intake for bounded physical measurement.

Parent admission, kernel replay and physical acceptance are distinct. The
coarse producer accepts a pending final replay only under explicit parent
admission; detailed routing is not admitted by this module.
"""
from dataclasses import asdict
import hashlib
import json
from pathlib import Path
import shutil
import shlex
import subprocess

import streaming_clean_source as clean_source

from streaming_mapped_cost import measure
from streaming_mapped_flow import state_inventory
from streaming_mapped_liberty import LIBRARY_SHA256, load_library
from streaming_mapped_netlist import load_mapped
from streaming_tt_physical import ROOT, BASE, ARCHIVE, read, regular, require, sha, write, verify_files, committed

TOP = 'tt_um_pinwheel_streaming_ready_d2'
PACKAGE = 'pinwheel_streaming_ready_quad_d2'
CHECKED = frozenset(('fresh_raw_source_gate','archive_membership','worker_kernel_join',
    'private_axiom_audit','tool_identity','input_closeout','semantic_ff_bijection',
    'independent_proof_source_regeneration','physical_sv_reimport'))
RECIPE_BASELINE = 'd7a5c0d9112d6b442f4447c643a4c2d57b9c986b'
RECIPE_CHANGES = dict(CTS_SINK_CLUSTERING_SIZE=8,CTS_APPLY_NDR='none',RUN_POST_GRT_DESIGN_REPAIR=True,
    RUN_POST_GRT_RESIZER_TIMING=False,GRT_RESIZER_HOLD_SLACK_MARGIN=0.02)
CTS_TRIAL_BASELINE = '71decd66e04c0aadcc2ae4447c59013b22ac3ece'
CTS_TRIAL_BASELINE_SHA256 = '5407fb171ab040ce83e50cb867a5215de6080638f4595b3575e0932c0a659513'


def bound(entry):
    require(type(entry) is dict and set(entry) >= {'path','sha256'}, 'Missing hash-bound intake artifact')
    path = regular(Path(entry['path']).absolute()).resolve()
    require(sha(path) == entry['sha256'], 'Optimized intake artifact changed: ' + str(path))
    return path


def actual_semantic_q_map(candidate, graph, inventories, library):
    """Names propose matches; every actual Q/D/clock and total coverage checks."""
    top = candidate['modules'][TOP]
    engines = [(name,cell) for name,cell in top['cells'].items() if cell['type'] == PACKAGE]
    require(len(engines) == 1, 'Expected one actual engine package')
    engine = engines[0][0]
    package = candidate['modules'][PACKAGE]; actual = {ff.name:ff for ff in graph.flipflops}; rows=[]
    for label, child in [('frontend','frontend'),('core-d2','core')]:
        require(child in package['cells'], 'Missing actual component instance')
        module = candidate['modules'][package['cells'][child]['type']]
        for value in inventories[label]['registers']:
            local = json.loads(value['mapped_cell'])
            require(type(local) is list and len(local) == 1 and type(local[0]) is str and
                type(value['index']) is int and value['index'] >= 0 and value['register'] in module['netnames'] and
                value['index'] < len(module['netnames'][value['register']]['bits']) and
                module['netnames'][value['register']]['bits'][value['index']] == value['mapped_q'],
                'Component semantic label does not bind its actual Q')
            cell = module['cells'][local[0]]
            require(cell['type'] in library.cells and library.cells[cell['type']].sequential and
                cell['connections']['Q'] == [value['mapped_q']] and cell['connections']['D'] == [value['mapped_d']],
                'Component semantic FF Q/D wiring differs')
            name = json.dumps([engine,child,*local],separators=(',',':'))
            require(name in actual, 'Actual whole candidate lost a declared FF')
            ff = actual[name]
            rows.append(dict(component=label,register=value['register'],index=value['index'],
                source_q=value['source_q'],component_q=value['mapped_q'],component_d=value['mapped_d'],
                component_ff=value['mapped_cell'],candidate_ff=name,candidate_q=ff.q,candidate_d=ff.d,
                candidate_clock=ff.clock,candidate_cell=ff.cell))
    require(len(rows) == 6039 and len({(r['component'],r['register'],r['index']) for r in rows}) == 6039 and
        {r['candidate_q'] for r in rows} == graph.state_bits and len({r['candidate_q'] for r in rows}) == 6039 and
        {r['candidate_ff'] for r in rows} == set(actual), 'Semantic FF map is not an exact6039-bit bijection')
    canonical = json.dumps(candidate,sort_keys=True,separators=(',',':'))+'\n'
    return dict(schema='pinwheel.streaming-tt-semantic-q-map.v1',top=TOP,physical_ff_bits=6039,
        candidate_sha256=hashlib.sha256(canonical.encode()).hexdigest(),rows=rows)


def optimized_candidate(admission_path, admission_sha256):
    admission_path = regular(Path(admission_path).absolute()).resolve()
    require(sha(admission_path) == admission_sha256, 'Parent physical admission differs before use')
    admission = read(admission_path)
    require(admission.get('schema') == 'pinwheel.streaming-tt-optimized-intake.v1' and
        admission.get('passed') is True and admission.get('purpose') == 'bounded_physical_measurement' and admission.get('qualified') is False and
        admission.get('physical_acceptance_claim') is False and type(admission.get('checked')) is dict and
        CHECKED <= admission['checked'].keys() and all(admission['checked'][key] is True for key in CHECKED),
        'Parent has not admitted the source-bound optimized candidate')
    require(admission['source_commit'] == admission['producer_commit'] and
        type(admission['source_commit']) is str and len(admission['source_commit']) == 40,
        'Optimized source/producer identity mismatch')
    worker_path = bound(admission['worker_report']); raw_path = bound(admission['raw_gate_report'])
    config_path = bound(admission['worker_config']); worker_config = read(config_path)
    worker, raw = read(worker_path), read(raw_path)
    source_identity = admission.get('source_admission')
    if source_identity is not None:
        require(source_identity.get('mode') == 'clean-v1', 'Unknown parent source admission mode')
        require(clean_source.admit(ROOT, admission['source_commit'], raw['source_sha256']) == source_identity,
            'Clean parent source admission does not rederive')
    require(worker.get('schema') == 'pinwheel.streaming-tt-optimized-device.v1' and worker.get('passed') is True and
        worker.get('qualified') is False and worker.get('stage') == 'complete' and
        worker.get('all_state_device_kernel_join') is True and worker.get('physical_ff_bits') == 6039 and
        worker.get('source_commit') == worker.get('producer_commit') == admission['source_commit'] and
        not worker.get('error'), 'Optimized device kernel join is incomplete')
    require(raw.get('schema') == 'pinwheel.streaming-uart-continuation.v1' and raw.get('stage') == 'components' and
        raw.get('passed') is True and raw.get('full_qualification') is False and
        raw.get('source_commit') == raw.get('producer_commit') == admission['source_commit'] and
        raw.get('committed_archive_membership_verified_before') is True and
        raw.get('committed_archive_membership_verified_after') is True and not raw.get('error') and
        not raw.get('closeout_error'), 'Fresh raw component gate is not accepted')
    replay = admission.get('frozen_lean_replay')
    require(type(replay) is dict and replay.get('status') in ('pending','passed'), 'Unknown final Lean replay status')
    replay_path = bound(replay) if replay['status'] == 'passed' else None
    artifacts = {key:bound(admission['artifacts'][key]) for key in ('candidate_json','candidate_sv','semantic_q_map','cost')}
    root = worker_path.parent.resolve()
    for path in artifacts.values():
        require(path.resolve().is_relative_to(root) and worker['artifact_sha256'].get(str(path)) == sha(path),
            'Candidate artifact is not in the accepted worker inventory')
    consumed = {}
    for key in ('input_sha256','artifact_sha256'):
        require(type(worker.get(key)) is dict and worker[key], 'Missing optimized consumed/artifact map')
        for name, expected in worker[key].items():
            path = regular(Path(name)); require(sha(path) == expected, 'Optimized consumed file changed: ' + name)
            require(name not in consumed or consumed[name] == expected, 'Conflicting optimized input binding')
            consumed[name] = expected
    commands = worker.get('commands')
    require(type(commands) is list and commands and all(c.get('status') == 'completed' and c.get('exit_code') == 0 and
        sha(regular(c['log'])) == c.get('log_sha256') for c in commands), 'Optimized native proof journal is incomplete')
    for name, expected in raw['source_sha256'].items():
        if name.startswith(('Pinwheel/','scripts/streaming_mapped_','scripts/streaming_ready_')) or name in (
                'scripts/backend_readback.py','lean-toolchain','tools/hardware-toolchain.json'):
            require(sha(regular(ROOT/name)) == expected, 'Current source differs from the certified logical model: ' + name)
    library_paths = [Path(path) for path,value in consumed.items() if value == LIBRARY_SHA256]
    require(library_paths, 'No exact pinned candidate Liberty input')
    library = regular(library_paths[0]); lib = load_library(library)
    candidate = read(artifacts['candidate_json']); graph = load_mapped(artifacts['candidate_json'],TOP,lib)
    inventories = {}; component_sources = {}
    for label, top in [('frontend','pinwheel_streaming_quad_frontend'),('core-d2','pinwheel_streaming_ready_core_d2')]:
        data = worker['components'][label]; mapping = read(regular(data['mapping_report']))
        # Only mapping-consumed raw inputs may propose the source inventory.
        candidates = [Path(path) for path in mapping['input_sha256'] if Path(path).suffix == '.json' and
            top in read(path).get('modules',{})]
        require(len(candidates) == 1, 'Ambiguous frozen raw component source')
        source = regular(candidates[0])
        component_sources[label] = str(source)
        mapped = regular(data['mapped_json'])
        inventories[label] = state_inventory(read(source),read(mapped),top,lib)
        retained = read(regular(mapped.parent/'state-inventory.json'))
        require(inventories[label] == retained, 'Component semantic state inventory changed')
    qmap = actual_semantic_q_map(candidate,graph,inventories,lib)
    require(qmap == read(artifacts['semantic_q_map']), 'Whole candidate semantic Q/D map differs')
    cost = measure(artifacts['candidate_json'],TOP,library,6039,complete=True)
    require(cost == read(artifacts['cost']) == worker['cost'], 'Complete candidate cost does not reproduce')
    require(sha(admission_path) == admission_sha256 and sha(worker_path) == admission['worker_report']['sha256'] and
        sha(raw_path) == admission['raw_gate_report']['sha256'], 'Candidate admission changed during intake')
    yosys = regular(worker_config['tools']['yosys'])
    require(consumed.get(str(yosys)) == sha(yosys), 'Pinned reimport tool is not a closed worker input')
    consumed[str(config_path)] = sha(config_path)
    if source_identity is not None:
        for name, expected in source_identity['input_sha256'].items():
            require(name not in consumed or consumed[name] == expected, 'Conflicting clean source input')
            consumed[name] = expected
    result = dict(kind='optimized_whole_device',admission=str(admission_path),admission_sha256=admission_sha256,
        source_commit=admission['source_commit'],worker_report=str(worker_path),worker_report_sha256=sha(worker_path),
        raw_gate_report=str(raw_path),raw_gate_report_sha256=sha(raw_path),consumed_sha256=consumed,
        replay_status=replay['status'],replay=str(replay_path) if replay_path else None,
        top=TOP,netlist=str(artifacts['candidate_json']),netlist_sha256=sha(artifacts['candidate_json']),
        verilog=str(artifacts['candidate_sv']),verilog_sha256=sha(artifacts['candidate_sv']),
        library=str(library),liberty_sha256=LIBRARY_SHA256,source_ff_bits=6039,
        source_cell_count=len(graph.gates)+len(graph.flipflops),source_state=[asdict(ff) for ff in graph.flipflops],
        inputs=graph.inputs,outputs=graph.outputs,cost=cost,semantic_q_map=qmap,
        yosys=str(yosys),component_sources=component_sources,component_tops=dict(
            frontend='pinwheel_streaming_quad_frontend',**{'core-d2':'pinwheel_streaming_ready_core_d2'}),
        parent_admitted_scope='through_global_route_only',post_pnr_equivalence_proved=False)
    if source_identity is not None:
        result.update(source_mode='clean-v1', source_admission=source_identity)
    return result


def validate_config(config, tech_lef):
    from streaming_tt_physical import FORBIDDEN_CONFIG
    from streaming_tt_rc import validate_nominal_rc
    require(config == read(ROOT/'physical/streaming-tt-candidate.json') and
        config['DESIGN_NAME'] == TOP and not FORBIDDEN_CONFIG.intersection(config),
        'Optimized physical recipe differs from the committed standard-cell target')
    return validate_nominal_rc(config,tech_lef)


def recipe_experiment(config, *, source_mode='historical', producer_sha256=None):
    """Retain the coarse03 ledger and isolate the fresh CTS8 trial delta."""
    require(source_mode in ('historical','clean-v1'), 'Unknown recipe source mode')
    baseline = (clean_source.recipe_bytes('recipe', ROOT, producer_sha256) if source_mode == 'clean-v1' else
        subprocess.check_output(['git','show',RECIPE_BASELINE+':physical/streaming-tt-candidate.json'],cwd=ROOT,timeout=30))
    require(hashlib.sha256(baseline).hexdigest() == '2fc0a01dc1f6c0eed4fb4353be8955c7730305f4d2d8c6731538ea2f71af994f',
        'Controlled recipe baseline differs')
    before = json.loads(baseline); expected = dict(before,**RECIPE_CHANGES)
    require(type(config.get('CTS_SINK_CLUSTERING_SIZE')) is int and config == expected,
        'Controlled recipe changes more than the admitted five settings')
    trial_baseline = (clean_source.recipe_bytes('cts_trial', ROOT, producer_sha256) if source_mode == 'clean-v1' else
        subprocess.check_output(['git','show',CTS_TRIAL_BASELINE+':physical/streaming-tt-candidate.json'],cwd=ROOT,timeout=30))
    require(hashlib.sha256(trial_baseline).hexdigest() == CTS_TRIAL_BASELINE_SHA256,
        'Controlled CTS trial baseline differs')
    trial_before = json.loads(trial_baseline)
    require(trial_before.get('CTS_SINK_CLUSTERING_SIZE') is None and
        config == dict(trial_before,CTS_SINK_CLUSTERING_SIZE=8),
        'CTS8 trial changes more than sink clustering size')
    sdc = (regular(ROOT/'physical/streaming-tt.sdc').read_bytes() if source_mode == 'clean-v1' else
        subprocess.check_output(['git','show',RECIPE_BASELINE+':physical/streaming-tt.sdc'],cwd=ROOT,timeout=30))
    require(hashlib.sha256(sdc).hexdigest() == sha(ROOT/'physical/streaming-tt.sdc') ==
        'bcfd5a3ee86ccf13d6a8851e4b8d05b02584926862b922efa00204b3f628d0e5', 'Physical timing contract changed')
    defaults = dict(CTS_SINK_CLUSTERING_SIZE=None,CTS_APPLY_NDR='half',RUN_POST_GRT_DESIGN_REPAIR=False,
        RUN_POST_GRT_RESIZER_TIMING=False,GRT_RESIZER_HOLD_SLACK_MARGIN=0.05)
    return dict(schema='pinwheel.streaming-tt-physical-recipe-experiment.v1',qualified=False,
        baseline_commit=RECIPE_BASELINE,baseline_config_sha256=hashlib.sha256(baseline).hexdigest(),
        sdc_sha256=sha(ROOT/'physical/streaming-tt.sdc'),changes={name:dict(source_present_before=name in before,
            source_before=before.get(name),resolved_before=before.get(name,defaults[name]),after=value)
            for name,value in RECIPE_CHANGES.items()},
        cts_trial=dict(baseline_commit=CTS_TRIAL_BASELINE,baseline_config_sha256=CTS_TRIAL_BASELINE_SHA256,
            changes=dict(CTS_SINK_CLUSTERING_SIZE=dict(before=None,after=8)),
            required_resolved_settings=dict(CTS_SINK_CLUSTERING_ENABLE=True,CTS_SINK_CLUSTERING_SIZE=8),
            native_measured=False,clock_fanout_closed=False),
        boundary='Explicit eight-sink CTS clustering is requested; the pinned default keeps clustering enabled. This requests leaf clustering and does not prove an upper-level clock fanout bound. Actual resolved CTS arguments, clock loads, skew, capacitance, slew, setup/hold and routing must be measured on the fresh candidate. Optional clock nondefault routing remains disabled; postGRT design repair is retained and postGRT timing optimization remains disabled. All PDK routing rules, the 20 ns clock, 0.2 ns uncertainty, 4.0/0.2 ns I/O contract and mandatory fresh all-corner nonnegative setup/hold and electrical checks remain unchanged.')


def validate_cts_trial(resolved, native_log):
    """Observe delivery of this trial, without accepting clock loads or timing."""
    require(resolved.get('CTS_SINK_CLUSTERING_ENABLE') is True and
        type(resolved.get('CTS_SINK_CLUSTERING_SIZE')) is int and resolved['CTS_SINK_CLUSTERING_SIZE'] == 8,
        'Native resolved CTS settings differ from the explicit8 trial')
    commands = [shlex.split(line[2:]) for line in native_log.splitlines()
        if line.startswith('+ clock_tree_synthesis ')]
    require(len(commands) == 1, 'Expected one observed native CTS command')
    words = commands[0]
    require(words.count('-sink_clustering_enable') == 1 and words.count('-sink_clustering_size') == 1 and
        words.index('-sink_clustering_size') + 1 < len(words) and
        words[words.index('-sink_clustering_size') + 1] == '8', 'Native CTS command did not request8-sink clustering')
    return dict(resolved_and_logged_cts_trial=True,requested_sink_clustering_size=8,
        actual_clock_loads_validated=False,clock_fanout_closed=False,qualified=False)


def prepare_optimized(design, *, admission, admission_sha256, pdk):
    from streaming_tt_physical import safe_name, producer_hashes
    from streaming_tt_intake import dependency_closure, stage_sources
    from streaming_tt_pdk import verify_complete_pdk, complete_pdk
    from streaming_tt_verilog import derive
    from streaming_tt_pdn_geometry import admit
    safe_name(design)
    sources = producer_hashes(optimized=True)
    validation_data = clean_source.data_inputs(ROOT)
    for name, expected in validation_data.items():
        require(hashlib.sha256(committed(ROOT/name)).hexdigest() == expected, 'Commit exact validation data first')
    sources.update(validation_data)
    source_commit = subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,timeout=30).decode().strip()
    candidate = optimized_candidate(admission,admission_sha256)
    lock, completion = read(ROOT/'tools/physical-toolchain.json'), read(ROOT/'tools/streaming-tt-signoff.json')
    pdk = Path(pdk).resolve(); pdk_before = verify_complete_pdk(pdk,lock,completion)
    template = regular(ARCHIVE/'upstream/tt_block_6x4_pgvdd.def')
    require(sha(template) == lock['allocation']['tt_def_template_sha256'], 'Official6x4 allocation changed')
    geometry = admit(template, ROOT/'physical/streaming_tt/pdn.tcl')
    out = BASE/design; out.mkdir(parents=True,exist_ok=False)
    staged_pdk = complete_pdk(pdk,out/'pdk',pdk)
    require(verify_complete_pdk(pdk,lock,completion) == pdk_before, 'Completed PDK source changed during staging')
    inputs = out/'inputs'; inputs.mkdir()
    for source, name in [(candidate['verilog'],'design-original.v'),(candidate['netlist'],'certified.json'),
            (ROOT/'physical/streaming-tt.sdc','core.sdc'),(template,'tt_block_6x4_pgvdd.def'),
            (ROOT/'physical/streaming_tt/pdn.tcl','pdn.tcl'),
            (ROOT/'physical/streaming_tt/librelane_plugin_streaming_tt.py','librelane_plugin_streaming_tt.py'),
            (candidate['admission'],'parent-intake.json'),(candidate['worker_report'],'optimized-worker.json'),
            (candidate['raw_gate_report'],'raw-gate.json')]:
        shutil.copyfile(source,inputs/name)
    physical_verilog, derivation = derive(candidate,inputs/'physical-verilog',
        load_library(candidate['library']),actual_semantic_q_map)
    shutil.copyfile(physical_verilog,inputs/'design.v')
    config = read(ROOT/'physical/streaming-tt-candidate.json')
    source_mode = candidate.get('source_mode', 'historical')
    experiment = recipe_experiment(config, source_mode=source_mode, producer_sha256=sources)
    rc = validate_config(config,out/'pdk/ihp-sg13cmos5l/libs.ref/sg13cmos5l_stdcell/lef/sg13cmos5l_tech.lef')
    require(admit(inputs/'tt_block_6x4_pgvdd.def',inputs/'pdn.tcl') == geometry, 'Staged PDN geometry changed')
    write(inputs/'pdn-geometry-admission.json',geometry)
    write(inputs/'core.json',config); write(inputs/'seed.json',dict(nl='/work/inputs/design.v',metrics={}))
    write(inputs/'source-state.json',dict(top=TOP,source_ff_bits=6039,source_state=candidate['source_state'],
        inputs=candidate['inputs'],outputs=candidate['outputs']))
    write(inputs/'semantic-q-map.json',candidate['semantic_q_map']); write(inputs/'cost.json',candidate['cost'])
    closure = dependency_closure(ROOT,list(sources))
    require(set(closure['files']) == set(sources), 'Producer source map does not close its imports')
    stage_sources(ROOT,inputs/'producer',closure['files'],committed)
    for name, expected in sources.items(): require(sha(inputs/'producer'/name) == expected, 'Staged producer differs')
    files = {str(path.relative_to(inputs)):sha(path) for path in sorted(inputs.rglob('*')) if path.is_file()}
    receipt = dict(schema='pinwheel.streaming-tt-physical-input.v2',recipe='optimized_nominal_rc',status='prepared',
        qualified=False,physical_acceptance_claim=False,producer_commit=source_commit,workspace_root=str(ROOT),
        producer_sha256=sources,producer_dependency_closure=closure,producer_execution='staged_readonly_snapshot',
        design=design,depth=2,candidate=candidate,pdk=staged_pdk,pdk_source=pdk_before,
        input_sha256=files,template_sha256=sha(template),nominal_wire_rc=rc,synthesis_bypassed=True,
        physical_verilog_derivation=derivation,
        physical_recipe_experiment=experiment,validation_source_mode=source_mode,
        pdn_geometry_admission=geometry,
        placement_hold_repair_target_ns=config['PL_RESIZER_HOLD_SLACK_MARGIN'],
        repair_target_boundary='Placement and global-route hold repair cushions are 0.02 ns; the SDC and final nonnegative setup/hold requirements are unchanged.',
        parent_admitted_scope='through_global_route_only',
        boundary='Parent-admitted optimized whole-device kernel candidate, fresh completed pinnedPDK and explicit nominal wireRC. Initial live producer imports are byte-verified before CAD; the native worker then re-execs the staged producer snapshot. Coarse diagnosticCAD only; pending parent replay, post-PNR correspondence, extracted timing, physical signoff and officialprecheck are separate gates.')
    write(out/'inputs.json',receipt); verify_optimized(out)
    return out


def verify_optimized(design):
    from streaming_tt_pdk import verify_complete_pdk
    from streaming_tt_intake import dependency_closure
    from streaming_tt_pdn_geometry import admit
    design = Path(design).resolve(); receipt = read(regular(design/'inputs.json'))
    require(receipt.get('schema') == 'pinwheel.streaming-tt-physical-input.v2' and
        receipt.get('recipe') == 'optimized_nominal_rc' and receipt.get('qualified') is False and
        receipt.get('physical_acceptance_claim') is False and receipt.get('parent_admitted_scope') == 'through_global_route_only',
        'Invalid optimized physical claim boundary')
    verify_files(design/'inputs',receipt['input_sha256']); verify_files(ROOT,receipt['producer_sha256'])
    verify_files(design/'inputs/producer',receipt['producer_sha256'])
    require(admit(design/'inputs/tt_block_6x4_pgvdd.def',design/'inputs/pdn.tcl') == receipt.get('pdn_geometry_admission') ==
        read(design/'inputs/pdn-geometry-admission.json'), 'Prepared PDN geometry admission changed')
    require(dependency_closure(design/'inputs/producer',list(receipt['producer_sha256'])) ==
        receipt['producer_dependency_closure'], 'Staged physical import closure differs')
    derivation = receipt['physical_verilog_derivation']
    require(derivation.get('passed') is True and derivation.get('qualified') is False and
        derivation.get('exact_tuple_comparison') is True and derivation.get('all_actual_cells_and_pins') is True and
        derivation.get('flatten_only') is True and derivation.get('flat_native_reimport') is True and
        derivation.get('full_public_port_shape') is True and
        derivation.get('all_ff_d_clock_reset_and_io') is True and derivation.get('semantic_ff_bits') == 6039 and
        sha(design/'inputs/design-original.v') == receipt['candidate']['verilog_sha256'] == derivation['source_verilog_sha256'] and
        sha(design/'inputs/design.v') == derivation['physical_verilog_sha256'] and
        sha(design/'inputs/certified.json') == receipt['candidate']['netlist_sha256'], 'Optimized physical source binding differs')
    require(read(design/'inputs/physical-verilog/report.json') == derivation,
        'Physical Verilog derivation receipt changed')
    verify_complete_pdk(design/'pdk',read(ROOT/'tools/physical-toolchain.json'),read(ROOT/'tools/streaming-tt-signoff.json'))
    validate_config(read(design/'inputs/core.json'),design/'pdk/ihp-sg13cmos5l/libs.ref/sg13cmos5l_stdcell/lef/sg13cmos5l_tech.lef')
    source_mode = receipt.get('validation_source_mode', 'historical')
    require(source_mode == receipt['candidate'].get('source_mode', 'historical'), 'Prepared source mode changed')
    require(recipe_experiment(read(design/'inputs/core.json'), source_mode=source_mode,
        producer_sha256=receipt['producer_sha256']) == receipt['physical_recipe_experiment'],
        'Controlled physical recipe record changed')
    for name, expected in receipt['candidate']['consumed_sha256'].items():
        require(sha(regular(name)) == expected, 'Admitted optimized proof input/artifact changed: ' + name)
    for name, expected in [(receipt['candidate']['admission'],receipt['candidate']['admission_sha256']),
            (receipt['candidate']['worker_report'],receipt['candidate']['worker_report_sha256']),
            (receipt['candidate']['raw_gate_report'],receipt['candidate']['raw_gate_report_sha256'])]:
        require(sha(regular(name)) == expected, 'Admitted optimized receipt changed')
    return receipt
