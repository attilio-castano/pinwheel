"""A repaired checkpoint must not silently re-enter synthesis, CTS or repair."""
from copy import deepcopy
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
from physical_checkpoint_sta import analysis_tcl
from physical_route_intake import ihp_layer_rc, validate_repair_route
from physical_buffer_repair import compare_buffer_repair
from validation_run import sha


class RouteIntake(unittest.TestCase):
    def fixture(self, root):
        root = root.resolve()
        def write(name, data):
            path = root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(json.dumps(data) if not isinstance(data, str) else data)
            return path

        def ref(path, key='sha256'):
            return dict(report=str(path.relative_to(root)), **{key: sha(path)})

        design, pdk = root / 'build/physical/design', root / 'pdk'
        inputs = write('build/physical/design/inputs.json', {'mapped_input': {}})
        config = write('build/physical/design/core.json', {})
        resolved = write('build/physical/design/runs/control/resolved.json', {})
        pdk_receipt = write('pdk/installed.json', {})
        lef = write('pdk/ihp-sg13cmos5l/libs.ref/sg13cmos5l_stdcell/lef/sg13cmos5l_tech.lef',
                    '\n'.join(f'LAYER {n}\n TYPE\tROUTING ;\n WIDTH 0.20 ;\n'
                              ' RESISTANCE RPERSQ 0.103 ;\n CAPACITANCE CPERSQDIST 1.81e-5 ;\n'
                              f' EDGECAPACITANCE 4.47e-5 ;\nEND {n}\n'
                              for n in ['Metal1', 'Metal2', 'Metal3', 'Metal4', 'TopMetal1']))
        controls = dict(MAX_FANOUT_CONSTRAINT=8, GRT_ALLOW_CONGESTION=True)
        inv = write('build/physical/control-invocation.json', dict(design=design.name,
                    inputs_sha256=sha(inputs), base_config_sha256=sha(config),
                    pdk_receipt_sha256=sha(pdk_receipt), overrides=controls))
        prior = write('control.json', dict(tag='control', invocation_sha256=sha(inv)))
        previous = write('previous.json', dict(receipts={'physical': ref(prior, 'report_sha256')}))
        odb = write('repair/repaired.odb', 'repaired database')
        nl = write('measure/implemented.v', 'repaired netlist')
        repair = write('repair/report.json', dict(status='passed', artifacts_sha256={'repaired.odb': sha(odb)}))
        measure = write('measure/report.json', dict(status='passed', original_geometry_unchanged=True,
                        corridor_clear=True, inputs_sha256={str(odb): sha(odb), str(resolved): sha(resolved)},
                        artifacts_sha256={'implemented.v': sha(nl)}))
        oracle = write('oracle.json', dict(status='passed', edges=508252, mutants_rejected=1,
                       inputs_sha256={str(nl): sha(nl)}))
        receipts = {'targeted-03': ref(repair), 'local-measure-03': ref(measure), 'oracle': ref(oracle)}
        decision = 'local-repair-validated-coarse-routing-still-required'
        report = write('report.json', dict(status='passed', decision=decision,
                       original_geometry_unchanged=True, corridor_clear=True,
                       connectivity={'buffer_contracted_connectivity': True}, receipts=receipts))
        selection = write('selected.json', dict(schema=1, status='passed', decision=decision,
                          report='report.json', report_sha256=sha(report), receipts=receipts,
                          source_selection=dict(path='previous.json', sha256=sha(previous))))
        write('build/physical/design/repaired.odb', odb.read_text())
        state = write('build/physical/design/state.json', dict(odb='/work/core/repaired.odb', metrics={}))
        return dict(selection_path=selection, state_path=state, design=design,
                    from_step='OpenROAD.GlobalRouting', stop_step='OpenROAD.GlobalRouting',
                    overrides=dict(controls, RUN_POST_GRT_DESIGN_REPAIR=False,
                                   RUN_POST_GRT_RESIZER_TIMING=False, RUN_ANTENNA_REPAIR=False,
                                   LAYERS_RC=ihp_layer_rc(lef)), timeout_seconds=600, pdk_root=pdk, root=root)

    def test_accepts_frozen_repair_and_derives_nominal_units(self):
        with tempfile.TemporaryDirectory() as folder:
            args = self.fixture(Path(folder))
            result = validate_repair_route(**args)
            self.assertEqual(result['netlist_sha256'], sha(Path(folder) / 'measure/implemented.v'))
            self.assertEqual(args['overrides']['LAYERS_RC']['nom_*']['Metal2'],
                             {'res': 0.000515, 'cap': 9.302e-5})

    def test_rejects_stale_repair_oracle_design_and_database(self):
        for name in ['oracle.json', 'repair/repaired.odb', 'measure/implemented.v', 'report.json',
                     'build/physical/design/repaired.odb', 'build/physical/design/inputs.json']:
            with self.subTest(name=name), tempfile.TemporaryDirectory() as folder:
                root = Path(folder)
                args = self.fixture(root)
                (root / name).write_text('changed bytes')
                with self.assertRaises(ValueError):
                    validate_repair_route(**args)

    def test_rejects_new_cts_unbounded_runs_repairs_and_changed_rc(self):
        with tempfile.TemporaryDirectory() as folder:
            args = self.fixture(Path(folder))
            for key, value in [('from_step', 'OpenROAD.CTS'), ('stop_step', 'OpenROAD.DetailedRouting'),
                               ('timeout_seconds', 601), ('timeout_seconds', 0)]:
                with self.subTest(key=key, value=value), self.assertRaises(ValueError):
                    validate_repair_route(**dict(args, **{key: value}))
            for key, value in [('RUN_POST_GRT_DESIGN_REPAIR', True), ('MAX_FANOUT_CONSTRAINT', 16),
                               ('LAYERS_RC', {}), ('PL_TARGET_DENSITY_PCT', 40)]:
                changed = deepcopy(args)
                changed['overrides'][key] = value
                with self.subTest(control=key), self.assertRaises(ValueError):
                    validate_repair_route(**changed)
            state = args['state_path']
            for extra in [{'metrics': {'old_slack': 4}}, {'spef': '/work/core/old.spef'}]:
                state.write_text(json.dumps({'odb': '/work/core/repaired.odb', 'metrics': {}, **extra}))
                with self.assertRaisesRegex(ValueError, 'only ODB'):
                    validate_repair_route(**args)

    def test_physical_pin_names_are_literal_tcl_data(self):
        script = analysis_tcl({'pins': ['memory.storage0/A_DOUT[42]']})
        self.assertIn('findITerm {memory.storage0/A_DOUT[42]}', script)
        for pin in ['x} ; exit ; {', 'x\nexit', 'x\\', 'x"']:
            with self.subTest(pin=pin), self.assertRaises(ValueError):
                analysis_tcl({'pins': [pin]})

    def diagnostic_fixture(self, root):
        """Independent functional/geometry evidence can admit diagnostic routing.

        Incomplete placement timing deliberately grants no timing qualification.
        """
        args = self.fixture(root)
        root = args['root']

        def update(name, **fields):
            p = root / name
            data = json.loads(p.read_text())
            data.update(fields)
            p.write_text(json.dumps(data))
            return p

        source = root / 'build/physical/design/source.odb'
        source.write_text('original database')
        update('repair/report.json', source_database=str(source.relative_to(root)),
               source_database_sha256=sha(source))
        update('measure/report.json', clock_nets_unchanged=670, nontarget_signal_nets_unchanged=True,
               connectivity={'buffer_contracted_connectivity': True})
        update('oracle.json', inputs_sha256={str(root / name): sha(root / name)
                                             for name in ['measure/implemented.v', 'measure/report.json']})
        inv = update('build/physical/control-invocation.json', exit_code=0, overrides=args['overrides'])
        update('control.json', invocation_sha256=sha(inv),
               artifact_sha256={str(source.relative_to(root)): sha(source)})
        roles = dict(probe='repair/report.json', measurement='measure/report.json', oracle='oracle.json',
                     control_invocation='build/physical/control-invocation.json', control_physical='control.json')
        selection = dict(schema=2, status='passed', decision='admit-one-diagnostic-coarse-route',
                         timing_admission='requires-fresh-complete-wire-estimates',
                         receipts={k: dict(path=v, sha256=sha(root / v)) for k, v in roles.items()})
        args['selection_path'].write_text(json.dumps(selection))
        return args

    def test_diagnostic_route_keeps_timing_unqualified_and_bounds_the_stage(self):
        with tempfile.TemporaryDirectory() as folder:
            args = self.diagnostic_fixture(Path(folder))
            evidence = validate_repair_route(**args)
            self.assertEqual(evidence['timing_admission'], 'requires-fresh-complete-wire-estimates')
            for change in [dict(from_step='OpenROAD.CTS'), dict(stop_step='OpenROAD.DetailedRouting'),
                           dict(timeout_seconds=601), dict(overrides=dict(args['overrides'], LAYERS_RC={}))]:
                with self.subTest(change=change), self.assertRaises(ValueError):
                    validate_repair_route(**dict(args, **change))

    def test_diagnostic_route_rejects_incomplete_functional_or_geometry_evidence(self):
        cases = [('measurement', 'clock_nets_unchanged', 0),
                 ('measurement', 'nontarget_signal_nets_unchanged', False),
                 ('measurement', 'original_geometry_unchanged', False),
                 ('measurement', 'connectivity', {'buffer_contracted_connectivity': False}),
                 ('measurement', 'inputs_sha256', {}),
                 ('oracle', 'edges', 508251), ('oracle', 'mutants_rejected', 0),
                 ('oracle', 'inputs_sha256', {}), ('probe', 'status', 'failed')]
        for role, field, value in cases:
            with self.subTest(role=role, field=field), tempfile.TemporaryDirectory() as folder:
                args = self.diagnostic_fixture(Path(folder))
                selection = json.loads(args['selection_path'].read_text())
                ref = selection['receipts'][role]
                path = args['root'] / ref['path']
                data = json.loads(path.read_text())
                data[field] = value
                path.write_text(json.dumps(data))
                ref['sha256'] = sha(path)  # Receipt is authentic but semantically insufficient.
                args['selection_path'].write_text(json.dumps(selection))
                with self.assertRaises(ValueError):
                    validate_repair_route(**args)

    def test_diagnostic_route_rejects_changed_artifacts_and_stale_state(self):
        for name in ['measure/implemented.v', 'repair/repaired.odb',
                     'build/physical/design/source.odb', 'build/physical/design/repaired.odb']:
            with self.subTest(name=name), tempfile.TemporaryDirectory() as folder:
                args = self.diagnostic_fixture(Path(folder))
                (args['root'] / name).write_text('changed bytes')
                with self.assertRaises(ValueError):
                    validate_repair_route(**args)
        with tempfile.TemporaryDirectory() as folder:
            args = self.diagnostic_fixture(Path(folder))
            state = json.loads(args['state_path'].read_text())
            state['metrics'] = {'old_slack': 5}
            args['state_path'].write_text(json.dumps(state))
            with self.assertRaisesRegex(ValueError, 'only ODB'):
                validate_repair_route(**args)

    def target_fixture(self, root):
        args = self.fixture(root)
        root = args['root']

        def write(name, data):
            path = root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(json.dumps(data) if not isinstance(data, str) else data)
            return path

        def ref(path):
            return dict(path=str(path.relative_to(root)), sha256=sha(path))

        corners = ['fast', 'slow', 'typ']
        resolved = write('build/physical/design/runs/control/resolved.json', {'STA_CORNERS': corners})
        source = write('build/physical/design/source.odb', 'original database')
        parent = write('build/physical/design/parent.json', {'odb': '/work/core/source.odb', 'metrics': {}})
        inv = root / 'build/physical/control-invocation.json'
        inv_data = json.loads(inv.read_text()); inv_data['exit_code'] = 0
        write(str(inv.relative_to(root)), inv_data)
        physical = write('control.json', dict(tag='control', invocation_sha256=sha(inv),
            state_sha256=sha(parent), artifact_sha256={str(source.relative_to(root)): sha(source)}))
        odb = root / 'repair/repaired.odb'
        probe = write('repair/report.json', dict(status='passed', physical_tag='control', source_unchanged=True,
            containers={'probe': 'absent'}, source_database=str(source.relative_to(root)),
            source_database_sha256=sha(source), artifacts_sha256={'repaired.odb': sha(odb)}))
        cell = dict(type='sg13cmos5l_buf_1', parameters={},
                    port_directions={'A': 'input', 'X': 'output'}, connections={'A': [2], 'X': [3]})
        before = dict(ports={'i': {'direction': 'input', 'bits': [2]},
                             'o': {'direction': 'output', 'bits': [3]}}, cells={'buffer': cell})
        after = deepcopy(before); after['cells']['buffer']['type'] = 'sg13cmos5l_buf_4'
        readbacks = [write('closure/' + name + '.json', {'modules': {'chip': module}})
                     for name, module in [('before', before), ('after', after)]]
        context = dict(instances={'buffer': {'master': 'buf_1'}, 'fixed': {'x': 2}},
            nets={}, macro_pins={}, ports={}, rows=[], placement_blockages=[], power_shapes=[],
            routing_obstructions=[], macro_obstructions=[], die=[0, 0, 10, 10])
        reference_context = write('reference/context.json', context)
        context['instances']['buffer']['master'] = 'buf_4'
        selected_context = write('measure/context.json', context)
        reference_netlist = write('reference/implemented.v', 'original netlist')
        reference = write('reference/report.json', dict(status='passed', containers={'reference': 'absent'},
            source_database_sha256=sha(source), netlist=str(reference_netlist.relative_to(root)),
            netlist_sha256=sha(reference_netlist), artifacts_sha256={
                'context.json': sha(reference_context), 'implemented.v': sha(reference_netlist)}))
        netlist = root / 'measure/implemented.v'
        timing = dict(timing__setup__ws=1.0, timing__hold__ws=0.1,
                      design__max_fanout_violation__count=0, design__max_slew_violation__count=0,
                      design__max_cap_violation__count=0)
        quality = dict(wire_annotation=dict(complete_for_consumed_nets=True,
                                           partially_unannotated=0, consumed_unannotated=[]))
        measure = write('measure/report.json', dict(status='passed', containers={'measure': 'absent'},
            source_database=str(odb.relative_to(root)), source_database_sha256=sha(odb),
            netlist=str(netlist.relative_to(root)), netlist_sha256=sha(netlist), repair_probe=ref(probe),
            inputs_sha256={str(resolved.relative_to(root)): sha(resolved)}, corridor_clear=True,
            target={'database_sha256': sha(odb)}, estimation_modes={c: 'placement' for c in corners},
            fresh_timing={c: timing for c in corners}, measurement_quality={c: quality for c in corners},
            artifacts_sha256={'context.json': sha(selected_context), 'implemented.v': sha(netlist)}))
        oracle = write('oracle.json', dict(status='passed', edges=12, mutants_rejected=1,
                                         input_sha256={str(reference_netlist): sha(reference_netlist)}))
        closure = write('closure/report.json', dict(status='passed',
            artifact_sha256={p.name: sha(p) for p in readbacks}, probe_receipts={'selected': ref(probe)},
            measurement_receipts={'selected': ref(measure), 'reference': ref(reference)},
            selected_parent_state=ref(parent), selected_parent_physical_report=ref(physical),
            selected_database=ref(odb), selected_netlist=ref(netlist),
            connectivity=compare_buffer_repair(before, after, allow_resizing=True),
            functional={'report': ref(oracle), 'edges': 12}))
        args['selection_path'].write_text(json.dumps(dict(schema=3, status='passed',
            decision='admit-one-validated-repair-coarse-route', validation=ref(closure),
            measurement='selected', reference_measurement='reference', probe='selected', module='chip',
            readbacks={'before': 'before.json', 'after': 'after.json'})))
        return args

    def update_target_measurement(self, args, change):
        """Rehash a semantically bad receipt so tests exercise admission itself."""
        root = args['root']; path = root / 'measure/report.json'
        data = json.loads(path.read_text()); change(data)
        path.write_text(json.dumps(data))
        closure_path = root / 'closure/report.json'; closure = json.loads(closure_path.read_text())
        closure['measurement_receipts']['selected']['sha256'] = sha(path)
        closure_path.write_text(json.dumps(closure))
        selection = json.loads(args['selection_path'].read_text())
        selection['validation']['sha256'] = sha(closure_path)
        args['selection_path'].write_text(json.dumps(selection))

    def test_target_repair_accepts_sizing_without_a_chip_specific_edge_count(self):
        with tempfile.TemporaryDirectory() as folder:
            args = self.target_fixture(Path(folder))
            result = validate_repair_route(**args)
            self.assertEqual(result['resized_buffers'], 1)
            self.assertEqual(result['pin_edges_reused'], 12)
            self.assertEqual(result['timing_admission'], 'positive-placement-margins-complete-wire-estimates')

    def test_target_repair_rejects_stale_artifacts_and_changed_continuation(self):
        for name in ['repair/repaired.odb', 'reference/implemented.v', 'closure/before.json',
                     'measure/context.json', 'build/physical/design/source.odb',
                     'build/physical/design/repaired.odb', 'build/physical/design/inputs.json',
                     'build/physical/design/runs/control/resolved.json']:
            with self.subTest(name=name), tempfile.TemporaryDirectory() as folder:
                args = self.target_fixture(Path(folder))
                (args['root'] / name).write_text('changed bytes')
                with self.assertRaises(ValueError):
                    validate_repair_route(**args)
        with tempfile.TemporaryDirectory() as folder:
            args = self.target_fixture(Path(folder))
            changes = [dict(from_step='OpenROAD.CTS'), dict(stop_step='OpenROAD.DetailedRouting'),
                       dict(timeout_seconds=601), dict(overrides=dict(args['overrides'], RUN_ANTENNA_REPAIR=True)),
                       dict(overrides=dict(args['overrides'], CTS_SINK_CLUSTERING_SIZE=20))]
            for change in changes:
                with self.subTest(change=change), self.assertRaises(ValueError):
                    validate_repair_route(**dict(args, **change))

    def test_target_repair_rejects_unqualified_measurements(self):
        for key, value in [('timing__setup__ws', -0.1), ('timing__hold__ws', 0.0),
                           ('timing__setup__ws', float('nan')), ('design__max_fanout_violation__count', 1),
                           ('design__max_slew_violation__count', 1), ('design__max_cap_violation__count', 1)]:
            with self.subTest(key=key), tempfile.TemporaryDirectory() as folder:
                args = self.target_fixture(Path(folder))
                self.update_target_measurement(args, lambda d: d['fresh_timing']['slow'].update({key: value}))
                with self.assertRaisesRegex(ValueError, 'Unqualified'):
                    validate_repair_route(**args)
        for key, value in [('complete_for_consumed_nets', False), ('partially_unannotated', 1),
                           ('consumed_unannotated', ['loaded_net'])]:
            with self.subTest(key=key), tempfile.TemporaryDirectory() as folder:
                args = self.target_fixture(Path(folder))
                self.update_target_measurement(args, lambda d: d['measurement_quality']['slow']['wire_annotation'].update({key: value}))
                with self.assertRaisesRegex(ValueError, 'Unqualified'):
                    validate_repair_route(**args)

    def test_target_repair_rejects_unrelated_geometry_even_with_updated_receipts(self):
        with tempfile.TemporaryDirectory() as folder:
            args = self.target_fixture(Path(folder)); path = args['root'] / 'measure/context.json'
            context = json.loads(path.read_text()); context['instances']['fixed']['x'] = 3
            path.write_text(json.dumps(context))
            self.update_target_measurement(args, lambda d: d['artifacts_sha256'].update({'context.json': sha(path)}))
            with self.assertRaisesRegex(ValueError, 'unrelated placement'):
                validate_repair_route(**args)


if __name__ == '__main__':
    unittest.main()
