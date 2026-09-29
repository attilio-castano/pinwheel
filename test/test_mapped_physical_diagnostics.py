"""Fresh physical timing must identify its completed checkpoint and RC mode."""
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
spec = importlib.util.spec_from_file_location('diagnostic', ROOT / 'scripts/check-mapped-physical.py')
diagnostic = importlib.util.module_from_spec(spec)
spec.loader.exec_module(diagnostic)
from validation_run import sha
from physical_checkpoint_sta import measurement_quality


class PhysicalDiagnostics(unittest.TestCase):
    def test_local_repair_requires_exact_source_and_frozen_completed_probe(self):
        with tempfile.TemporaryDirectory() as folder, patch.object(diagnostic, 'ROOT', Path(folder).resolve()):
            root=Path(folder).resolve();source=root/'source.odb';source.write_bytes(b'source')
            target=root/'repaired.odb';target.write_bytes(b'repair')
            p=root/'report.json'
            probe=dict(status='passed',source_unchanged=True,physical_tag='run',source_database='source.odb',
                source_database_sha256=sha(source),containers={'exact-probe':'absent'},
                inputs_sha256={str(source):sha(source)},artifacts_sha256={'repaired.odb':sha(target)})
            p.write_text(json.dumps(probe))
            self.assertEqual(diagnostic.repair_checkpoint(p,source,'run')[0],target)
            for key,value in [('status','failed'),('source_unchanged',False),('physical_tag','other'),
                              ('containers',{'exact-probe':'running'}),('source_database_sha256','stale')]:
                p.write_text(json.dumps(dict(probe,**{key:value})))
                with self.subTest(key=key),self.assertRaises(ValueError):
                    diagnostic.repair_checkpoint(p,source,'run')
            p.write_text(json.dumps(probe));target.write_bytes(b'changed')
            with self.assertRaisesRegex(ValueError,'repair database'):
                diagnostic.repair_checkpoint(p,source,'run')

    def test_wire_annotation_needs_actual_loads_and_exact_driver_names(self):
        context = dict(nets={'unused': dict(type='SIGNAL', terminals=[], ports=['unused']),
            'clock': dict(type='CLOCK', terminals=[dict(instance='buf', pin='X', direction='OUTPUT'),
                dict(instance='reg', pin='CLK', direction='INPUT')], ports=[])})
        report = ('\nmax fanout\n\nPin Limit Fanout Slack\nbuf/X 8 12 -4 (VIOLATED)\n\n\n'
                  'Found 2 unannotated drivers.\n unused\n dummy/X\nFound 0 partially unannotated drivers.\n')
        quality = measurement_quality(report, context, ['dummy/X'])
        self.assertTrue(quality['wire_annotation']['complete_for_consumed_nets'])
        self.assertEqual(quality['fanout_violations'][0]['kind'], 'CLOCK')
        used = measurement_quality(report.replace('unused\n', 'buf/X\n'), context, ['dummy/X'])
        self.assertFalse(used['wire_annotation']['complete_for_consumed_nets'])
        self.assertEqual(used['wire_annotation']['consumed_unannotated'][0]['loads'], 1)
        partial = measurement_quality(report.replace('0 partially', '1 partially'), context, ['dummy/X'])
        self.assertFalse(partial['wire_annotation']['complete_for_consumed_nets'])
        for bad in [report.replace('Found 2', 'Found 3'), report.replace('dummy/X', 'unknown/X'), '']:
            with self.subTest(report=bad), self.assertRaises(ValueError):
                measurement_quality(bad, context, ['dummy/X'])

    def fixture(self, root):
        design = root / 'build/physical/design'
        previous, final = '25-openroad-stamidpnr-2', '26-openroad-globalrouting'
        for step in [previous, final]:
            folder = design / 'runs/run' / step
            folder.mkdir(parents=True)
            (folder / 'chip.odb').write_bytes(step.encode())
            state = dict(odb='/work/core/runs/run/' + step + '/chip.odb', metrics={})
            (folder / 'state_out.json').write_text(json.dumps(state))
        state_path = design / 'runs/run' / final / 'state_out.json'
        odb = state_path.with_name('chip.odb')
        report = dict(tag='run', last_completed_step=final, completed_steps=[previous, final],
                      state_sha256=sha(state_path), artifact_sha256={str(odb.relative_to(root)): sha(odb)})
        return design, report, previous

    def test_blank_fanout_slack_keeps_the_violation(self):
        context=dict(nets={'signal':dict(type='SIGNAL',ports=[],terminals=[
            dict(instance='buf',pin='X',direction='OUTPUT')])})
        template=('\nmax fanout\n\nPin Limit Fanout Slack\n{}\n\nmax capacitance\n\n\n'
                  'Found 0 unannotated drivers.\nFound 0 partially unannotated drivers.\n')
        for row in ('buf/X 8 9 -1 (VIOLATED)','buf/X 8 9    (VIOLATED)'):
            quality=measurement_quality(template.format(row),context,[])
            self.assertEqual(quality['fanout_violations'],[
                dict(pin='buf/X',net='signal',kind='SIGNAL',limit=8,fanout=9)])
        for row in ('buf/X 8 (VIOLATED)','buf/X 8 7 (VIOLATED)',
                    'buf/X 8 9 1 (VIOLATED)','buf/X 8 9 -2 (VIOLATED)','missing/X 8 9 (VIOLATED)'):
            with self.subTest(row=row),self.assertRaises(ValueError):
                measurement_quality(template.format(row),context,[])

    def test_selects_completed_requested_checkpoint_not_latest_metric(self):
        with tempfile.TemporaryDirectory() as folder, patch.object(diagnostic, 'ROOT', Path(folder)):
            design, report, previous = self.fixture(Path(folder))
            path, state, odb = diagnostic.checkpoint(report, design, previous)
            self.assertEqual(path.parent.name, previous)
            self.assertEqual(odb.read_bytes(), previous.encode())
            self.assertEqual(state['metrics'], {})
            self.assertEqual(diagnostic.checkpoint(report, design)[0].parent.name, report['last_completed_step'])

    def test_rejects_incomplete_or_outside_step_and_changed_final_artifacts(self):
        with tempfile.TemporaryDirectory() as folder, patch.object(diagnostic, 'ROOT', Path(folder)):
            design, report, _ = self.fixture(Path(folder))
            for step in ['27-openroad-repairdesignpostgrt', '../outside']:
                with self.subTest(step=step), self.assertRaisesRegex(ValueError, 'completed step'):
                    diagnostic.checkpoint(report, design, step)
            path, _, odb = diagnostic.checkpoint(report, design)
            odb.write_bytes(b'changed database')
            with self.assertRaisesRegex(ValueError, 'database'):
                diagnostic.checkpoint(report, design)
            path.write_text('{}')
            with self.assertRaisesRegex(ValueError, 'final state'):
                diagnostic.checkpoint(report, design)

    def test_estimation_requires_propagated_clock_and_unambiguous_mode(self):
        clock = 'PINWHEEL_PROPAGATED_CLOCK 1\n'
        place = 'PINWHEEL_ESTIMATION_GLOBAL_ROUTES 0\n'
        route = 'PINWHEEL_ESTIMATION_GLOBAL_ROUTES 1\n'
        self.assertEqual(diagnostic.estimation_mode(clock + place), 'placement')
        self.assertEqual(diagnostic.estimation_mode(clock + route), 'global_routing')
        for text in [place, 'PINWHEEL_PROPAGATED_CLOCK 0\n' + route, clock, clock + place + route]:
            with self.subTest(text=text), self.assertRaises(ValueError):
                diagnostic.estimation_mode(text)


if __name__ == '__main__':
    unittest.main()
