"""Admission and owned-process cleanup controls for mapped TT acceptance."""
import importlib.util
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import patch


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
spec = importlib.util.spec_from_file_location('tt_buffered_netlist',
                                            ROOT / 'scripts/check-tt-buffered-netlist.py')
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)


def fixture(ports=gate.PORTS):
    declarations = '\n'.join(f'{direction} {width} {name};'
                             for name, (direction, width) in ports.items())
    return ('module ' + gate.TOP + '(' + ','.join(ports) + ');\n' + declarations + '\n' +
            gate.MASTER + ' \\engine.memory.storage0 (.A_CLK(clk));\n' +
            gate.MASTER + ' \\engine.memory.storage1 (.A_CLK(clk));\nendmodule\n')


class MappedBoundaryControls(unittest.TestCase):
    def test_only_top_identifier_is_transformed_and_supplies_are_explicit(self):
        original = '// module tt_um_pinwheel_buffered is the mapped name.\n' + fixture()
        renamed, adapter = gate.adapt_netlist(original)
        self.assertEqual(renamed, original.replace('module ' + gate.TOP + '(',
                                                  'module ' + gate.IMPLEMENTED + '(', 1))
        self.assertIn('supply1 VPWR;', adapter)
        self.assertIn('supply0 VGND;', adapter)
        self.assertIn('.VPWR(VPWR), .VGND(VGND)', adapter)

    def test_native_logical_export_has_exact_public_ports_and_no_supply_connections(self):
        original = fixture(gate.PUBLIC)
        renamed, adapter = gate.adapt_netlist(original)
        self.assertEqual(renamed, original.replace('module ' + gate.TOP + '(',
                                                  'module ' + gate.IMPLEMENTED + '(', 1))
        self.assertEqual(adapter, gate.LOGICAL_ADAPTER)
        self.assertNotIn('VPWR', adapter)
        self.assertNotIn('VGND', adapter)
        for name in gate.PUBLIC:
            self.assertIn('.' + name + '(' + name + ')', adapter)

    def test_partial_supply_and_extra_native_export_ports_are_rejected(self):
        for ports in ({**gate.PUBLIC, 'VPWR': ('inout', '')},
                      {**gate.PUBLIC, 'VGND': ('inout', '')},
                      {**gate.PUBLIC, 'VDD': ('inout', ''), 'VSS': ('inout', '')},
                      {**gate.PUBLIC, 'extra': ('input', '')},
                      {**gate.PORTS, 'extra': ('input', '')}):
            with self.subTest(ports=list(ports)), self.assertRaisesRegex(ValueError, 'Unexpected mapped top ports'):
                gate.adapt_netlist(fixture(ports))

    def test_wrong_missing_or_multiple_top_and_wrong_macro_count_are_rejected(self):
        for text in (fixture().replace(gate.TOP, 'wrong_top'),
                     fixture().replace('module ' + gate.TOP, 'missing ' + gate.TOP),
                     fixture() + 'module extra(); endmodule\n',
                     fixture().replace(gate.MASTER + ' \\engine.memory.storage1',
                                       'wrong_macro \\engine.memory.storage1')):
            with self.subTest(text=text[:100]), self.assertRaises(ValueError):
                gate.adapt_netlist(text)

    def test_bad_supply_pins_widths_powered_cells_and_behavioral_logic_are_rejected(self):
        for text in (fixture().replace('VGND', 'VSS'),
                     fixture().replace('inout  VPWR;', 'input  VPWR;'),
                     fixture().replace('[7:0] ui_in', '[6:0] ui_in'),
                     fixture().replace('(.A_CLK(clk))', '(.VDD(VPWR), .A_CLK(clk))'),
                     fixture().replace('endmodule', 'always @(posedge clk) ;\nendmodule'),
                     '`include "foreign.v"\n' + fixture()):
            with self.subTest(text=text[:100]), self.assertRaises(ValueError):
                gate.adapt_netlist(text)

    def test_changed_frozen_source_is_rejected(self):
        with tempfile.TemporaryDirectory() as folder:
            path = Path(folder) / 'model.v'
            path.write_text('original')
            frozen = {str(path): gate.sha(path)}
            gate.verify_hashes(frozen)
            path.write_text('changed')
            with self.assertRaisesRegex(ValueError, 'Input changed'):
                gate.verify_hashes(frozen)

    def test_checkpoint_must_name_exact_selected_nl(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            design = root / 'design'; design.mkdir()
            nl = design / 'mapped.nl.v'; nl.write_text(fixture())
            state = root / 'state.json'
            gate.write(state, dict(nl='/work/core/other.nl.v'))
            args = dict(netlist=str(nl), state=str(state), design=str(design))
            with self.assertRaisesRegex(ValueError, 'differs from the provided checkpoint'):
                gate.selected_state(args, {})
            gate.write(state, dict(nl='/work/core/../mapped.nl.v'))
            with self.assertRaisesRegex(ValueError, 'Invalid checkpoint'):
                gate.selected_state(args, {})

    def test_fresh_export_can_replace_inherited_nl_and_must_match_selected_odb(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            design = root / 'design'; design.mkdir()
            database = design / 'latest.odb'; database.write_text('final database')
            nl = design / 'fresh.nl.v'; nl.write_text(fixture())
            state = root / 'state.json'
            gate.write(state, dict(nl='/work/core/old.nl.v', odb='/work/core/latest.odb'))
            export = root / 'export.json'
            receipt = dict(status='passed', netlist=str(nl), netlist_sha256=gate.sha(nl),
                           source_database=str(database), source_database_sha256=gate.sha(database))
            gate.write(export, receipt)
            args = dict(netlist=str(nl), state=str(state), design=str(design), mapped_export=str(export))
            result = gate.selected_state(args, {})
            self.assertTrue(result['latest_odb_match_established'])
            foreign = design / 'foreign.odb'; foreign.write_text('another database')
            receipt.update(source_database=str(foreign), source_database_sha256=gate.sha(foreign))
            gate.write(export, receipt)
            with self.assertRaisesRegex(ValueError, 'differs from the selected checkpoint ODB'):
                gate.selected_state(args, {})

    def test_recovery_root_resolves_exact_nl_and_fresh_export_odb(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            design = root / 'design'; design.mkdir()
            nl = design / 'mapped.nl.v'; nl.write_text(fixture())
            database = design / 'latest.odb'; database.write_text('recovery checkpoint')
            state = root / 'state.json'
            gate.write(state, dict(nl='/work/recovery/mapped.nl.v',
                                   odb='/work/recovery/latest.odb'))
            args = dict(netlist=str(nl), state=str(state), design=str(design),
                        container_design_root='/work/recovery')
            hashes = {}
            result = gate.selected_state(args, hashes)
            self.assertEqual(result['container_design_root'], '/work/recovery')
            self.assertEqual(result['nl_in_state'], '/work/recovery/mapped.nl.v')
            self.assertEqual(hashes[str(state.resolve())], gate.sha(state))
            fresh = design / 'fresh.nl.v'; fresh.write_text(fixture())
            export = root / 'export.json'
            gate.write(export, dict(status='passed', netlist=str(fresh), netlist_sha256=gate.sha(fresh),
                                    source_database=str(database), source_database_sha256=gate.sha(database)))
            args.update(netlist=str(fresh), mapped_export=str(export))
            result = gate.selected_state(args, {})
            self.assertTrue(result['latest_odb_match_established'])
            self.assertEqual(result['source_database'], str(database.resolve()))

    def test_wrong_container_root_partial_prefix_and_traversal_are_rejected(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            design = root / 'design'; design.mkdir()
            nl = design / 'mapped.nl.v'; nl.write_text(fixture())
            state = root / 'state.json'
            args = dict(netlist=str(nl), state=str(state), design=str(design),
                        container_design_root='/work/recovery')
            for nl_path, odb_path in (
                    ('/work/core/mapped.nl.v', None),
                    ('/work/recovery-extra/mapped.nl.v', None),
                    ('/work/recovery/../mapped.nl.v', None),
                    ('/work/recovery//mapped.nl.v', None),
                    ('/work/recovery/mapped.nl.v', '/work/core/latest.odb'),
                    ('/work/recovery/mapped.nl.v', '/work/recovery-extra/latest.odb'),
                    ('/work/recovery/mapped.nl.v', '/work/recovery/../latest.odb'),
                    ('/work/recovery/mapped.nl.v', '/work/recovery//latest.odb')):
                gate.write(state, dict(nl=nl_path, odb=odb_path))
                with self.subTest(nl=nl_path, odb=odb_path), self.assertRaises(ValueError):
                    gate.selected_state(args, {})
            gate.write(state, dict(nl='/work/recovery/mapped.nl.v'))
            args['container_design_root'] = '/work/other'
            with self.assertRaisesRegex(ValueError, 'Unsupported container design root'):
                gate.selected_state(args, {})

    def test_recovery_odb_symlink_escape_and_foreign_export_are_rejected(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            design = root / 'design'; design.mkdir()
            nl = design / 'mapped.nl.v'; nl.write_text(fixture())
            foreign = root / 'foreign.odb'; foreign.write_text('foreign checkpoint')
            linked = design / 'linked.odb'; linked.symlink_to(foreign)
            state = root / 'state.json'
            gate.write(state, dict(nl='/work/recovery/mapped.nl.v', odb='/work/recovery/linked.odb'))
            args = dict(netlist=str(nl), state=str(state), design=str(design),
                        container_design_root='/work/recovery')
            with self.assertRaisesRegex(ValueError, 'outside the prepared design'):
                gate.selected_state(args, {})
            database = design / 'latest.odb'; database.write_text('recovery checkpoint')
            gate.write(state, dict(nl='/work/recovery/mapped.nl.v', odb='/work/recovery/latest.odb'))
            export = root / 'export.json'
            gate.write(export, dict(status='passed', netlist=str(nl), netlist_sha256=gate.sha(nl),
                                    source_database=str(foreign), source_database_sha256=gate.sha(foreign)))
            args['mapped_export'] = str(export)
            with self.assertRaisesRegex(ValueError, 'differs from the selected checkpoint ODB'):
                gate.selected_state(args, {})

    def test_cli_recovery_root_is_explicit_and_unknown_root_rejected_before_launch(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            argv = ['gate', '--netlist', 'nl.v', '--validation', 'gate.json',
                    '--macro-root', 'models', '--tag', 'recovery-root-test',
                    '--container-design-root', '/work/recovery']
            result = dict(timed_out=True, exit_code=-15, process_group_stopped=True)
            with patch.object(gate, 'ROOT', root), patch.object(sys, 'argv', argv), \
                    patch.object(gate, 'supervise', return_value=result):
                self.assertEqual(gate.main(), 1)
            plan = gate.read(root / 'build/tt-buffered/netlist/recovery-root-test/plan.json')
            self.assertEqual(plan['container_design_root'], '/work/recovery')
            argv[-1] = '/work/unknown'
            with patch.object(sys, 'argv', argv), patch.object(gate, 'supervise') as run:
                with self.assertRaises(SystemExit) as error:
                    gate.main()
                self.assertEqual(error.exception.code, 2)
                run.assert_not_called()

    def test_timeout_stops_owned_worker_and_its_descendant(self):
        with tempfile.TemporaryDirectory() as folder:
            out = Path(folder)
            pid_file = out / 'descendant.pid'
            code = '''import signal, subprocess, sys, time
from pathlib import Path
child = subprocess.Popen([sys.executable, '-c', 'import time; time.sleep(30)'])
Path(sys.argv[1]).write_text(str(child.pid))
def stop(*_):
    child.wait(timeout=2)
    sys.exit(0)
signal.signal(signal.SIGTERM, stop)
time.sleep(30)
'''
            result = gate.supervise([sys.executable, '-c', code, pid_file], out, 0.3)
            self.assertTrue(result['timed_out'])
            self.assertTrue(result['process_group_stopped'])
            pid = int(pid_file.read_text())
            with self.assertRaises(ProcessLookupError):
                os.kill(pid, 0)
            self.assertTrue((out / 'worker.log').is_file())

    def test_timeout_report_cannot_claim_acceptance(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            args = ['gate', '--netlist', 'nl.v', '--validation', 'gate.json',
                    '--macro-root', 'models', '--tag', 'timeout-test', '--timeout-seconds', '1']
            result = dict(timed_out=True, exit_code=-15, process_group_stopped=True)
            previous_term = signal.getsignal(signal.SIGTERM)
            with patch.object(gate, 'ROOT', root), patch.object(sys, 'argv', args), \
                    patch.object(gate, 'supervise', return_value=result):
                self.assertEqual(gate.main(), 1)
            self.assertIs(signal.getsignal(signal.SIGTERM), previous_term)
            report = gate.read(root / 'build/tt-buffered/netlist/timeout-test/report.json')
            self.assertEqual(report['status'], 'timed_out')
            self.assertFalse(report['inputs_unchanged'])

    def test_sigterm_supervisor_records_interruption_and_cleans_owned_descendant(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            pid_file = root / 'descendant.pid'
            fixture_runner = root / 'supervisor.py'
            worker_code = '''import signal, subprocess, sys, time
from pathlib import Path
child = subprocess.Popen([sys.executable, '-c', 'import time; time.sleep(30)'])
def stop(*_):
    child.wait(timeout=2)
    sys.exit(0)
signal.signal(signal.SIGTERM, stop)
Path(sys.argv[1]).write_text(str(child.pid))
time.sleep(30)
'''
            fixture_runner.write_text('''import importlib.util, sys
from pathlib import Path
sys.path.insert(0, sys.argv[1])
spec = importlib.util.spec_from_file_location('mapped_gate', Path(sys.argv[1])/'check-tt-buffered-netlist.py')
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)
gate.ROOT = Path(sys.argv[2])
supervise = gate.supervise
pid_file = sys.argv[3]
sys.argv = ['gate', '--netlist', 'unused.nl.v', '--validation', 'unused.json',
            '--macro-root', 'unused', '--tag', 'sigterm-test']
# Capture the fixture argument before main constructs its ordinary CLI argv.
gate.supervise = lambda argv, out, timeout: supervise([sys.executable, '-c', ''' +
                                      repr(worker_code) + ''', pid_file], out, timeout)
gate.main()
''')
            supervisor = subprocess.Popen([sys.executable, fixture_runner, ROOT / 'scripts', root, pid_file],
                                          stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                          text=True, start_new_session=True)
            descendant = None
            try:
                deadline = time.monotonic() + 5
                while not pid_file.exists() and supervisor.poll() is None and time.monotonic() < deadline:
                    time.sleep(0.01)
                self.assertTrue(pid_file.exists(), 'Owned descendant fixture did not start')
                descendant = int(pid_file.read_text())
                supervisor.send_signal(signal.SIGTERM)
                supervisor.communicate(timeout=5)
                report = gate.read(root / 'build/tt-buffered/netlist/sigterm-test/report.json')
                self.assertEqual(report['status'], 'interrupted')
                self.assertFalse(report['inputs_unchanged'])
                self.assertTrue(report['supervision']['process_group_stopped'])
                for pid in (descendant, report['supervision']['process_group']):
                    with self.assertRaises(ProcessLookupError):
                        os.kill(pid, 0)
            finally:
                if supervisor.poll() is None:
                    supervisor.kill()
                    supervisor.communicate(timeout=3)
                if descendant is not None:
                    try:
                        os.kill(descendant, signal.SIGKILL)
                    except ProcessLookupError:
                        pass

    def test_more_than_900_seconds_is_rejected_before_launch(self):
        args = ['gate', '--netlist', 'nl.v', '--validation', 'gate.json',
                '--macro-root', 'models', '--tag', 'invalid', '--timeout-seconds', '901']
        with patch.object(sys, 'argv', args), patch.object(gate, 'supervise') as run:
            with self.assertRaises(SystemExit) as error:
                gate.main()
            self.assertEqual(error.exception.code, 2)
            run.assert_not_called()


if __name__ == '__main__':
    unittest.main()
