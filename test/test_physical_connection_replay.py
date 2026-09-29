"""Exercise the committed diagnostic replay command, including absent SRAM bounds."""
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from test_physical_connections import REPORT, fixture


ROOT = Path(__file__).resolve().parents[1]
STD = '''library (std) { capacitive_load_unit (1,pf); default_max_fanout : 8;
    cell (sg13cmos5l_buf_1) { pin (X) { direction : output; } } }'''
MACRO = '''library (sram) { capacitive_load_unit (1,pf); default_fanout_load : 1;
    cell (RM_IHP) { bus (A_DOUT) { direction : output; max_capacitance : .4;
        pin (A_DOUT[63:0]) { related_power_pin : VDD; } } } }'''
NAMES = ['n', 'memory.mem_q0[51]', 'memory.mem_q0[53]']


class ConnectionReplay(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.directory = Path(self.tmp.name)
        context, _ = fixture()
        context['nets']['n']['ports'] = []
        raw, rows = '', {}
        for name, driver in zip(NAMES, ['d/X', 'memory/A_DOUT[51]', 'memory/A_DOUT[53]']):
            block = REPORT.replace('PINWHEEL_CONNECTION n\nNet n\n',
                'PINWHEEL_CONNECTION '+name+'\nNet '+name+'\n').replace('d/X', driver)
            fanout = dict(pin=driver, limit=8., actual=1., slack=7., verdict='MET')
            if name != 'n':
                block = block.replace('max fanout\n'+driver+' 8 1 7 (MET)\n', '')
                fanout = None
                inst, pin = driver.rsplit('/', 1)
                context['nets'][name] = dict(type='SIGNAL', ports=[], terminals=[
                    dict(instance=inst, pin=pin, direction='OUTPUT'),
                    dict(instance='q', pin='D', direction='INPUT')])
            raw += block
            # Independent expected values; do not construct the oracle with the parser.
            rows[name] = dict(pin_cap_pf=[.02,.03], wire_cap_pf=[.3,.3], total_cap_pf=[.32,.33],
                drivers=1, loads=1, fanout=fanout,
                slew=dict(pin=driver, limit=.5, actual=.6, slack=-.1, verdict='VIOLATED'),
                capacitance=dict(pin=driver, limit=.4, actual=.33, slack=.07, verdict='MET'),
                paths={k:dict(startpoint='s', endpoint='q', slack_ns=v, verdict='MET', cells=[])
                    for k,v in [('min',.08),('max',.4)]})
        self.raw, self.context = raw, context
        self.saved = {c:deepcopy(rows) for c in ('fast','slow','typ')}
        self.request = dict(schema=1, context=self.write('context.json', json.dumps(context)),
            sdc=self.write('comparison.sdc', (ROOT/'physical/chip.sdc').read_text()),
            measurements=self.write('measurements.json', json.dumps(self.saved)), connections=NAMES,
            corners={c:dict(libraries=[self.write('std.lib', STD),self.write('macro.lib', MACRO)],
                report=self.write(c+'.rpt', raw)) for c in self.saved})

    def write(self, name, text):
        data = text.encode()
        (self.directory/name).write_bytes(data)
        return dict(path=name, sha256=hashlib.sha256(data).hexdigest())

    def invoke(self):
        (self.directory/'request.json').write_text(json.dumps(self.request))
        return subprocess.run([sys.executable, '-B', str(ROOT/'scripts/replay-physical-connections.py'),
            '--request', 'request.json', '--output', 'receipt.json'], cwd=self.directory,
            text=True, capture_output=True, timeout=15)

    def reject(self, message):
        result = self.invoke()
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn(message, result.stderr)
        self.assertFalse((self.directory/'receipt.json').exists())

    def test_command_replays_mixed_drivers_and_preserves_unknowns_without_qualification(self):
        before = {p.name:p.read_bytes() for p in self.directory.iterdir()}
        result = self.invoke()
        self.assertEqual(result.returncode, 0, result.stderr)
        receipt = json.loads(result.stdout)
        self.assertTrue(receipt['measurements_equal'])
        self.assertEqual(receipt['connection_corner_records'], 9)
        self.assertEqual(receipt['unreported_macro_fanout_limits'], {c:NAMES[1:] for c in self.saved})
        self.assertFalse(receipt['physical_qualification'])
        self.assertTrue(all((self.directory/n).read_bytes()==b for n,b in before.items()))
        saved_receipt = (self.directory/'receipt.json').read_bytes()
        result = self.invoke()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('FileExistsError', result.stderr)
        self.assertEqual((self.directory/'receipt.json').read_bytes(), saved_receipt)

    def test_standard_cell_absence_is_rejected_even_with_two_allowed_macro_absences(self):
        self.request['corners']['slow']['report'] = self.write('slow.rpt',
            self.raw.replace('max fanout\nd/X 8 1 7 (MET)\n', ''))
        self.reject('Missing electrical measurement')

    def test_pin_bus_bit_and_library_default_constraints_require_a_report(self):
        variants = [MACRO.replace('direction : output;', 'direction : output; max_fanout : 4;'),
            MACRO.replace('related_power_pin : VDD;', 'related_power_pin : VDD; max_fanout : 4;'),
            MACRO.replace('pin (A_DOUT[63:0])', 'pin (A_DOUT[51]) { max_fanout : 4; } pin (A_DOUT[63:0])'),
            MACRO.replace('default_fanout_load : 1;', 'default_fanout_load : 1; default_max_fanout : 4;'),
            MACRO.replace('direction : output;', 'direction : output; max_fanout : invalid;')]
        for text in variants:
            with self.subTest(lib=text):
                self.request['corners']['slow']['libraries'][1] = self.write('changed.lib', text)
                self.reject('Missing electrical measurement')

    def test_unknown_or_fanout_constrained_sdc_does_not_allow_absent_limits(self):
        for extra in ['\nset_max_fanout 4 [current_design]\n', '\nsource other.sdc\n']:
            with self.subTest(extra=extra):
                self.request['sdc'] = self.write('changed.sdc', (ROOT/'physical/chip.sdc').read_text()+extra)
                self.reject('Missing electrical measurement')

    def test_required_sections_and_malformed_present_fanout_remain_errors(self):
        for bad, message in [(self.raw.replace('max slew\n', 'absent slew\n'), 'Missing electrical measurement'),
            (self.raw.replace('max capacitance\n', 'absent cap\n'), 'Missing electrical measurement'),
            (self.raw.replace('max capacitance\nmemory/A_DOUT[51]',
                'max fanout\nmalformed row\nmax capacitance\nmemory/A_DOUT[51]'), 'Missing electrical limit/slack')]:
            with self.subTest(message=message):
                self.request['corners']['fast']['report'] = self.write('fast.rpt', bad)
                self.reject(message)

    def test_macro_flag_cannot_override_a_missing_or_changed_library_driver(self):
        for change, message in [
            (lambda c:c['instances']['memory'].update(macro=False), 'Missing electrical measurement'),
            (lambda c:c['instances']['memory'].update(cell='other'), 'Unresolved Liberty cell'),
            (lambda c:c['nets'][NAMES[1]]['terminals'][0].update(pin='A_DOUT[50]'),
                'Diagnostic measurement differs from physical connection')]:
            with self.subTest(message=message):
                context = deepcopy(self.context); change(context)
                self.request['context'] = self.write('changed-context.json', json.dumps(context))
                self.reject(message)

    def test_changed_hash_missing_corner_and_different_saved_value_are_rejected(self):
        ref = self.request['corners']['fast']['report']
        original = ref['sha256']; ref['sha256'] = '0'*64
        self.reject('Changed replay input')
        ref['sha256'] = original
        corners = self.request['corners'].copy(); self.request['corners'].pop('slow')
        self.reject('Replay corners differ')
        self.request['corners'] = corners
        self.saved['fast'][NAMES[1]]['loads'] = 2
        self.request['measurements'] = self.write('measurements.json', json.dumps(self.saved))
        self.reject('Replayed measurement differs from saved result')

    def test_measured_macro_fanout_is_retained_when_present(self):
        raw = self.raw.replace('max capacitance\nmemory/A_DOUT[51]',
            'max fanout\nmemory/A_DOUT[51] 4 1 3 (MET)\nmax capacitance\nmemory/A_DOUT[51]')
        self.request['corners']['slow']['report'] = self.write('slow.rpt', raw)
        self.saved['slow'][NAMES[1]]['fanout'] = dict(pin='memory/A_DOUT[51]', limit=4., actual=1., slack=3., verdict='MET')
        self.request['measurements'] = self.write('measurements.json', json.dumps(self.saved))
        result = self.invoke()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(json.loads(result.stdout)['unreported_macro_fanout_limits']['slow'], [NAMES[2]])


if __name__ == '__main__':
    unittest.main()
