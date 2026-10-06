"""Reject incomplete or corrupted evidence at the independent hardware boundary."""
from copy import deepcopy
import importlib.util
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
spec = importlib.util.spec_from_file_location('buffered_reactive_hardware_gate',
                                            ROOT / 'scripts/check-buffered-reactive-hardware.py')
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)


def fixture():
    state = dict(valid=0, busy=0, retained=0, pending=0, rejected=0, mode=0,
        pc=0, remaining=0, levels=0, enabled=0, tx_consumed=0, rx_length=0,
        rx_data=0, read_valid=0, read_bit=0, generation=0, transfer=0,
        exhausted=0, stage1=0, stage2=0, virtual_pc=0, env0=0, env1=0, phase=0,wait_left=0,scratch=0)
    commands = [dict(command=dict(initialize=1), raw_inputs=1),
                dict(command=dict(command=0), raw_inputs=2),
                dict(command=dict(command=7), raw_inputs=3)]
    states = [state, dict(state, stage1=2), dict(state, generation=1)]
    request = dict(schema='pinwheel-buffered-reactive-hardware-input-v1', cases=[dict(
        name='cold-sampler-warm', vectors=deepcopy(commands), checks=[
            dict(edge=0, state=dict(generation=0, transfer=0, retained=0, busy=0)),
            dict(edge=1, state=dict(stage1=2, stage2=0)),
            dict(edge=2, state=dict(generation=1, stage1=0, stage2=0))])])
    exported = dict(schema='pinwheel-buffered-reactive-hardware-vectors-v1', cases=[dict(
        name='cold-sampler-warm', vectors=[dict(command=command['command'],
            raw_inputs=command['raw_inputs'], state=deepcopy(snapshot))
            for command, snapshot in zip(commands, states, strict=True)])])
    return request, exported


class BufferedReactiveHardwareExportTests(unittest.TestCase):
    def test_complete_independent_command_checks_are_counted(self):
        request, exported = fixture()
        report = gate.check_export(request, exported)
        self.assertEqual((report['cases'], report['edges'], report['independent_state_checks']),
                         (1, 3, 3))

    def test_wrong_schema_missing_case_or_missing_edge_is_rejected(self):
        for mutate in (lambda obj: obj.update(schema='unknown'),
                       lambda obj: obj['cases'].clear(),
                       lambda obj: obj['cases'][0]['vectors'].pop()):
            request, exported = fixture()
            mutate(exported)
            with self.assertRaises(RuntimeError): gate.check_export(request, exported)

    def test_changed_case_name_or_input_transcript_is_rejected(self):
        for mutate in (lambda obj: obj['cases'][0].update(name='other-case'),
                       lambda obj: obj['cases'][0]['vectors'][1].update(raw_inputs=3),
                       lambda obj: obj['cases'][0]['vectors'][0]['command'].update(initialize=0),
                       lambda obj: obj['cases'][0]['vectors'][1]['command'].update(address=1)):
            request, exported = fixture()
            mutate(exported)
            with self.assertRaises(RuntimeError): gate.check_export(request, exported)

    def test_independent_sampler_reset_or_identity_observation_cannot_change(self):
        for edge, field, value in ((0, 'generation', 1), (0, 'transfer', 1),
                                  (0, 'retained', 1), (0, 'busy', 1),
                                  (1, 'stage1', 3), (1, 'stage2', 1),
                                  (2, 'generation', 0), (2, 'stage1', 3)):
            request, exported = fixture()
            exported['cases'][0]['vectors'][edge]['state'][field] = value
            with self.subTest(edge=edge, field=field), self.assertRaises(RuntimeError):
                gate.check_export(request, exported)

    def test_boolean_or_float_aliases_cannot_replace_integer_port_values(self):
        for mutate in (
                lambda obj: obj['cases'][0]['vectors'][0]['command'].update(initialize=True),
                lambda obj: obj['cases'][0]['vectors'][0].update(raw_inputs=True),
                lambda obj: obj['cases'][0]['vectors'][0]['state'].update(generation=False),
                lambda obj: obj['cases'][0]['vectors'][1]['state'].update(stage1=2.0),
                lambda obj: obj['cases'][0]['vectors'][1]['command'].update(command=0.0)):
            request, exported = fixture()
            mutate(exported)
            with self.assertRaises(RuntimeError): gate.check_export(request, exported)

    def test_every_public_state_field_is_required_and_width_checked(self):
        for mutate in (
                lambda state: state.pop('rx_data'),
                lambda state: state.update(extra=0),
                lambda state: state.update(pc=256),
                lambda state: state.update(rx_data=1 << 32),
                lambda state: state.update(read_bit=-1),
                lambda state: state.update(virtual_pc=1024),
                lambda state: state.update(env0=8),
                lambda state: state.pop('env1'),
                lambda state: state.update(phase=8),
                lambda state: state.update(wait_left=256),
                lambda state: state.update(scratch=65536)):
            request, exported = fixture()
            mutate(exported['cases'][0]['vectors'][1]['state'])
            with self.assertRaises(RuntimeError): gate.check_export(request, exported)


if __name__ == '__main__':
    unittest.main()
