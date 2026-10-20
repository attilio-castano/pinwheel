"""Pure refusal controls for actual-SV public-wire mutation evidence."""
from copy import deepcopy
import hashlib
from pathlib import Path
import struct
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
from streaming_ready_peers import expected_rx, payloads
from streaming_ready_transport import pack_read
from streaming_ready_wire_cases import packed
from streaming_ready_wire_controls import (CONTROL_NAMES, SCHEMA, check_controls, mutate_core,
    prepare_controls, wire_events)


SV = """module core;
always @(posedge clk) begin
  r_stage1 <= _GEN_1 ? 2'h0 : raw_inputs;
  r_stage2 <= _GEN_1 ? 2'h0 : r_stage1;
  r_current_word <= _GEN_86 ? 64'h2 : _GEN_204 ? _GEN_182 : r_current_word;
end
endmodule
"""


def fixture():
    raw = expected_rx(pack_read(0x52, 64), payloads()[1])[:11]
    records = []
    for index, name in enumerate(CONTROL_NAMES):
        observed = dict(physical_edges=3000, fault=True, retained=True, captured_bits=11,
            physical_data_rises=12, owner_tag=65537, tx_accepted=32,
            rx_sha256=hashlib.sha256(packed(raw)).hexdigest(), prefix_acknowledged=True,
            unused_tx_release_refused=True, warm_cancelled=True,
            deadline_alignment=dict(slot=11, expected_stage2_ready=132, expected_last_poll=131, first_raw_high=130),
            deadline_trace=dict(measured_first_raw_high=130))
        mutation = None if not index else dict(changed_drivers=1, operation='actual driver change',
            candidate_sha256='2' * 64, executable_sha256='3' * 64,
            source_sha256={name: '1' * 64 for name in ('core.sv', 'frontend.sv', 'package.sv', 'tt.sv', 'bridge.sv')})
        value = dict(native_exit_code=0, oracle_rejected=index != 0,
            error="RuntimeError('I2C oracle detected mutation')" if index else None,
            observation=observed, trace=dict(edges=3000, bytes=60000, sha256='1' * 64))
        records.append(dict(name=name, passed=True, expected_rejection=index != 0,
            profile='varying' if index == 2 else 'late', mutation=mutation, result=value))
    return dict(schema=SCHEMA, passed=True, depth=2, controls=records, physical_edges=9000)


class ReadyWireControlTests(unittest.TestCase):
    def test_mutations_change_one_exact_actual_driver(self):
        one, description = mutate_core(SV, 'sampler-stage')
        self.assertIn("r_stage2 <= _GEN_1 ? 2'h0 : raw_inputs;", one)
        self.assertIn("r_stage1 <= _GEN_1 ? 2'h0 : raw_inputs;", one)
        self.assertIn('second sampler', description)
        guard, _ = mutate_core(SV, 'guard-bypass')
        self.assertIn("_GEN_204 ? (_GEN_182 & 64'hbfffffffffffffff) : r_current_word;", guard)
        self.assertIn("r_stage2 <= _GEN_1 ? 2'h0 : r_stage1;", guard)
        self.assertEqual(len(one.splitlines()), len(SV.splitlines()))

    def test_missing_or_ambiguous_sv_shape_refused(self):
        for text in ('module x; endmodule', SV + SV):
            for name in ('sampler-stage', 'guard-bypass'):
                with self.assertRaises(RuntimeError): mutate_core(text, name)
        with self.assertRaises(ValueError): mutate_core(SV, 'unknown')

    def test_native_build_uses_mutated_core_and_all_four_original_ports(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            original = root / 'original'
            original.mkdir()
            sources = [original / name for name in ('core.sv', 'frontend.sv', 'package.sv', 'tt.sv', 'bridge.sv')]
            for path in sources: path.write_text(SV if path.name == 'core.sv' else path.name)
            commands, frozen = [], []
            def run(argv, label):
                commands.append(list(map(str, argv)))
                Path(argv[argv.index('-o') + 1]).write_bytes(b'fake native executable; not qualification')
            result = prepare_controls(sources, root / 'mutants', {'iverilog': '/selected/iverilog'}, run,
                freeze=lambda paths: frozen.extend(map(str, paths)))
            self.assertEqual(set(result), {'sampler-stage', 'guard-bypass'})
            self.assertEqual(len(commands), 2)
            for command in commands:
                self.assertEqual(command[0], '/selected/iverilog')
                self.assertEqual(command[-4:], list(map(str, sources[1:])))
                self.assertNotEqual(command[-5], str(sources[0]))
            self.assertEqual(sources[0].read_text(), SV)
            self.assertEqual(len(frozen), 9)

    def test_native_crash_or_compile_failure_is_not_oracle_rejection(self):
        check_controls(fixture())
        for index in range(3):
            value = fixture()
            value['controls'][index]['result']['native_exit_code'] = 1
            with self.assertRaises(RuntimeError): check_controls(value)
        value = fixture()
        value['controls'][1]['result']['error'] = 'native timeout'
        with self.assertRaises(RuntimeError): check_controls(value)

    def test_wrong_outcome_prefix_owner_and_late_raw_window_refused(self):
        for name, changed in (('captured_bits', 12), ('fault', False), ('owner_tag', 65538),
                ('unused_tx_release_refused', False)):
            value = fixture()
            value['controls'][0]['result']['observation'][name] = changed
            with self.assertRaises(RuntimeError): check_controls(value)
        value = fixture()
        value['controls'][0]['result']['observation']['deadline_trace']['measured_first_raw_high'] += 1
        with self.assertRaises(RuntimeError): check_controls(value)

    def test_unchanged_mutant_reordered_or_missing_controls_refused(self):
        value = fixture()
        value['controls'][1]['mutation']['candidate_sha256'] = '1' * 64
        with self.assertRaises(RuntimeError): check_controls(value)
        for records in (fixture()['controls'][:-1], list(reversed(fixture()['controls']))):
            value = fixture()
            value['controls'] = records
            with self.assertRaises(RuntimeError): check_controls(value)

    def test_trace_counts_and_aggregate_must_match(self):
        value = fixture()
        value['physical_edges'] += 1
        with self.assertRaises(RuntimeError): check_controls(value)
        value = fixture()
        value['controls'][2]['result']['trace']['bytes'] -= 20
        with self.assertRaises(RuntimeError): check_controls(value)

    def test_measured_rises_include_the_failing_decoder_event(self):
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / 'wire.bin'
            wires = [3, 1, 0, 1, 0, 1, 3]
            rows = []
            for cycle, wire in enumerate(wires, 1):
                fields = [cycle, *([0] * 16)]
                fields[14] = wire
                rows.append(struct.pack('<I16B', *fields))
            path.write_bytes(b''.join(rows))
            self.assertEqual(wire_events(path), dict(resolved_start_events=1, resolved_stop_events=1,
                resolved_scl_rises_after_start=2))
            path.write_bytes(path.read_bytes()[:-1])
            with self.assertRaises(RuntimeError): wire_events(path)


if __name__ == '__main__': unittest.main()
