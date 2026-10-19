"""Pure distinguishing receipt controls, not Icarus or hardware qualification."""
from copy import deepcopy
from dataclasses import asdict
import hashlib
from pathlib import Path
import sys
import struct
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
from streaming_ready_compile import i2c_image
from streaming_ready_peers import expected_rx, payloads
from streaming_ready_transport import pack_read, pack_write, project
from streaming_ready_wire_cases import PROFILES, SCHEMA, audit_deadline_trace, check_i2c_cases, packed
from streaming_transport import Code, Receipt


def fixture(depth=2):
    """Synthetic contract data; it has no executable/RTL acceptance status."""
    write, read = payloads()
    image, cases = i2c_image(), []
    for direction in ('read', 'write'):
        plan = pack_read(0x52, 64) if direction == 'read' else pack_write(0x52, write)
        for profile in PROFILES:
            timeout, nack = profile == 'timeout', profile == 'address_nack'
            raw = expected_rx(plan, read, address_ack=not nack)[:50 if timeout else 585]
            projection = asdict(project(plan, raw, fault=timeout))
            projection['data_hex'] = projection.pop('data').hex()
            peer = dict(stream_slots=585, captured_prefix_bits=len(raw), start_count=1,
                address_ack=not nack, aborted=timeout, host_low_extra_edges=10,
                physical_data_rises=len(raw), stop_count=0 if timeout else 1,
                stop_preparation_rises=0 if timeout else 1, direction=direction,
                profile='clean' if nack else profile, low_cycles=4, high_cycles=4, wait_budget=31,
                low_min_edges=5, high_phase_edges=[7], callback_delay_cycles=1, sampler_delay_cycles=2,
                target_stretch_edges=0 if profile in ('clean', 'address_nack') else 20,
                stretches=[dict(slot=585, stimulus='resolved fall timer')] if profile == 'varying' else [])
            if profile == 'lastpoll':
                peer['deadline_alignment'] = dict(slot=11, master_release=100, release_callback=128,
                    first_raw_high=129, expected_stage2_ready=131, expected_last_poll=131,
                    access='public SCL output-enable transition')
                peer['deadline_trace'] = dict(public_master_release=100, target_release_callback=128,
                    measured_first_raw_high=129, fresh_low_raw_edges_before_release=3, independent_sda_stable_raw_edges=4)
            receipts = [asdict(Receipt(8, Code.ACCEPTED, tag=65537, tx_free=depth, flags=3))]
            accepted = 96 if timeout else 585
            if timeout:
                receipts += [asdict(Receipt(10, Code.ACCEPTED, tag=65537, tx_accepted=96,
                    rx_start=32, rx_valid=18, data=1, tx_free=depth - 1, flags=13)),
                    asdict(Receipt(11, Code.ACCEPTED, tag=65537, tx_accepted=96,
                        rx_start=50, tx_free=depth - 1, flags=13)),
                    asdict(Receipt(12, Code.REJECTED, tag=65537, tx_accepted=96,
                        rx_start=50, tx_free=depth - 1, flags=29)),
                    asdict(Receipt(13, Code.ACCEPTED, tag=65537, tx_free=depth, flags=0))]
                cleanup = dict(fault_prefix_acknowledged=True, unused_tx_release_refused=True, warm_cancelled=True)
            else:
                receipts += [asdict(Receipt(40, Code.ACCEPTED, tag=65537, tx_free=depth, flags=1))]
                cleanup = dict(matching_release=True)
            value = hashlib.sha256(packed(raw)).hexdigest()
            cases.append(dict(passed=True, depth=depth, direction=direction, profile=profile,
                address=0x52, payload_bytes=64, stream_cells=585, owner_tag=65537, starts=1,
                tx_accepted=accepted, captured_bits=len(raw), actual_rx_sha256=value, expected_rx_sha256=value,
                image_words=list(image.words), image_certificate=asdict(image.certificate),
                peer=peer, projection=projection, cleanup=cleanup, receipts=receipts,
                physical_edges=10000, trace=dict(edges=10000, bytes=200000, sha256='1' * 64)))
    return dict(schema=SCHEMA, passed=True, depth=depth, cases=cases, physical_edges=100000)


class ReadyWireContracts(unittest.TestCase):
    def test_actual_deadline_raw_window_and_release_are_checked(self):
        alignment = dict(master_release=5, release_callback=9)
        def make_rows():
            rows = []
            for cycle in range(1, 14):
                values = [cycle, *([0] * 16)]
                values[6] = 1 if cycle <= 9 else 0
                values[13] = 1 if cycle < 5 else 0
                values[14] = 0 if cycle <= 9 else 1
                values[16] = 2 | (0 if cycle <= 9 else 1)
                rows.append(values)
            return rows
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / 'wire.bin'
            def write(rows): path.write_bytes(b''.join(struct.pack('<I16B', *row) for row in rows))
            rows = make_rows()
            write(rows)
            self.assertEqual(audit_deadline_trace(path, alignment, True)['measured_first_raw_high'], 10)
            for index, field in ((4, 13), (7, 16), (9, 6), (8, 16)):
                rows = make_rows()
                rows[index][field] ^= 1 if field != 16 or index == 7 else 2
                write(rows)
                with self.assertRaises(RuntimeError): audit_deadline_trace(path, alignment, True)

    def test_both_ten_case_contracts_and_json_shaped_prefixes(self):
        for depth in (2, 4): check_i2c_cases(fixture(depth))

    def test_missing_reordered_or_duplicated_matrix_refused(self):
        for change in ('missing', 'reordered', 'duplicate'):
            value = fixture()
            if change == 'missing': value['cases'].pop()
            elif change == 'reordered': value['cases'].reverse()
            else: value['cases'][-1] = deepcopy(value['cases'][0])
            with self.assertRaises(RuntimeError): check_i2c_cases(value)

    def test_equal_reported_hashes_do_not_replace_independent_payload(self):
        value = fixture()
        value['cases'][0]['actual_rx_sha256'] = value['cases'][0]['expected_rx_sha256'] = '0' * 64
        with self.assertRaisesRegex(RuntimeError, 'independent payload'): check_i2c_cases(value)

    def test_changed_compiled_word_certificate_or_raw_projection_refused(self):
        for field in ('word', 'certificate', 'projection'):
            value = fixture()
            case = value['cases'][0]
            if field == 'word': case['image_words'][0] ^= 1
            elif field == 'certificate': case['image_certificate']['source_sha256'] = '0' * 64
            else: case['projection']['raw_bits'] = (False,) * 585
            with self.assertRaises(RuntimeError): check_i2c_cases(value)

    def test_address_nack_cannot_be_relabelled_successful_read_payload(self):
        value = fixture()
        case = next(case for case in value['cases'] if case['profile'] == 'address_nack')
        case['projection']['payload_valid'] = True
        case['projection']['data_hex'] = 'ff' * 64
        with self.assertRaises(RuntimeError): check_i2c_cases(value)

    def test_fault_partial_and_actual_cleanup_receipts_required(self):
        for change in ('partial', 'release', 'cancel'):
            value = fixture()
            case = next(case for case in value['cases'] if case['profile'] == 'timeout')
            if change == 'partial': case['receipts'][1]['rx_valid'] = 17
            elif change == 'release': case['receipts'][-2]['flags'] = 13
            else: case['receipts'][-1]['tx_accepted'] = 96
            with self.assertRaises(RuntimeError): check_i2c_cases(value)

    def test_owner_and_actual_release_not_just_boolean_claims(self):
        for change in ('owner', 'release'):
            value = fixture()
            case = value['cases'][0]
            if change == 'owner': case['receipts'][-1]['tag'] += 1
            else: case['receipts'][-1]['flags'] = 5
            with self.assertRaises(RuntimeError): check_i2c_cases(value)

    def test_deadline_alignment_stretch_coverage_and_high_timing_required(self):
        for change in ('deadline', 'stretch', 'high', 'stop_stretch'):
            value = fixture()
            case = next(case for case in value['cases'] if case['profile'] == 'lastpoll')
            if change == 'deadline': case['peer']['deadline_alignment']['expected_stage2_ready'] += 1
            elif change == 'stretch': case['peer']['target_stretch_edges'] = 0
            elif change == 'high': case['peer']['high_phase_edges'] = [8]
            else:
                case = next(case for case in value['cases'] if case['profile'] == 'varying')
                case['peer']['stretches'] = []
            with self.assertRaises(RuntimeError): check_i2c_cases(value)

    def test_trace_edge_and_aggregate_counts_cannot_drift(self):
        for change in ('trace', 'aggregate'):
            value = fixture()
            if change == 'trace': value['cases'][0]['trace']['bytes'] += 1
            else: value['physical_edges'] += 1
            with self.assertRaises(RuntimeError): check_i2c_cases(value)


if __name__ == '__main__': unittest.main()
