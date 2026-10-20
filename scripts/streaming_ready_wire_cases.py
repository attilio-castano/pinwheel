"""Public-pin I2C corpus for the separate sampled-ready RTL target.

The peer supplies data from a fixed external plan and sees resolved pads only,
with declared public OE access for deadline alignment. Exact source TX-consumed
counters are not wire observations. Every case retains its complete edge trace.
"""
from dataclasses import asdict
import hashlib
import json
from pathlib import Path
import re
import struct
import time

from streaming_ready_compile import i2c_image, lean_certificate, validate_image
from streaming_ready_peers import StreamingI2cPeer, expected_rx, payloads
from streaming_ready_transport import ReadyHost, pack_read, pack_write, project
from streaming_rtl import QuadRTL
from streaming_transport import Code, Opcode, QuadTransport, Receipt
from streaming_wire_cases import EdgeTrace


SCHEMA = 'pinwheel.streaming-ready-i2c-wire.v1'
PROFILES = ('clean', 'varying', 'lastpoll', 'timeout', 'address_nack')


def require(value, message):
    if not value:
        raise RuntimeError(message)


def write_json(path, value):
    Path(path).write_text(json.dumps(value, indent=2) + '\n')


def packed(bits):
    result = bytearray((len(bits) + 7) // 8)
    for index, value in enumerate(bits): result[index // 8] |= int(value) << (7 - index % 8)
    return bytes(result)


def audit_deadline_trace(path, alignment, expected_bit):
    """Check actual pre-edge raw samples separately from predicted stage2 time."""
    data = Path(path).read_bytes()
    require(len(data) % 20 == 0, 'Truncated I2C public-edge trace')
    rows = {row[0]: row for row in struct.iter_unpack('<I16B', data)}
    require(sorted(rows) == list(range(1, len(data) // 20 + 1)), 'I2C trace cycles are ambiguous or discontinuous')
    release, callback = alignment['master_release'], alignment['release_callback']
    require(release >= 3 and callback + 3 <= len(rows), 'Deadline trace lacks its complete sampling window')
    require(rows[release - 1][13] & 1 and not rows[release][13] & 1,
        'Deadline stimulus did not observe the actual public SCL-OE release transition')
    require(all(not rows[index][16] & 1 for index in range(release - 2, callback + 1)),
        'Deadline fixture has stale HIGH or unexpected pre-edge SCL readiness')
    require(rows[callback][6] & 1 and not rows[callback + 1][6] & 1 and
        rows[callback + 1][16] & 1 and not rows[callback][14] & 1 and rows[callback + 1][14] & 1,
        'Actual target release, first raw HIGH or resolved SCL rise differs from callback chronology')
    require(all(bool(rows[index][16] & 2) is expected_bit for index in range(callback - 2, callback + 2)),
        'Independent SDA bit was not stable before the deadline SCL release')
    return dict(public_master_release=release, target_release_callback=callback,
        measured_first_raw_high=callback + 1, fresh_low_raw_edges_before_release=3,
        independent_sda_stable_raw_edges=4,
        stage2_scope='Stage2 readiness time is the explicit two-register sampling contract, not a private-state observation')


def run_i2c_case(vvp, executable, directory, *, depth, direction, profile):
    if depth not in (2, 4) or direction not in ('read', 'write') or profile not in PROFILES:
        raise ValueError('Expected one declared Ready I2C depth/direction/profile')
    directory = Path(directory)
    directory.mkdir(parents=True, exist_ok=False)
    write_data, read_data = payloads()
    plan = pack_read(0x52, 64) if direction == 'read' else pack_write(0x52, write_data)
    image = i2c_image()
    validate_image(image)
    stream = image.source.instructions[image.certificate.stream_row]
    address_ack = profile != 'address_nack'
    peer_profile = profile if address_ack else 'clean'
    expected = expected_rx(plan, read_data, address_ack=address_ack)
    expected_count = 50 if profile == 'timeout' else 585
    (directory / 'tx-slots.bin').write_bytes(packed(plan.tx_bits))
    (directory / 'expected-rx-slots.bin').write_bytes(packed(expected[:expected_count]))
    (directory / 'write-payload.bin').write_bytes(write_data)
    (directory / 'read-target-payload.bin').write_bytes(read_data)
    (directory / 'image-certificate.lean').write_text(lean_certificate(image))
    trace = EdgeTrace(directory / 'wire.bin')
    started, receipts, pending, peer, rtl = time.monotonic(), [], None, None, None
    try:
        with QuadRTL(vvp, executable, record_sink=trace) as rtl:
            transport = QuadTransport(rtl)
            host = ReadyHost(transport, depth=depth)
            host.initialize()
            loaded = host.load(image)
            peer = StreamingI2cPeer(plan, read_data, address_ack=address_ack, profile=peer_profile,
                low_cycles=stream.cell.low_cycles, high_cycles=stream.cell.high_cycles,
                wait_budget=stream.guard.limit.budget)
            rtl.device = peer
            pending = loaded.submit(plan.tx_bits, bit_count=plan.bit_count)
            receipts.append(asdict(pending.last))
            # This delays only the host. The target has not armed an SCL hold
            # yet, so the trace distinguishes an actual parked LOW interval.
            transport.idle(64)
            pending.pump(max_bits=32 if profile == 'lastpoll' else 64)
            receipts.append(asdict(pending.last))
            for _ in range(100):
                if pending.last.retained and not pending.last.rx_queued and (
                        pending.last.fault or len(pending.rx_bits) == plan.bit_count):
                    break
                pending.pump()
                receipts.append(asdict(pending.last))
            else:
                raise RuntimeError('I2C public-wire exchange budget expired')
            require(pending.last.fault is (profile == 'timeout'), 'I2C terminal result differs from the planned target hold')
            require(pending.rx_bits == expected[:expected_count], 'I2C host RX differs from the independent external plan')
            require(all(row['rx_valid'] <= 32 for row in receipts), 'Frontend exported more than one RX word')
            projection = project(plan, pending.rx_bits, fault=pending.last.fault)
            require(projection.payload_valid is (profile not in ('timeout', 'address_nack')),
                'I2C host projection silently upgraded a NACK or fault')
            if address_ack:
                require(projection.data == (read_data if direction == 'read' else write_data)[:len(projection.data)],
                    'I2C projected payload bytes differ')
            else:
                require(projection.address_ack is False and projection.data == b'', 'Address NACK returned a payload')
            peer_result = peer.check(pending.rx_bits, fault=profile == 'timeout', require_host_stall=True)
            tag, accepted = pending.tag, pending.tx_accepted
            if profile == 'timeout':
                require(accepted >= 64 and any(row['rx_start'] == 32 and row['rx_valid'] == 18 for row in receipts),
                    'Timeout did not retain the full-word plus18-bit partial RX prefix')
                acknowledged = pending.pump(max_bits=0)
                receipts.append(asdict(acknowledged))
                require(acknowledged.rx_start == 50 and acknowledged.rx_valid == 0 and not acknowledged.rx_queued and
                    acknowledged.tag == tag and acknowledged.tx_accepted == accepted,
                    'Fault prefix acknowledgment changed the owner, RX interval or accepted TX')
                held = transport.request(Opcode.RELEASE, tag=tag)
                receipts.append(asdict(held))
                require(held.code is Code.REJECTED and held.retained and held.fault and held.tx_accepted == accepted,
                    'Matching RELEASE discarded the accepted but unused TX suffix')
                cancelled = host.warm_reset()
                receipts.append(asdict(cancelled))
                require(not cancelled.valid and not cancelled.busy and not cancelled.retained and
                    cancelled.tag == tag and not cancelled.tx_accepted and not cancelled.rx_queued,
                    'Explicit warm cancellation failed to clear custody while retaining allocation IDs')
                cleanup = dict(fault_prefix_acknowledged=True, unused_tx_release_refused=True, warm_cancelled=True,
                    source_reservation_expected=51,
                    reservation_scope='Source-semantic expected reservation count; not a wire receipt field')
            else:
                require(accepted == 585, 'Successful I2C stream did not accept all585 TX slots')
                released = pending.release()
                receipts.append(asdict(released))
                require(released.tag == tag and not released.busy and not released.retained,
                    'Matching I2C RELEASE did not free the same owner')
                cleanup = dict(matching_release=True)
            require(transport.opcode_counts[Opcode.START] == 1, 'I2C used more than one START')
            (directory / 'actual-rx-slots.bin').write_bytes(packed(pending.rx_bits))
            result = dict(passed=True, depth=depth, direction=direction, profile=profile,
                address=plan.address, payload_bytes=64, stream_cells=585, owner_tag=tag,
                starts=1, tx_accepted=accepted, captured_bits=len(pending.rx_bits),
                expected_rx_sha256=hashlib.sha256(packed(expected[:expected_count])).hexdigest(),
                actual_rx_sha256=hashlib.sha256(packed(pending.rx_bits)).hexdigest(),
                image_words=list(image.words), image_certificate=asdict(image.certificate),
                peer=peer_result, projection={**{name: value for name, value in asdict(projection).items()
                    if name != 'data'}, 'data_hex': projection.data.hex()}, cleanup=cleanup,
                terminal_retries=pending.terminal_retries, receipts=receipts,
                requests=transport.transactions, physical_edges=rtl.cycle)
    except Exception as error:
        result = dict(passed=False, depth=depth, direction=direction, profile=profile, error=repr(error),
            receipts=receipts, captured_bits=len(pending.rx_bits) if pending else 0,
            physical_edges=rtl.cycle if rtl else trace.edges,
            peer_progress=dict(captured_physical_rises=len(peer.bits), starts=int(peer.started_at is not None),
                stopped=peer.stopped_at, deadline=peer.deadline_alignment) if peer else None)
    finally:
        record = trace.close()
    if result.get('passed') and profile == 'lastpoll':
        try:
            result['peer']['deadline_trace'] = audit_deadline_trace(directory / 'wire.bin',
                result['peer']['deadline_alignment'], expected[11])
        except Exception as error:
            result.update(passed=False, error=repr(error))
    result.update(trace=record, elapsed_seconds=round(time.monotonic() - started, 6))
    write_json(directory / 'report.json', result)
    return result


def check_i2c_cases(result):
    require(result.get('schema') == SCHEMA and result.get('passed') is True and result.get('depth') in (2, 4),
        'Ready I2C receipt does not claim the declared successful scope')
    expected = [(direction, profile) for direction in ('read', 'write') for profile in PROFILES]
    cases = result.get('cases', [])
    require([(case.get('direction'), case.get('profile')) for case in cases] == expected,
        'Ready I2C matrix is missing, reordered or duplicated')
    write_data, read_data = payloads()
    image = i2c_image()
    for case in cases:
        timeout, nack = case['profile'] == 'timeout', case['profile'] == 'address_nack'
        peer, projection, cleanup = case.get('peer', {}), case.get('projection', {}), case.get('cleanup', {})
        plan = pack_read(0x52, 64) if case['direction'] == 'read' else pack_write(0x52, write_data)
        expected = expected_rx(plan, read_data, address_ack=not nack)[:50 if timeout else 585]
        projected = project(plan, expected, fault=timeout)
        projected_dict = {**{name: value for name, value in asdict(projected).items() if name != 'data'},
            'data_hex': projected.data.hex()}
        require(case.get('passed') is True and case.get('depth') == result['depth'] and case.get('address') == 0x52 and
            case.get('payload_bytes') == 64 and case.get('stream_cells') == 585 and case.get('owner_tag') == 65537 and
            case.get('starts') == 1 and case.get('captured_bits') == (50 if timeout else 585) and
            case.get('actual_rx_sha256') == case.get('expected_rx_sha256') and
            re.fullmatch(r'[0-9a-f]{64}', case.get('actual_rx_sha256', '')),
            'Incomplete I2C owner, payload, prefix or independent RX binding')
        require(case['actual_rx_sha256'] == hashlib.sha256(packed(expected)).hexdigest() and
            case.get('image_words') == list(image.words) and case.get('image_certificate') == asdict(image.certificate) and
            json.loads(json.dumps(projection)) == json.loads(json.dumps(projected_dict)),
            'I2C result is not bound to the fixed independent payload/image/projection')
        require(peer.get('stream_slots') == 585 and peer.get('captured_prefix_bits') == case['captured_bits'] and
            peer.get('start_count') == 1 and peer.get('address_ack') is (not nack) and
            peer.get('aborted') is timeout and peer.get('host_low_extra_edges', 0) > 0 and
            projection.get('payload_valid') is (not timeout and not nack) and projection.get('fault') is timeout,
            'I2C peer/projection chronology, address or fault contract differs')
        require(peer.get('profile') == ('clean' if nack else case['profile']) and peer.get('direction') == case['direction'] and
            peer.get('low_cycles') == 4 and peer.get('high_cycles') == 4 and peer.get('wait_budget') == 31 and
            peer.get('low_min_edges', 0) >= 4 and peer.get('high_phase_edges') and
            all(type(value) is int and 4 <= value <= 7 for value in peer['high_phase_edges']) and
            peer.get('callback_delay_cycles') == 1 and peer.get('sampler_delay_cycles') == 2,
            'I2C timing, profile or declared sampling access differs')
        receipts = case.get('receipts', [])
        require(receipts and receipts[0].get('sequence') == 8, 'I2C did not start after the seven-row upload/COMMIT')
        for row in receipts:
            Receipt(**{**row, 'code': Code(row['code'])})
            require(row['tag'] == case['owner_tag'] and row['tx_free'] <= result['depth'] and
                row['rx_queued'] <= result['depth'], 'I2C receipt changed owner or exceeded queue bounds')
        if timeout:
            require(case.get('tx_accepted', 0) >= 64 and all(cleanup.get(name) is True for name in
                ('fault_prefix_acknowledged', 'unused_tx_release_refused', 'warm_cancelled')) and
                peer.get('physical_data_rises') == 50 and peer.get('stop_count') == 0 and
                any(row.get('rx_start') == 32 and row.get('rx_valid') == 18 for row in case.get('receipts', [])),
                'I2C timeout lost partial RX or unused TX ownership')
            ack, held, cancelled = receipts[-3:]
            require((ack['code'], ack['flags'], ack['rx_start'], ack['rx_valid'], ack['tx_accepted'], ack['rx_queued']) ==
                (0, 13, 50, 0, case['tx_accepted'], 0) and
                (held['code'], held['flags'], held['tx_accepted']) == (5, 29, case['tx_accepted']) and
                (cancelled['code'], cancelled['flags'], cancelled['tx_accepted'], cancelled['rx_queued']) == (0, 0, 0, 0),
                'Actual fault drain, held RELEASE or warm-cancellation receipts differ')
        else:
            require(case.get('tx_accepted') == 585 and cleanup.get('matching_release') is True and
                peer.get('physical_data_rises') == 585 and peer.get('stop_preparation_rises') == 1 and
                peer.get('stop_count') == 1, 'I2C success did not complete its exact clocks and matching RELEASE')
            released = receipts[-1]
            require((released['code'], released['flags'], released['tx_accepted'], released['rx_valid'], released['rx_queued']) ==
                (0, 1, 0, 0, 0), 'Actual matching RELEASE receipt did not establish the free valid slot')
        if case['profile'] in ('varying', 'lastpoll', 'timeout'):
            require(peer.get('target_stretch_edges', 0) > 0, 'I2C stretching fixture did not stretch')
        if case['profile'] == 'lastpoll':
            alignment = peer.get('deadline_alignment') or {}
            measured = peer.get('deadline_trace') or {}
            release, callback = alignment.get('master_release', 0), alignment.get('release_callback', 0)
            require(alignment.get('slot') == 11 and release > 0 and callback == release + 28 and
                alignment.get('first_raw_high') == callback + 1 and alignment.get('expected_stage2_ready') == callback + 3 and
                alignment.get('expected_last_poll') == release + 31 and 'output-enable' in alignment.get('access', ''),
                'Last-poll fixture lacks exact declared sampling chronology')
            require(measured.get('public_master_release') == release and measured.get('target_release_callback') == callback and
                measured.get('measured_first_raw_high') == callback + 1 and
                measured.get('fresh_low_raw_edges_before_release') == 3 and
                measured.get('independent_sda_stable_raw_edges') == 4,
                'Last-poll fixture lacks actual pre-edge raw-input trace verification')
        if case['profile'] == 'varying':
            require(any(row.get('slot') == 585 and row.get('stimulus') == 'resolved fall timer'
                for row in peer.get('stretches', [])), 'Varying I2C case did not include a STOP stretch')
        trace = case.get('trace', {})
        require(case.get('physical_edges', 0) > 0 and trace.get('edges') == case['physical_edges'] and
            trace.get('bytes') == case['physical_edges'] * 20 and re.fullmatch(r'[0-9a-f]{64}', trace.get('sha256', '')),
            'I2C public-edge trace inventory differs')
    require(result.get('physical_edges') == sum(case['physical_edges'] for case in cases), 'I2C aggregate edges differ')


def run_i2c_cases(vvp, executable, directory, *, depth):
    if depth not in (2, 4):
        raise ValueError('Ready I2C qualification depths are2 or4')
    directory = Path(directory)
    directory.mkdir(parents=True, exist_ok=False)
    cases = [run_i2c_case(vvp, executable, directory / (direction + '-' + profile),
        depth=depth, direction=direction, profile=profile)
        for direction in ('read', 'write') for profile in PROFILES]
    result = dict(schema=SCHEMA, passed=all(case['passed'] for case in cases), depth=depth, cases=cases,
        physical_edges=sum(case['physical_edges'] for case in cases),
        boundary='Independent finite resolved-pin I2C traces through the actual public quad link. '
            'Deadline alignment declares public output-enable access. Exact source counters are not wire observations. '
            'No electrical, multi-master arbitration, immediate NACK abort or physical timing/signoff claim.')
    if result['passed']: check_i2c_cases(result)
    write_json(directory / 'report.json', result)
    return result
