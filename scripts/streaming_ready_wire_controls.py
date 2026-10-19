"""Separate public-wire deadline and actual-SV mutation controls.

The twenty-case positive corpus is unchanged. These controls distinguish a
two-stage sampled-ready deadline from a one-stage sampler and a bypassed guard.
Only native simulation plus the independent peer can reject a mutant here;
compile failures, simulator crashes and unrelated host errors do not count.
"""
from dataclasses import asdict
import hashlib
import json
from pathlib import Path
import re
import struct
import time

from streaming_ready_compile import i2c_image, validate_image
from streaming_ready_peers import StreamingI2cPeer, expected_rx, payloads
from streaming_ready_transport import ReadyHost, pack_read
from streaming_ready_wire_cases import audit_deadline_trace, packed
from streaming_rtl import QuadRTL
from streaming_transport import Code, Opcode, QuadTransport, StreamTransportError
from streaming_wire_cases import EdgeTrace


SCHEMA = 'pinwheel.streaming-ready-wire-controls.v1'
CONTROL_NAMES = ('unchanged-late', 'sampler-stage', 'guard-bypass')


def require(value, message):
    if not value:
        raise RuntimeError(message)


def sha(path): return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def wire_events(path):
    data = Path(path).read_bytes()
    require(len(data) % 20 == 0, 'Truncated Ready control trace')
    previous_scl = previous_sda = 1
    starts = stops = rises = 0
    for row in struct.iter_unpack('<I16B', data):
        scl, sda = bool(row[14] & 1), bool(row[14] & 2)
        if scl and previous_scl and sda != previous_sda:
            if sda: stops += int(starts > 0)
            else: starts += 1
        if starts and scl and not previous_scl: rises += 1
        previous_scl, previous_sda = scl, sda
    return dict(resolved_start_events=starts, resolved_stop_events=stops,
        resolved_scl_rises_after_start=rises)


def mutate_core(text, kind):
    if kind == 'sampler-stage':
        pattern = r"(?m)^(\s*r_stage2 <= [^\n;]+: )r_stage1(;)"
        replacement = r'\g<1>raw_inputs\g<2>'
        operation = 'Replace exactly the second sampler register driver with reset-or-raw_inputs'
    elif kind == 'guard-bypass':
        pattern = r"(?m)^(\s*r_current_word <= .* \? )(_GEN_\d+)( : r_current_word;)$"
        replacement = r"\g<1>(\g<2> & 64'hbfffffffffffffff)\g<3>"
        operation = 'Clear only stream guard-enable bit62 on the current-word entry assignment'
    else:
        raise ValueError('Unknown Ready wire mutation')
    result, changes = re.subn(pattern, replacement, text)
    require(changes == 1 and result != text, 'Mutation must change exactly one recognized actual SV driver')
    return result, operation


def prepare_controls(sources, directory, tools, run, *, freeze=None):
    """Compile mutants from the caller's exact certified five-source bundle."""
    sources = list(map(Path, sources))
    require([path.name for path in sources] == ['core.sv', 'frontend.sv', 'package.sv', 'tt.sv', 'bridge.sv'] and
        all(path.is_file() and not path.is_symlink() for path in sources), 'Expected the exact actual public-wrapper source bundle')
    directory = Path(directory)
    directory.mkdir(parents=True, exist_ok=False)
    original = {str(path): sha(path) for path in sources}
    if freeze: freeze(sources)
    result = {}
    for kind in ('sampler-stage', 'guard-bypass'):
        target = directory / kind
        target.mkdir()
        text, operation = mutate_core(sources[0].read_text(), kind)
        candidate = target / 'core.sv'
        candidate.write_text(text)
        if freeze: freeze([candidate])
        executable = target / 'chip.vvp'
        run([tools['iverilog'], '-g2012', '-s', 'streaming_quad_host_bridge', '-o', executable,
            candidate, *sources[1:]], 'wire-mutant-' + kind)
        if freeze: freeze([executable])
        require({str(path): sha(path) for path in sources} == original, 'Actual source bundle changed during control compilation')
        result[kind] = dict(executable=str(executable), executable_sha256=sha(executable), operation=operation,
            candidate=str(candidate), candidate_sha256=sha(candidate), source_sha256=original, changed_drivers=1)
    return result


def observe(vvp, executable, directory, *, depth, profile):
    """Observe the whole outcome, then ask the independent schedule oracle."""
    directory = Path(directory)
    directory.mkdir(parents=True, exist_ok=False)
    _, read_data = payloads()
    plan, image = pack_read(0x52, 64), i2c_image()
    validate_image(image)
    trace = EdgeTrace(directory / 'wire.bin')
    peer, pending, rtl, oracle_rejected = None, None, None, False
    error_text, native_exit = None, None
    started = time.monotonic()
    observed = {}
    try:
        with QuadRTL(vvp, executable, record_sink=trace) as rtl:
            transport = QuadTransport(rtl)
            host = ReadyHost(transport, depth=depth)
            host.initialize()
            loaded = host.load(image)
            peer = StreamingI2cPeer(plan, read_data, profile=profile)
            rtl.device = peer
            pending = loaded.submit(plan.tx_bits, bit_count=585)
            transport.idle(64)
            pending.pump(max_bits=32)
            pending.wait(max_exchanges=100)
            observed = dict(fault=pending.last.fault, retained=pending.last.retained,
                captured_bits=len(pending.rx_bits), physical_data_rises=len(peer.bits),
                tx_accepted=pending.tx_accepted, owner_tag=pending.tag,
                rx_sha256=hashlib.sha256(packed(pending.rx_bits)).hexdigest(),
                terminal_reply=asdict(pending.last))
            summary = peer.check(pending.rx_bits, fault=pending.last.fault, require_host_stall=True)
            require(profile == 'late' and len(pending.rx_bits) == 11 and pending.last.fault,
                'I2C control oracle unexpectedly accepted a non-late result')
            observed['peer'] = summary
            acknowledged = pending.pump(max_bits=0)
            require(acknowledged.rx_start == 11 and acknowledged.rx_valid == 0, 'Late fault prefix was not acknowledged exactly')
            held = transport.request(Opcode.RELEASE, tag=pending.tag)
            require(held.code is Code.REJECTED and held.retained, 'Late fault discarded unused accepted TX')
            cancelled = host.warm_reset()
            require(cancelled.tag == pending.tag and not cancelled.valid and not cancelled.retained,
                'Late fault explicit cancellation changed allocation IDs')
            observed.update(prefix_acknowledged=True, unused_tx_release_refused=True, warm_cancelled=True)
    except Exception as error:
        cause = error.cause if isinstance(error, StreamTransportError) else error
        error_text = repr(cause)
        oracle_rejected = type(cause) is RuntimeError and str(cause).startswith('I2C ')
    finally:
        record = trace.close()
        if rtl is not None:
            native_exit = rtl.process.returncode
            events = wire_events(directory / 'wire.bin')
            observed.update(physical_edges=rtl.cycle,
                **events, decoded_prefix_rises=len(peer.bits) if peer else 0,
                physical_data_rises=events['resolved_scl_rises_after_start'] - int(peer is not None and peer.stop_rise is not None),
                captured_bits=len(pending.rx_bits) if pending else 0)
        if peer is not None and peer.deadline_alignment is not None:
            try:
                observed['deadline_trace'] = audit_deadline_trace(directory / 'wire.bin', peer.deadline_alignment,
                    peer.expected[peer.deadline_slot])
                observed['deadline_alignment'] = peer.deadline_alignment
            except Exception as error:
                oracle_rejected = False
                error_text = 'Trace audit failed: ' + repr(error)
    result = dict(native_exit_code=native_exit, oracle_rejected=oracle_rejected, error=error_text,
        observation=observed, trace=record, elapsed_seconds=round(time.monotonic() - started, 6))
    (directory / 'observation.json').write_text(json.dumps(result, indent=2) + '\n')
    return result


def check_controls(result):
    require(result.get('schema') == SCHEMA and result.get('passed') is True and result.get('depth') in (2, 4),
        'Incomplete Ready wire-control scope')
    records = result.get('controls', [])
    require([value.get('name') for value in records] == list(CONTROL_NAMES), 'Missing or reordered Ready wire control')
    for index, record in enumerate(records):
        value = record['result']
        require(record.get('passed') is True and record.get('expected_rejection') is (index != 0) and
            value.get('native_exit_code') == 0 and value.get('oracle_rejected') is (index != 0) and
            record.get('profile') == ('varying' if index == 2 else 'late') and
            (isinstance(value.get('error'), str) and 'I2C ' in value['error'] if index else value.get('error') is None),
            'Ready wire control used a native failure or the wrong distinguishing oracle')
        if index == 0:
            observed = value.get('observation', {})
            require(observed.get('fault') is True and observed.get('retained') is True and
                observed.get('captured_bits') == 11 and observed.get('physical_data_rises') in (11, 12) and
                observed.get('owner_tag') == 65537 and observed.get('tx_accepted') == 32 and
                observed.get('rx_sha256') == hashlib.sha256(packed(expected_rx(pack_read(0x52, 64), payloads()[1])[:11])).hexdigest() and
                all(observed.get(name) is True for name in
                    ('prefix_acknowledged', 'unused_tx_release_refused', 'warm_cancelled')),
                'Correct two-stage late readiness did not retain exactly its11-bit prefix')
        if index < 2:
            observed = value.get('observation', {})
            alignment = observed.get('deadline_alignment', {})
            measured = observed.get('deadline_trace', {})
            require(alignment.get('slot') == 11 and alignment.get('expected_stage2_ready') ==
                alignment.get('expected_last_poll', 0) + 1 and measured.get('measured_first_raw_high') ==
                alignment.get('first_raw_high'), 'Late control lacks the actual one-poll-late raw-input window')
        if index:
            mutation = record.get('mutation', {})
            sources = mutation.get('source_sha256', {})
            require(mutation.get('changed_drivers') == 1 and mutation.get('operation') and len(sources) == 5 and
                {Path(name).name for name in sources} == {'core.sv', 'frontend.sv', 'package.sv', 'tt.sv', 'bridge.sv'} and
                mutation.get('candidate_sha256') != next(value for path, value in sources.items() if Path(path).name == 'core.sv') and
                re.fullmatch(r'[0-9a-f]{64}', mutation.get('candidate_sha256', '')) and
                re.fullmatch(r'[0-9a-f]{64}', mutation.get('executable_sha256', '')),
                'Wire mutation is not bound to an actual retained one-driver SV change')
        trace = value.get('trace', {})
        require(trace.get('edges', 0) > 0 and trace.get('bytes') == trace['edges'] * 20 and
            re.fullmatch(r'[0-9a-f]{64}', trace.get('sha256', '')) and
            value.get('observation', {}).get('physical_edges') == trace['edges'], 'Ready control trace is incomplete')
    require(result.get('physical_edges') == sum(record['result']['trace']['edges'] for record in records),
        'Ready control aggregate edge count differs')


def run_ready_controls(vvp, unchanged_executable, mutants, directory, *, depth):
    require(depth in (2, 4) and set(mutants) == {'sampler-stage', 'guard-bypass'}, 'Both actual SV mutants are required')
    directory = Path(directory)
    directory.mkdir(parents=True, exist_ok=False)
    records = []
    for name in CONTROL_NAMES:
        mutation = None if name == 'unchanged-late' else mutants[name]
        executable = unchanged_executable if mutation is None else mutation['executable']
        if mutation:
            require(sha(executable) == mutation['executable_sha256'] and sha(mutation['candidate']) ==
                mutation['candidate_sha256'] and all(sha(path) == value for path, value in mutation['source_sha256'].items()),
                'Wire mutation artifact changed before consumption')
        profile = 'varying' if name == 'guard-bypass' else 'late'
        result = observe(vvp, executable, directory / name, depth=depth, profile=profile)
        if mutation:
            require(sha(executable) == mutation['executable_sha256'] and sha(mutation['candidate']) ==
                mutation['candidate_sha256'] and all(sha(path) == value for path, value in mutation['source_sha256'].items()),
                'Wire mutation artifact changed during consumption')
        rejected = name != 'unchanged-late'
        records.append(dict(name=name, passed=result['native_exit_code'] == 0 and
            result['oracle_rejected'] is rejected and (rejected or result['error'] is None),
            expected_rejection=rejected, profile=profile, mutation=mutation, result=result))
    result = dict(schema=SCHEMA, passed=all(record['passed'] for record in records), depth=depth,
        controls=records, physical_edges=sum(record['result']['trace']['edges'] for record in records),
        boundary='Finite public-wire negative controls. Expected data comes from an external I2C plan; '
            'public OE aligns the late diagnostic. Actual SV edits change one sampler or current-word driver. '
            'No mapped/electrical claim and no private RTL state is an expected-data oracle.')
    if result['passed']: check_controls(result)
    (directory / 'report.json').write_text(json.dumps(result, indent=2) + '\n')
    return result
