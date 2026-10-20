"""Autonomous 8N1 reception through the unchanged public sampled-ready package.

Valid frames use an independent absolute-clock transmitter. No quad request or
read occurs during a frame. A separate actual sampler mutant is distinguished
by its one-edge-early public BUSY transition, not by an assumed payload change.
"""
from dataclasses import asdict
import hashlib
import json
from pathlib import Path
import re

from streaming_ready_transport import ReadyHost
from streaming_rtl import QuadRTL
from streaming_transport import Code, Opcode, QuadTransport, Receipt
from streaming_uart_compile import QUARTERS, lean_certificate, project, uart_image, validate_uart_image
from streaming_uart_peers import AbsoluteUartPeer, FrameObservation, UartPlan
from streaming_wire_cases import EdgeTrace

SCHEMA = 'pinwheel.streaming-uart-wire.v1'
UART_VALID_FRAMES_PER_DEPTH = 768
UART_ERROR_CONTROLS_PER_DEPTH = 9
UART_SAMPLING_DIAGNOSTICS_PER_DEPTH = 2
UART_MUTANT_CONTROLS_PER_DEPTH = 1
UART_CASES_PER_DEPTH = 780
MUTATION_OPERATION = 'Replace exactly the second sampler register driver with reset-or-raw_inputs'


def require(condition, message):
    if not condition: raise RuntimeError(message)


def sha(path): return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def case_keys():
    result = []
    for q in QUARTERS:
        result += [('valid', q, byte) for byte in range(256)]
        result += [('false-start', q, 0x96), ('bad-stop', q, 0x69)]
        if q == 4: result += [('sampling-center', 4, 0), ('sampling-off-center', 4, 0)]
        result += [('held-high', q, 0)]
    return result + [('sampler-stage', 4, 0)]


class Recording:
    def __init__(self, path):
        self.trace, self.active = EdgeTrace(path), None

    def __call__(self, record):
        self.trace(record)
        if self.active is not None: self.active(record)


def opcode_counts(transport):
    return {op.name: count for op, count in transport.opcode_counts.items() if count}


def receive_frame(rtl, transport, host, loaded, recording, *, q, profile, payload, timing_delta=0):
    """One actual START8, an autonomous frame, then exact drain/ACK/RELEASE."""
    before, start_count = transport.transactions, transport.opcode_counts[Opcode.START]
    pending = loaded.submit(bit_count=8)
    start = pending.last
    require(start.busy and not start.retained and start.valid and start.tx_accepted == 0,
        'UART START did not arm a free valid RX-only owner')
    first, falling = rtl.cycle + 1, rtl.cycle + 16
    plan = UartPlan(q, payload, falling, profile)
    end = falling + 40 * q + 8
    observation = FrameObservation(plan, first, end)
    recording.active = observation
    rtl.device = AbsoluteUartPeer(plan)
    requests_before_frame = transport.transactions
    transport.idle(end - rtl.cycle)
    recording.active = None
    observed = observation.result()
    require(transport.transactions == requests_before_frame, 'UART autonomously received while host commands were issued')
    if profile == 'held-high':
        require(observed['public_terminal_edge'] is None, 'UART unbounded start wait completed without a start')
    else:
        require(observed['terminal_delta'] == timing_delta,
            'UART public terminal edge differs from the exact delayed-sample source timing')
    receipt = pending.pump(max_bits=0)
    expected = plan.expected_bits
    require(pending.rx_bits == expected and pending.tx_accepted == 0 and receipt.tag == pending.tag and
        receipt.rx_start == 0 and receipt.rx_valid == len(expected) and receipt.tx_free == host.depth and
        not receipt.rx_queued, 'UART exact retained RX prefix, owner or zero-TX custody differs')
    require(receipt.fault is plan.expected_fault and receipt.busy is (profile == 'held-high') and
        receipt.retained is (profile != 'held-high'), 'UART fault/retained status differs from the independent stimulus')
    projection = project(pending.rx_bits, fault=receipt.fault, uart_timing=plan.uart_timing)
    if profile == 'held-high':
        final = host.warm_reset()
        require(final.tag == pending.tag and not final.valid and not final.busy and not final.retained,
            'UART explicit cancellation changed allocation or failed to clear the waiting owner')
        cleanup = 'warm-cancel'
    else:
        final = pending.release()
        require(final.tag == pending.tag and final.valid and not final.busy and not final.retained and
            not final.tx_accepted and not final.rx_queued and not final.rx_valid,
            'UART exact acknowledgement and matching RELEASE did not restore the free valid slot')
        cleanup = 'matching-release'
    require(transport.opcode_counts[Opcode.START] - start_count == 1, 'UART frame used multiple START commands')
    return dict(passed=True, kind=profile, quarter_cycles=q, payload=payload,
        image_generation=loaded.generation, owner_tag=pending.tag, starts=1,
        start_sequence=start.sequence, start_receipt=asdict(start), rx_receipt=asdict(receipt),
        cleanup_receipt=asdict(final), cleanup=cleanup, tx_accepted=pending.tx_accepted,
        captured_bits=len(pending.rx_bits), rx_bits=list(pending.rx_bits),
        projection=asdict(projection), waveform=asdict(plan), observation=observed,
        requests=transport.transactions - before,
        source_timing_refuted=timing_delta != 0, expected_terminal_delta=timing_delta,
        interpretation='single-edge sampling-window diagnostic; not a valid UART timing claim'
            if profile.startswith('sampling-') else 'one 8N1 frame' if profile == 'valid' else 'UART error/park control')


def validate_mutation(mutation):
    require(type(mutation) is dict and mutation.get('changed_drivers') == 1 and
        mutation.get('operation') == MUTATION_OPERATION, 'An actual one-driver sampler-stage mutant is mandatory')
    sources = mutation.get('source_sha256', {})
    require(type(sources) is dict and len(sources) == 5 and {Path(path).name for path in sources} ==
        {'core.sv', 'frontend.sv', 'package.sv', 'tt.sv', 'bridge.sv'}, 'UART sampler mutant lacks its exact source bundle')
    for key in ('candidate_sha256', 'executable_sha256'):
        require(re.fullmatch(r'[0-9a-f]{64}', mutation.get(key, '')), 'UART sampler mutant lacks a valid retained hash')
    require(mutation['candidate_sha256'] != next(value for path, value in sources.items() if Path(path).name == 'core.sv'),
        'UART sampler mutation did not change the actual core source')


def assert_mutation_files(mutation):
    validate_mutation(mutation)
    for path, expected in {**mutation['source_sha256'], mutation['candidate']: mutation['candidate_sha256'],
            mutation['executable']: mutation['executable_sha256']}.items():
        require(Path(path).is_file() and not Path(path).is_symlink() and sha(path) == expected,
            'UART sampler mutant input changed before or during native consumption')


def check_uart_cases(result):
    require(result.get('schema') == SCHEMA and result.get('passed') is True and
        type(result.get('depth')) is int and result['depth'] in (2, 4),
        'Incomplete autonomous UART corpus scope')
    require(result.get('case_counts') == dict(valid_frames=768, error_controls=9,
        sampling_diagnostics=2, mutant_controls=1, total=780), 'UART required case counts differ')
    cases = result.get('cases', [])
    require([(case.get('kind'), case.get('quarter_cycles'), case.get('payload')) for case in cases] == case_keys(),
        'UART payload/control corpus is missing, duplicated or reordered')
    depth = result['depth']
    images = result.get('images', [])
    require([item.get('quarter_cycles') for item in images] == list(QUARTERS), 'UART loaded profile inventory differs')
    for item in images:
        image = uart_image(item['quarter_cycles'])
        require(item.get('words') == list(image.words) and item.get('certificate') == asdict(image.certificate) and
            item.get('rows') == 9 and item.get('loads') == 1, 'UART source/image or single-load reuse binding differs')
    last_owner, last_q, transfer = None, None, 0
    generations = {item['quarter_cycles']: item.get('generation') for item in images}
    for case in cases:
        kind, q = case['kind'], case['quarter_cycles']
        mutant = kind == 'sampler-stage'
        profile = 'sampling-center' if mutant else kind
        plan = UartPlan(**case['waveform'])
        require(plan == UartPlan(q, case['payload'], plan.first_low_edge, profile), 'UART waveform parameters differ')
        expected = plan.expected_bits
        observation = case.get('observation', {})
        rx = Receipt(**{**case['rx_receipt'], 'code': Code(case['rx_receipt']['code'])})
        start = Receipt(**{**case['start_receipt'], 'code': Code(case['start_receipt']['code'])})
        final = Receipt(**{**case['cleanup_receipt'], 'code': Code(case['cleanup_receipt']['code'])})
        require(case.get('passed') is True and case.get('starts') == 1 and case.get('tx_accepted') == 0 and
            case.get('captured_bits') == len(expected) and case.get('rx_bits') == list(expected),
            'UART payload bit order, prefix length or zero-TX ownership differs')
        require(start.code is Code.ACCEPTED and start.sequence == case['start_sequence'] and start.busy and start.valid and
            not start.retained and start.rx_valid == 0 and start.tx_accepted == 0 and
            start.tag == rx.tag == final.tag == case['owner_tag'] and start.generation == case['image_generation'] and
            rx.code is Code.ACCEPTED and rx.valid and rx.rx_start == 0 and rx.rx_valid == len(expected) and
            rx.tx_accepted == 0 and rx.tx_free == depth and rx.rx_queued == 0 and
            tuple(rx.rx_bits) == expected and rx.fault is plan.expected_fault,
            'UART actual receipt owner, retained prefix or right-aligned packed word differs')
        held = profile == 'held-high'
        require(rx.busy is held and rx.retained is (not held) and case.get('requests') == (3 if held else 4),
            'UART frame command count or terminal status differs')
        require(json.loads(json.dumps(case.get('projection'))) == json.loads(json.dumps(asdict(project(expected,
            fault=plan.expected_fault, uart_timing=plan.uart_timing)))), 'UART LSB-first payload/fault projection differs')
        require(observation.get('first_edge', 0) + 15 == plan.first_low_edge and
            observation.get('last_edge') == plan.first_low_edge + 40 * q + 8 and
            observation.get('edges') == observation['last_edge'] - observation['first_edge'] + 1 and
            observation.get('idle_high_arm_edges') == 15 and observation.get('host_frames_during_reception') == 0 and
            observation.get('released_protocol_pins') is True and
            observation.get('first_raw_low') == (None if held else plan.first_low_edge),
            'UART autonomous physical-frame/arming chronology differs')
        delta = -1 if mutant else 0
        require(case.get('expected_terminal_delta') == delta and case.get('source_timing_refuted') is mutant and
            observation.get('expected_terminal_edge') == plan.expected_terminal_edge and
            observation.get('public_terminal_edge') == (None if held else plan.expected_terminal_edge + delta) and
            observation.get('terminal_delta') == (None if held else delta), 'UART exact public terminal timing differs')
        require(observation.get('raw_sample_edges') == list(plan.samples), 'UART raw sample-center offsets differ')
        if profile not in ('false-start', 'held-high'):
            require(observation.get('raw_center_bits') == list(expected), 'UART center sample raw input differs')
        if held:
            require(case.get('cleanup') == 'warm-cancel' and final.code is Code.ACCEPTED and
                final.flags == 0 and final.tx_accepted == 0 and final.rx_queued == 0,
                'UART unbounded no-start wait was not explicitly cancelled')
        else:
            require(case.get('cleanup') == 'matching-release' and final.code is Code.ACCEPTED and
                final.flags == 1 and final.tx_accepted == 0 and final.rx_valid == 0 and final.rx_queued == 0,
                'UART exact ACK plus matching RELEASE failed to restore a free valid image')
        if not mutant:
            transfer += 1
            require(start.transfer == transfer and start.generation == generations[q],
                'UART reset/reload boundaries lost the carried allocator or loaded-image generation')
            if q == last_q:
                require(case['owner_tag'] == last_owner + 1, 'UART fixed-image reuse lost the carried transfer allocator')
            last_q, last_owner = q, case['owner_tag']
        else:
            require(case.get('name') == 'sampler-stage' and case.get('expected_rejection') is True and
                case.get('oracle_rejected') is True, 'UART actual sampler timing negative control is missing')
            validate_mutation(case.get('mutation'))
    runs = result.get('native_runs', [])
    require([run.get('name') for run in runs] == ['unchanged', 'sampler-stage'], 'UART native run inventory differs')
    expected_counts = dict(WRITE=27, COMMIT=3, START=779, RELEASE=776, WARM_RESET=3, EXCHANGE0=1555)
    for index, run in enumerate(runs):
        require(run.get('native_exit_code') == 0 and run.get('physical_edges', 0) > 0 and
            type(run.get('argv')) is list and len(run['argv']) == 2 and
            re.fullmatch(r'[0-9a-f]{64}', run.get('executable_sha256', '')) and
            run.get('executable_unchanged') is True and run.get('opcode_counts') ==
            (expected_counts if index == 0 else dict(WRITE=9, COMMIT=1, START=1, EXCHANGE0=2, RELEASE=1)),
            'UART native exit, executable binding or fixed-image operation inventory differs')
        trace = run.get('trace', {})
        require(trace.get('edges') == run['physical_edges'] and trace.get('bytes') == run['physical_edges'] * 20 and
            re.fullmatch(r'[0-9a-f]{64}', trace.get('sha256', '')), 'UART complete physical trace inventory differs')
    control = cases[-1]
    require(control.get('native') == runs[1] and runs[1]['argv'][1] == control['mutation']['executable'] and
        runs[1]['executable_sha256'] == control['mutation']['executable_sha256'],
        'UART sampler control does not consume the exact retained actual mutant executable')
    last_edge = 0
    for case in cases:
        observation = case['observation']
        mutant = case['kind'] == 'sampler-stage'
        require(observation['last_edge'] <= runs[int(mutant)]['physical_edges'] and
            (mutant or observation['first_edge'] > last_edge), 'UART frame ranges are outside or overlap the native trace')
        last_edge = observation['last_edge']
    require(result.get('physical_edges') == sum(run['physical_edges'] for run in runs), 'UART total physical edges differ')


def run_uart_cases(vvp, executable, out, *, depth, sampler_mutant=None):
    """Run the exact 780-case contract for one already compiled Ready depth."""
    require(type(depth) is int and depth in (2, 4), 'UART qualification depth must be2 or4')
    assert_mutation_files(sampler_mutant)
    out = Path(out)
    out.mkdir(parents=True, exist_ok=False)
    executable = Path(executable)
    original_executable = sha(executable)
    result = dict(schema=SCHEMA, passed=False, depth=depth, images=[], cases=[], native_runs=[],
        case_counts=dict(valid_frames=768, error_controls=9, sampling_diagnostics=2, mutant_controls=1, total=780),
        boundary='Finite autonomous8N1 corpus through the unchanged Ready public quad package. '
            'One frame perSTART8, noTX and no host request/read during reception. '
            'Clock rate is exactly4Q controller clocks per bit; no analog, metastability, clock mismatch tolerance '
            'or continuous multi-frame-perSTART claim. Sampling-window diagnostics are outside valid UART timing. '
            'Uniform sampler latency changes cancel in raw data centers; the actual mutant is distinguished '
            'by its one-edge-early public BUSY transition.')
    recording, rtl = Recording(out / 'wire.bin'), None
    try:
        with QuadRTL(vvp, executable, record_sink=recording) as rtl:
            transport = QuadTransport(rtl)
            host = ReadyHost(transport, depth=depth)
            host.initialize()
            for q in QUARTERS:
                image = uart_image(q)
                validate_uart_image(image)
                (out / f'UARTImageQ{q}.lean').write_text(lean_certificate(image))
                loaded = host.load(image)
                result['images'].append(dict(quarter_cycles=q, words=list(image.words),
                    certificate=asdict(image.certificate), rows=9, loads=1, generation=loaded.generation))
                profiles = [('valid', byte) for byte in range(256)] + [('false-start', 0x96), ('bad-stop', 0x69)]
                if q == 4: profiles += [('sampling-center', 0), ('sampling-off-center', 0)]
                profiles += [('held-high', 0)]
                for profile, payload in profiles:
                    result['cases'].append(receive_frame(rtl, transport, host, loaded, recording,
                        q=q, profile=profile, payload=payload))
        result['native_runs'].append(dict(name='unchanged', argv=[str(vvp), str(executable)],
            native_exit_code=rtl.process.returncode, physical_edges=rtl.cycle,
            executable_sha256=original_executable, executable_unchanged=sha(executable) == original_executable,
            opcode_counts=opcode_counts(transport), trace=recording.trace.close()))
        assert_mutation_files(sampler_mutant)
        mutant_dir = out / 'sampler-stage'
        mutant_dir.mkdir()
        mutant_recording = Recording(mutant_dir / 'wire.bin')
        mutant_rtl = None
        try:
            with QuadRTL(vvp, sampler_mutant['executable'], record_sink=mutant_recording) as mutant_rtl:
                mutant_transport = QuadTransport(mutant_rtl)
                mutant_host = ReadyHost(mutant_transport, depth=depth)
                mutant_host.initialize()
                loaded = mutant_host.load(uart_image(4))
                control = receive_frame(mutant_rtl, mutant_transport, mutant_host, loaded, mutant_recording,
                    q=4, profile='sampling-center', payload=0, timing_delta=-1)
            native = dict(name='sampler-stage', argv=[str(vvp), sampler_mutant['executable']],
                native_exit_code=mutant_rtl.process.returncode, physical_edges=mutant_rtl.cycle,
                executable_sha256=sha(sampler_mutant['executable']), executable_unchanged=True,
                opcode_counts=opcode_counts(mutant_transport), trace=mutant_recording.trace.close())
            control.update(kind='sampler-stage', name='sampler-stage', expected_rejection=True, oracle_rejected=True,
                mutation=sampler_mutant, native=native)
            result['cases'].append(control)
            result['native_runs'].append(native)
        finally:
            mutant_recording.trace.close()
        assert_mutation_files(sampler_mutant)
        result.update(passed=True, physical_edges=sum(run['physical_edges'] for run in result['native_runs']))
        check_uart_cases(result)
    except BaseException as error:
        result.update(passed=False, error=type(error).__name__ + ': ' + str(error),
            completed_cases=len(result['cases']), physical_edges=rtl.cycle if rtl else recording.trace.edges)
        raise
    finally:
        recording.trace.close()
        (out / 'report.json').write_text(json.dumps(result, indent=2) + '\n')
    return result
