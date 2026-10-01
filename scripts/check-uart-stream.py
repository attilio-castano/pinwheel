#!/usr/bin/env python3
"""Fresh resolved-wire UART supervisor, one-entry mailbox and ownership gate."""
import argparse
from dataclasses import asdict, replace
import itertools
import json
from pathlib import Path
import re
import time

from capability_receipt import CapabilityEvidence
from host_demo import compiler_images
from i2c_peers import I2CWritePeer
from pad_io import PAD_MAP
from pad_peers import SPIPeer, spi_result_bytes, require
from pinwheel_host import Command, Host, PAIRED_FORMAT, Program
from pinwheel_sim import Simulation
from protocol_tool_closure import ProtocolToolClosure
from uart_stream_peer import Frame, OneEntryOracle, UARTStreamPeer
from validation_run import Commands, fresh_directory, sha

ROOT = Path(__file__).resolve().parents[1]
FIELDS = {'name', 'bit_cycles', 'input_pin', 'populated_positions', 'canonical_records'}
RESULT_FIELDS = [('reset_first', 1), ('reset_second', 1), ('page_first', 2), ('page_second', 2),
    ('control_first', 2), ('control_second', 2), ('consume_prev', 1), ('clear_prev', 1),
    ('was_active', 1), ('samples', 16), ('outcome', 3), ('valid', 1), ('overrun', 1), ('rejected', 1)]


def metadata(data, images):
    entries = json.loads(data)
    require(isinstance(entries, list) and entries, 'UART metadata must be a nonempty list')
    names = set()
    for item in entries:
        require(isinstance(item, dict) and set(item) == FIELDS and
            isinstance(item['name'], str) and re.fullmatch(r'[A-Za-z0-9_-]+', item['name']),
            'Unsupported UART fixture schema/name')
        require(all(type(item[k]) is int for k in FIELDS - {'name'}) and
            8 <= item['bit_cycles'] <= 6656 and item['input_pin'] in (0, 1), 'UART configuration range/type')
        require(item['name'] in images and item['name'] not in names, 'UART image/metadata names differ')
        source = images[item['name']]
        require(source.last + 1 == item['populated_positions'] and
            len(set(source.words)) == item['canonical_records'] and item['canonical_records'] <= 32,
            'UART metadata differs from actual source image capacity')
        names.add(item['name'])
    require(names == set(images), 'UART image/metadata names differ')
    require({(b, p) for b in (8, 9, 16, 257, 6656) for p in (0, 1)} <=
            {(x['bit_cycles'], x['input_pin']) for x in entries}, 'UART baseline fixture coverage incomplete')
    return entries


def timing_certificate(name, bit_cycles, input_pin, tx_cycles, tx_tick, rx_tick, phase, start, payload):
    require(re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*', name), 'Invalid UART timing certificate name')
    values = ', '.join(map(str, payload))
    return f'''import Pinwheel.Compile.UARTStreamLink
import Pinwheel.UART.LinkPipeline
import Lean
namespace Pinwheel.Artifact.UARTStream.{name}
open Pinwheel Pinwheel.UART
def timing : Link.Timing := {{
  tx := ⟨⟨{tx_cycles - 1}, by decide⟩⟩
  rx := ⟨{bit_cycles}, by decide, by decide, {input_pin}⟩
  txTick := {tx_tick}, txTickPositive := by decide
  rxTick := {rx_tick}, rxTickPositive := by decide
  txStart := {start}, rxPhase := {phase} }}
def latency : Link.Latency := .fixed {2 * rx_tick}
def bytes : List (BitVec 8) := [{values}]
def incoming (n : Nat) : Rx.Stream.Input :=
  {{line := StreamLink.sampled timing bytes (fun _ => {2 * rx_tick}) n}}
theorem safe : StreamLink.Safe timing latency := by decide
theorem received : ∃ frames, frames.map Rx.Stream.FrameSpec.byte = bytes ∧
    StreamLink.Windows timing latency frames ∧
    ∀ n, n ≤ Rx.Stream.horizon timing.rx frames →
      Compile.UARTRx.result (Compile.UARTRxStream.run timing.rx
        (Compile.UARTRxStream.lift timing.rx ⟨Rx.initial, {{}}⟩)
        incoming (fun _ => false) n).core = Rx.Stream.expected timing.rx frames n := by
  apply Compile.UARTStreamLink.receive_series timing latency bytes (fun _ => {2 * rx_tick})
    incoming (fun _ => false) {{}} safe
  · intro n; exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  · intro n; rfl
  · intro n; rfl
end Pinwheel.Artifact.UARTStream.{name}
open Lean Elab Command in
elab "#audit_uart_stream_timing" : command => do
  for theoremName in [``Pinwheel.Artifact.UARTStream.{name}.safe,
      ``Pinwheel.Artifact.UARTStream.{name}.received,
      ``Pinwheel.Compile.UARTStreamLink.receive_series,
      ``Pinwheel.UART.StreamLink.Safe.delayed] do
    let axioms ← collectAxioms theoremName
    let unexpected := axioms.filter fun ax =>
      ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound
    unless unexpected.isEmpty do throwError "Unapproved UART timing axioms: {{unexpected}}"
  logInfo "UART stream timing certificate: kernel checked; standard axioms only."
#audit_uart_stream_timing
'''


def certify_timing(evidence, run, name, **kwargs):
    path = evidence.out / (name + '-timing.lean')
    require(not path.exists(), 'Preserve existing UART timing certificate')
    path.write_text(timing_certificate(name.replace('-', '_'), **kwargs))
    digest = evidence.freeze_generated(path)
    log = run(['lake', 'env', 'lean', '-DwarningAsError=true', path], name + '-timing')
    require(sha(path) == digest, 'UART timing certificate changed during kernel consumption')
    require('UART stream timing certificate: kernel checked; standard axioms only.' in log,
            'Missing UART timing axiom audit')
    return dict(path=path.name, sha256=digest, **kwargs,
        scope='Kernel sufficient clock bounds and ideal finite-wire compiled theorem; '
              'actual resolved pin history and mailbox timing are checked separately.')


def result_component_vector(old, arrival, overrun=False, take=False, clear=False, reset=False,
                            consume_prev=False, clear_prev=False, busy=False, started=False, rejected=False):
    state = dict(reset_first=1, reset_second=1, page_first=2, page_second=3, control_first=2,
        control_second=int(take) | int(clear) << 1, consume_prev=int(consume_prev), clear_prev=int(clear_prev),
        was_active=1, samples=0 if old is None else old, outcome=0 if old is None else 5,
        valid=int(old is not None), overrun=int(overrun), rejected=0)
    core = dict(pin_rst_n=int(not reset), pin_ui_in=0x74, core_busy=int(busy),
        core_mode=0 if arrival is None else 5, core_samples=0 if arrival is None else arrival,
        core_start=int(started), core_rejected=int(rejected))
    event = arrival if arrival is not None and not busy else None
    queue = OneEntryOracle(None if old is None else (old, 5), overrun)
    receipt = queue.edge(None if event is None else (event, 5), take=take and not consume_prev,
                         clear=clear and not clear_prev, reset=reset)
    accepted = receipt['accepted']
    expected = dict(reset_first=int(not reset), reset_second=1, page_first=2, page_second=2,
        control_first=3, control_second=2, consume_prev=0 if reset else int(take),
        clear_prev=0 if reset else int(clear), was_active=0 if reset else int(busy or started),
        samples=0 if reset else accepted[0] if accepted else state['samples'],
        outcome=0 if reset else accepted[1] if accepted else state['outcome'],
        valid=int(queue.pending is not None), overrun=int(queue.overrun), rejected=int(not reset and rejected))
    return dict(inputs={**core, **{'state_result_' + k: v for k, v in state.items()}},
        expected={'next_result_' + k: v for k, v in expected.items()}, receipt=receipt)


def component_vectors():
    values = (None, 0x200, 0x2ff, 0x53)
    vectors = [result_component_vector(old, new, overrun, take, clear)
        for old, new, overrun, take, clear in itertools.product(values, values, (False, True), (False, True), (False, True))]
    for old, new in itertools.product(values, values):
        vectors.append(result_component_vector(old, new, True, True, True, reset=True))
    vectors.extend([result_component_vector(0x253, 0x2a6, True, True, True, consume_prev=True, clear_prev=True),
        result_component_vector(0x253, 0x2a6, busy=True),
        result_component_vector(None, None, started=True),
        result_component_vector(0x253, None, rejected=True)])
    return vectors


def component_testbench(vectors):
    inputs = [('pin_rst_n', 1), ('pin_ui_in', 8), ('core_busy', 1), ('core_mode', 3),
        ('core_samples', 16), ('core_start', 1), ('core_rejected', 1),
        *[('state_result_' + name, width) for name, width in RESULT_FIELDS]]
    outputs = [('next_result_' + name, width) for name, width in RESULT_FIELDS]
    declarations = ['reg clk=0;'] + ['reg ' + (f'[{w-1}:0] ' if w > 1 else '') + n + ';' for n,w in inputs]
    declarations += ['wire ' + (f'[{w-1}:0] ' if w > 1 else '') + n + ';' for n,w in outputs]
    rows = []
    for index, vector in enumerate(vectors):
        rows += [f'{name} = {value};' for name,value in vector['inputs'].items()]
        rows += ['#1;']
        rows += [f'if ({name} !== {value}) $fatal(1,"UART_BUFFER vector{index} {name}");'
                 for name,value in vector['expected'].items()]
    return '\n'.join(['module uart_stream_result_tb;', *declarations,
        'uart_stream_result_component dut(.*);', 'initial begin', *rows,
        f'$display("UART buffer RTL: {len(vectors)} vectors passed.");', '$finish;', 'end', 'endmodule', ''])


def pulse_at(host, bit, edge):
    """Raw control rise reaches the existing two-stage edge detector on edge."""
    require(edge - 3 >= host.transport.cycle, 'UART control deadline already passed')
    host.ui &= ~(1 << bit)
    if edge - 3 > host.transport.cycle:
        host.advance(edge - 3 - host.transport.cycle)
    host.ui |= 1 << bit
    host.advance(3)
    host.ui &= ~(1 << bit)
    host.advance(3)


def scheduled_peer(simulation, item, payload, *, stops=None, tx_tick=100, rx_phase=0,
                   gap=0, initial_low=False, false_start=False, start_after=None):
    period, pin = item['bit_cycles'], item['input_pin']
    base = simulation.cycle
    # The external schedule is fixed before sending the 292-edge arm command.
    # Its first frame remains later than the complete command/status handshake.
    start = (base + (start_after if start_after is not None else 480 if initial_low else 430)) * 100 + 1
    bit_ticks = period * tx_tick
    stops = [1] * len(payload) if stops is None else stops
    frames = [Frame(start + k * (10 * bit_ticks + gap * 100), byte, bit_ticks, stops[k])
              for k, byte in enumerate(payload)]
    return UARTStreamPeer(frames, input_pin=pin, rx_phase=rx_phase,
        initial_low_until=(base + 450) * 100 if initial_low else 0,
        low_pulses=[((base + 350) * 100, (base + 351) * 100)] if false_start else [])


def load(host, evidence, run, name, source):
    program = replace(source, image_format=PAIRED_FORMAT)
    evidence.certify(name, program, run)
    path = evidence.out / (name + '.json')
    program.write(path)
    evidence.freeze_generated(path)
    host.upload(program)
    return program


def observe_stream(simulation, host, item, peer, *, policy='ready'):
    simulation.device = peer
    if peer.initial_low_until:
        host.advance(4)  # Drain the raw held-low input before arm.
    host.arm_uart_stream()
    armed = simulation.cycle
    end = (peer.frames[-1].end + 99 - peer.rx_phase) // 100 + 5
    expected = peer.completions(item['bit_cycles'], armed, end)
    intended = [(f.byte, not bool(f.stop)) for f in peer.frames]
    require([(r.byte,r.framing_error) for r in expected] == intended,
            'Declared UART wire schedule does not produce the intended frame sequence')
    reads = []
    if policy == 'ready':
        for event in expected:
            result = host.read_uart_result(timeout_cycles=event.mailbox_edge - simulation.cycle + 16, consume=False)
            again = host.read_uart_result(timeout_cycles=0, consume=False)
            require(result == again, 'UART retained byte changed without consumption')
            require((result.byte, result.framing_error) == (event.byte, event.framing_error), 'UART byte/framing mismatch')
            require(not result.overrun and not result.rejected, 'UART ready-consumer flags')
            host.consume()
            reads.append(asdict(result))
    elif policy in ('stall', 'simultaneous', 'clear-drop'):
        if policy == 'simultaneous':
            first = host.read_uart_result(timeout_cycles=100_000, consume=False)
            require(first.byte == expected[0].byte, 'UART old result absent before simultaneous consumption')
            pulse_at(host, 5, expected[1].mailbox_edge)
        elif policy == 'clear-drop':
            if simulation.cycle < expected[1].mailbox_edge + 2:
                host.advance(expected[1].mailbox_edge + 2 - simulation.cycle)
            require(host.stream_status() & 2, 'UART first drop failed to set overrun')
            pulse_at(host, 6, expected[2].mailbox_edge)
        if simulation.cycle < end:
            host.advance(end - simulation.cycle)
        result = host.read_uart_result(timeout_cycles=0, consume=False)
        index = 1 if policy == 'simultaneous' else 0
        require((result.byte,result.framing_error) == (expected[index].byte,expected[index].framing_error),
                'UART unread ownership order')
        require(result.overrun == (policy != 'simultaneous') and not result.rejected, 'UART drop/clear/consume priority')
        require(result == host.read_uart_result(timeout_cycles=0, consume=False), 'UART stalled retention changed')
        reads.append(asdict(result))
        host.consume()
        require(not host.stream_status() & 1, 'UART terminal pending result not consumed')
        host.clear_flags()
        require(not host.stream_status() & 6, 'UART flags failed to clear without new arrival')
    else:
        raise ValueError('Unknown UART consumer policy')
    require(simulation.pins.enabled == 0, 'UART RX output drive')
    host.stop_uart_stream()
    require(not host.stream_status() & 8 and not host.page(0) & 1, 'UART stop did not quiesce supervisor')
    simulation.device = None
    return dict(policy=policy, expected_completions=[asdict(e) for e in expected], reads=reads,
        retained_twice=True, outputs_released=True, stopped=True, wire=peer.report(),
        boundary='Package mailbox captures core completion one edge later; raw consumer controls use the same mailbox edge.')


def advance_to(host, edge):
    if edge > host.transport.cycle:
        host.advance(edge - host.transport.cycle)


def check_packet(host, samples, *, outcome=5, overrun=False, rejected=False):
    result = host.read_result(timeout_cycles=0, consume=False)
    require((result.samples, result.outcome, result.overrun, result.rejected) ==
            (samples, outcome, overrun, rejected), 'UART retained packet or flags differ from expected ownership')
    require(result == host.read_result(timeout_cycles=0, consume=False), 'UART packet changed between retained reads')
    return asdict(result)


def session_controls(simulation, host, item, source, evidence, run):
    """Actual serial ownership and reset boundaries, with a fixed external schedule."""
    controls = []
    simulation.device = None
    host.reset()
    host.command(Command.STREAM, 1)
    require(host.stream_status() & 4 and not host.stream_status() & 8,
            'UART arm accepted an absent committed image')
    host.clear_flags()
    load(host, evidence, run, 'uart-control-source', source)
    host.command(Command.BEGIN)
    require(host.page(0) & 4, 'UART pending-upload control did not stage an image')
    host.command(Command.STREAM, 1)
    require(host.stream_status() & 4 and not host.stream_status() & 8 and host.page(0) & 4,
            'UART arm accepted or discarded a staged upload')
    host.command(Command.ABORT)
    host.clear_flags()
    controls.append(dict(name='arm-no-image-and-staged-upload', absent_image_rejected=True,
                         staged_image_rejected_and_preserved=True, aborted=True))

    peer = scheduled_peer(simulation, item, [0x53], start_after=2600)
    simulation.device = peer
    host.arm_uart_stream()
    rejected_commands = []
    for command, data in [(Command.BEGIN, 0), (Command.PUSH, 4), (Command.COMMIT, 0),
                          (Command.ABORT, 0), (Command.START, 0), (Command.STREAM, 2)]:
        host.command(command, data)
        status = host.stream_status()
        require(status & 8 and status & 4 and host.page(0) & 7 == 3,
                'UART enabled session did not reserve the committed executing image')
        rejected_commands.append(dict(command=int(command), data=data, enabled=True, rejected=True,
                                      committed_image_valid=True, staging_pending=False))
        host.clear_flags()
    result = host.read_uart_result(timeout_cycles=10_000, consume=False)
    require(result.byte == 0x53 and not result.framing_error and not result.overrun and not result.rejected,
            'UART rejected command changed the running image')
    host.stop_uart_stream()
    retained = check_packet(host, 0x253)
    require(not host.stream_status() & 8 and host.page(0) & 7 == 2, 'UART STOP ownership boundary')
    simulation.device = None
    controls.append(dict(name='enabled-session-command-reservation-and-stop', commands=rejected_commands,
        retained_after_stop=retained, wire=peer.report(), automatic_consumption=False))

    # Serial core reset retains the unread mailbox and committed program.
    host.command(Command.RESET)
    require(not host.stream_status() & 8 and host.page(0) & 7 == 2, 'UART serial reset did not disarm')
    after_reset = check_packet(host, 0x253)
    peer = scheduled_peer(simulation, item, [0xa6])
    simulation.device = peer
    host.arm_uart_stream()  # An unread packet does not prevent explicit rearm.
    advance_to(host, (peer.frames[-1].end + 99) // 100 + 5)
    after_arrival = check_packet(host, 0x253, overrun=True)
    host.stop_uart_stream()
    host.consume()
    host.clear_flags()
    simulation.device = None
    controls.append(dict(name='serial-reset-retains-and-explicit-rearm-drops',
        reset_boundary='serial command7 core reset; mailbox retained', retained_after_reset=after_reset,
        retained_after_new_arrival=after_arrival, wire=peer.report(), consumed=True, flags_cleared=True))

    # External reset interrupts an incomplete frame and flushes every channel flag.
    peer = scheduled_peer(simulation, item, [0x53])
    simulation.device = peer
    host.arm_uart_stream()
    advance_to(host, (peer.frames[0].start + 99) // 100 + 3 * item['bit_cycles'])
    require(host.page(0) & 1 and host.stream_status() & 8, 'UART active reset did not reach receiving state')
    simulation.device = None
    host.reset()
    require(host.result_status() == 0x10 and host.page(1) == 0 and host.page(2) == 0 and
            not host.page(0) & 7 and simulation.pins.enabled == 0, 'UART external reset did not flush and disarm')
    load(host, evidence, run, 'uart-after-active-reset', source)
    recovery = observe_stream(simulation, host, item, scheduled_peer(simulation, item, [0xa6]))
    controls.append(dict(name='active-external-reset-and-reload',
        reset_boundary='external rst_n through Host.reset', incomplete_frame=True,
        mailbox_flushed=True, supervisor_disarmed=True, image_invalidated=True, recovery=recovery))

    # Reset with an unread completed packet is a different ownership boundary.
    peer = scheduled_peer(simulation, item, [0x53])
    simulation.device = peer
    host.arm_uart_stream()
    host.read_uart_result(timeout_cycles=10_000, consume=False)
    simulation.device = None
    host.reset()
    require(host.result_status() == 0x10 and host.page(1) == 0 and host.page(2) == 0,
            'UART external reset did not flush an unread completed packet')
    controls.append(dict(name='unread-completed-external-reset', old_unread_flushed=True,
                         no_stale_result=True, supervisor_disarmed=True))
    return controls


def fault_controls(simulation, host, evidence, run):
    """Canonical existing E64 programs trigger terminal6/7; neither may rearm."""
    cases = []
    for outcome, source in [(6, Program((1 | (7 << 9) | (2 << 25), 4), 1)),
                            (7, Program((2 | (5 << 25) | (7 << 9), 4), 1))]:
        simulation.device = None
        simulation.incoming = 0
        host.reset()
        name = 'uart-supervisor-terminal' + str(outcome)
        load(host, evidence, run, name, source)
        host.stream_status()
        host.command(Command.STREAM, 1)
        packet = host.read_result(timeout_cycles=128, consume=False)
        require(packet.outcome == outcome and not packet.overrun and not packet.rejected,
                'UART supervisor failure fixture did not reach its declared terminal')
        require(not host.stream_status() & 8 and not host.page(0) & 1,
                'UART timeout/fault failed to disarm')
        try:
            host.read_uart_result(timeout_cycles=0)
        except RuntimeError as error:
            require('canonical RX capture' in str(error),'Unexpected UART failure decode refusal')
        else:
            raise RuntimeError('UART timeout/fault was decoded as a data byte')
        host.advance(32)
        require(check_packet(host, 0, outcome=outcome) == asdict(packet),
                'UART failure rearmed or changed its retained packet')
        host.consume()
        require(not host.stream_status() & 1 and simulation.pins.enabled == 0,
                'UART failure consume or output release failed')
        cases.append(dict(name=name, result=asdict(packet), disarmed=True,
            no_rearm_after32_edges=True, retained_twice=True, consumed=True, outputs_released=True,
            uart_decoder_refused_and_packet_preserved=True,
            boundary='Generic canonical E64 terminal failure; not a UART bad-stop packet.'))
    simulation.incoming = 3
    return cases


def spacing_control(simulation,host,item,source,evidence,run):
    simulation.device=None
    host.reset()
    load(host,evidence,run,'uart-rearm-spacing-control',source)
    start=(simulation.cycle+430)*100+1
    peer=UARTStreamPeer([Frame(start,0,770),Frame(start+7700,0,770)],input_pin=item['input_pin'])
    simulation.device=peer
    host.arm_uart_stream()
    armed=simulation.cycle
    end=(peer.frames[-1].end+99)//100+5
    expected=peer.completions(8,armed,end)
    require([(e.byte,e.framing_error) for e in expected]==[(0,False)],
            'UART spacing control must contain one valid arrival and a missed second start')
    first=host.read_uart_result(timeout_cycles=10_000,consume=True)
    require(first.byte==0 and not first.framing_error and not first.overrun,'UART spacing first frame')
    advance_to(host,end)
    require(not host.stream_status()&3,'UART rearm spacing loss was mislabeled as pending/overrun')
    host.stop_uart_stream()
    simulation.device=None
    return dict(name='single-frame-bound-does-not-guarantee-stream-rearm',declared_frames=2,
        actual_arrivals=1,first=asdict(first),second_start_missed=True,overrun=False,wire=peer.report(),
        boundary='Finite RX8/TXbit770-quanta phase counterexample; stronger stream bound fails. '
                 'Loss precedes mailbox admission and is distinct from consumer overrun.')


def wrong_capture_slots(source):
    """Keep a canonical wire program but overwrite every capture into slot0."""
    words, changed = [], 0
    for word in source.words:
        for offset in (29,35):
            if word & (1 << offset) and (word >> (offset + 2) & 15) != 8:
                changed += bool(word & (15 << (offset + 2)))
                word &= ~(15 << (offset + 2))
        words.append(word)
    require(changed, 'UART capture mutation found no distinct destinations')
    return replace(source, words=tuple(words))


def program_mutation_controls(simulation, host, item, source, evidence, run):
    name = 'uart-wrong-capture-slots'
    simulation.device = None
    host.reset()
    load(host, evidence, run, name, wrong_capture_slots(source))
    peer = scheduled_peer(simulation, item, [0x53])
    simulation.device = peer
    host.arm_uart_stream()
    armed = simulation.cycle
    packet = host.read_result(timeout_cycles=10_000, consume=False)
    expected = peer.completions(item['bit_cycles'], armed,
                                (peer.frames[-1].end + 99) // 100 + 5)
    # The raw independent sender is intact, but the canonical image no longer
    # preserves byte/stop slots. Do not let a generic upload certificate stand
    # in for a UART compiler certificate or a decoded protocol result.
    require(packet.outcome == 5 and packet.samples != 0x253,
            'UART canonical capture corruption escaped decoded result checking')
    require([(e.byte,e.framing_error) for e in expected] == [(0x53,False)],
            'UART capture control did not preserve the independently scheduled valid frame')
    retained = host.read_result(timeout_cycles=0, consume=False)
    require(retained == packet, 'UART mutation changed an unread packet')
    host.stop_uart_stream()
    host.consume()
    simulation.device = None
    return [dict(name=name, canonical_upload_certificate_passed=True, refused_by='decoded-byte/stop oracle',
        result=asdict(packet), intended_samples=0x253, retained_twice=True, consumed=True,
        wire=peer.report(), protocol_refinement_claimed=False)]


def completion_edge_reservation(simulation, host, item, *, require_all_rejected=True):
    """Serial BEGIN delivery near each represented completion/rearm edge."""
    observations=[]
    for lead in (288,289,290,291,292,293):
        peer=scheduled_peer(simulation,item,[0x53],start_after=1000)
        simulation.device=peer
        host.arm_uart_stream()
        end=(peer.frames[-1].end+99)//100+5
        event=peer.completions(item['bit_cycles'],simulation.cycle,end)[0]
        advance_to(host,event.core_edge-lead)
        before=simulation.cycle
        host.command(Command.BEGIN)
        status,live=host.stream_status(),host.page(0)
        rejected=bool(status&4) and not bool(live&4)
        observations.append(dict(serial_frame_first_edge=before+1,serial_frame_last_edge=before+292,
            command_delivery_edge=before+290,command_delivery_boundary='phase_cycles2 serial sampler/receiver/control pipeline',
            lead_cycles=lead,core_completion_edge=event.core_edge,mailbox_arrival_edge=event.mailbox_edge,
            status=status,live=live,rejected=rejected))
        if not rejected:
            require(not require_all_rejected,'UART enabled session admitted BEGIN around its completion edge')
            simulation.device=None
            return dict(observations=observations,refused_mutant=True,
                        refused_by='completion-edge session ownership; staged BEGIN accepted')
        require(status&8,'UART completion-edge reservation disarmed unexpectedly')
        host.stop_uart_stream()
        host.consume()
        host.clear_flags()
        simulation.device=None
    require(require_all_rejected,'UART reservation corruption was not detected by any completion-edge phase')
    return dict(name='completion-edge-serial-reservation',observations=observations,all_rejected=True)


def active_stop_control(simulation,host,item,source,evidence,run):
    simulation.device=None
    host.reset()
    load(host,evidence,run,'uart-active-stop-source',source)
    peer=scheduled_peer(simulation,item,[0x53])
    simulation.device=peer
    host.arm_uart_stream()
    old=host.read_uart_result(timeout_cycles=100_000,consume=False)
    host.stop_uart_stream()
    simulation.device=None
    peer=scheduled_peer(simulation,item,[0xa6])
    simulation.device=peer
    host.arm_uart_stream()
    advance_to(host,(peer.frames[0].start+99)//100+3*item['bit_cycles'])
    require(host.page(0)&1,'UART STOP did not interrupt an active long frame')
    host.stop_uart_stream()
    require(host.read_uart_result(timeout_cycles=0,consume=False)==old,
            'UART active STOP failed to retain the oldest unread byte without a new arrival')
    require(not host.stream_status()&8 and not host.page(0)&1,'UART active STOP failed to quiesce')
    simulation.device=None
    host.consume()
    return dict(name='active-stop-retains-unread',bit_cycles=item['bit_cycles'],old=asdict(old),
        incomplete_new_frame=True,mailbox_unchanged=True,overrun=False,disarmed=True,consumed=True,
        reset_boundary='serial command6 word0; core abort, mailbox retained',wire=peer.report())


def disabled_compatibility(simulation,host,uart_item,uart_source,spi_source,i2c_source,evidence,run):
    """Previous one-shot protocol compilers on the new disabled supervisor."""
    cases=[]
    simulation.device=None
    host.reset()
    for name,source in [('disabled-uart-rx',uart_source),('disabled-spi',spi_source),('disabled-i2c-write',i2c_source)]:
        require(host.result_status()&0x18==0x10,'Disabled supervisor changed the version1 marker')
        load(host,evidence,run,name,source)
        if name=='disabled-uart-rx':
            peer=scheduled_peer(simulation,uart_item,[0xa6]);expected=0x2a6
        elif name=='disabled-spi':
            peer=SPIPeer(0,(0xa6,0x53),(0x96,0x3c),4);expected=None
        else:
            peer=I2CWritePeer(0x53,[0xa6,0x53],[0,0,0],phase_cycles=4);expected=0
        simulation.device=peer
        host.start()
        packet=host.read_result(timeout_cycles=100_000,consume=False)
        require(packet.outcome==5 and not packet.overrun and not packet.rejected,
                'Disabled one-shot compatibility outcome/flags')
        require(packet==host.read_result(timeout_cycles=0,consume=False),'Disabled compatibility retention')
        if name=='disabled-spi':
            require(spi_result_bytes(packet.samples,2)==(0x96,0x3c),'Disabled SPI byte decode')
            wire=peer.check()
        elif name=='disabled-i2c-write':
            require(packet.samples==expected,'Disabled I2C ACK decode');wire=peer.check()
        else:
            require(packet.samples==expected,'Disabled UART byte/stop decode');wire=peer.report()
        host.consume()
        require(not host.result_status()&1 and not host.result_status()&8,'Disabled one-shot consume or supervisor state')
        simulation.device=None
        cases.append(dict(name=name,result=asdict(packet),retained_twice=True,consumed=True,
            disabled_marker_unchanged=True,wire=wire))
    return cases


def replace_assignment(text,name,expression,*,sequential=False):
    operator='<=' if sequential else '='
    pattern=rf'(\b{re.escape(name)}\s*{re.escape(operator)})\s*[^;]+;'
    changed,count=re.subn(pattern,lambda m:m[1]+' '+expression+';',text)
    require(count==1,'UART RTL mutation requires exactly one represented assignment: '+name)
    require(changed!=text,'UART RTL mutation had no effect')
    return changed


def supervisor_mutation(text,kind):
    if kind=='no-rearm':
        pattern=r'(wire\s+_GEN_\d+\s*=)\s*~\(~(_GEN_\d+) & ~\([^;]*r_stream_enabled[^;]*\)\);'
        changed,count=re.subn(pattern,lambda m:m[1]+' '+m[2]+';',text)
    elif kind=='no-reservation':
        pattern=r'r_stream_enabled & ~(_GEN_\d+) \? 3\'h6 : (_GEN_\d+)'
        changed,count=re.subn(pattern,lambda m:"1'h0 ? 3'h6 : "+m[2],text)
    else:
        raise ValueError('Unknown supervisor corruption')
    require(count==1 and changed!=text,'UART supervisor mutation requires one unambiguous gate: '+kind)
    return changed


def rtl_mutation_controls(evidence,run,closure,cad,models,source,item,tb):
    negatives=[]
    original=(evidence.out/'host-result-component.sv').read_text()
    for name,target,expression in [('buffer-overwrite-unread','next_result_samples',
            'pin_rst_n ? core_samples : 16\'h0'),
        ('buffer-clear-after-drop','next_result_overrun',
            "state_result_control_second[1] ? 1'h0 : state_result_overrun")]:
        path=evidence.out/(name+'.sv');path.write_text(replace_assignment(original,target,expression))
        evidence.freeze_generated(path)
        executable=evidence.out/(name+'.vvp')
        run([cad/'iverilog','-B',closure.backend,'-g2012','-s','uart_stream_result_tb','-o',executable,path,tb],name+'-compile')
        evidence.freeze_generated(executable);closure.check_executable(executable)
        log=run([cad/'vvp',executable],name+'-rejected',reject='UART_BUFFER')
        negatives.append(dict(name=name,refused_by='actual mailbox component truth table',log=name+'-rejected.log'))
    original=(evidence.out/'design.sv').read_text()
    for kind in ('no-rearm','no-reservation'):
        name='supervisor-'+kind
        path=evidence.out/(name+'.sv');path.write_text(supervisor_mutation(original,kind));evidence.freeze_generated(path)
        executable=evidence.out/(name+'.vvp')
        run([cad/'iverilog','-B',closure.backend,'-g2012','-DFUNCTIONAL','-s','host_bridge','-o',executable,
            path,ROOT/'test/host_bridge.sv',ROOT/'test/paired_chip.sv',*models],name+'-compile')
        evidence.freeze_generated(executable);closure.check_executable(executable)
        with Simulation(cad/'vvp',executable) as simulation:
            host=Host(simulation,image_format=PAIRED_FORMAT);host.reset()
            load(host,evidence,run,name+'-source',source)
            if kind=='no-reservation':
                detail=completion_edge_reservation(simulation,host,item,require_all_rejected=False)
            else:
                peer=scheduled_peer(simulation,item,[0x53,0xa6]);simulation.device=peer
                try:
                    observe_stream(simulation,host,item,peer)
                except TimeoutError as error:
                    require('No result before host timeout' in str(error),'UART rearm mutation unexpected failure')
                    detail=dict(refused_by='second independently scheduled byte absent',reason=str(error),wire=peer.report())
                else:
                    raise RuntimeError('UART no-rearm RTL corruption escaped the finite stream oracle')
            negatives.append(dict(detail,name=name,refused_mutant=True))
    return negatives


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--tag', required=True)
    args = parser.parse_args()
    out = fresh_directory(ROOT / 'build/host', args.tag)
    sources = [ROOT/'Pinwheel.lean', *sorted((ROOT/'Pinwheel').rglob('*.lean')),
        *[ROOT/n for n in ('lakefile.toml','lake-manifest.json','lean-toolchain',
            'test/PairedStreamEmit.lean','test/UARTBufferedSupervisor.lean','test/host_bridge.sv',
            'test/paired_chip.sv','test/SPITransactions.lean','test/I2CWriteTransactions.lean',
            'tools/hardware-toolchain.json','tools/storage-macros.json')],
        *[ROOT/'scripts'/n for n in ('check-uart-stream.py','uart_stream_peer.py','capability_receipt.py',
            'protocol_tool_closure.py','pinwheel_host.py','pinwheel_sim.py','pad_io.py','pad_peers.py','i2c_peers.py',
            'host_demo.py','paired_execution.py','paired_image_certificate.py','execution-vectors.py',
            'validation_run.py','process_group.py')]]
    cad = ROOT/'build/tools/oss-cad-suite/bin'
    circt = ROOT/'build/tools/firtool-1.159.0/bin/circt-opt'
    closure = ProtocolToolClosure(ROOT,circt,cad/'iverilog',cad/'vvp')
    models = [ROOT/'build/storage/macros'/n for n in
        ('RM_IHPSG13_1P_512x64_c2_bm_bist.v','RM_IHPSG13_1P_core_behavioral_bm_bist.v')]
    locked = json.loads((ROOT/'tools/storage-macros.json').read_text())['files_sha256']
    require(all(sha(p)==locked['verilog/'+p.name] for p in models), 'UART unpinned SRAM models')
    evidence = CapabilityEvidence(ROOT,out,sources,closure.files,models)
    started = time.monotonic()
    run = Commands(ROOT,out,default_timeout=600)
    lean_version = run(['lake','env','lean','--version'],'lean-version').strip()
    version = (ROOT/'lean-toolchain').read_text().strip().split(':v')[-1]
    require(re.search(r'Lean \(version '+re.escape(version)+r'(?:,|\s)',lean_version), 'UART Lean toolchain mismatch')
    run(['lake','build','Pinwheel'],'build')
    compiled = out/'compiled'
    run(['lake','env','lean','-DwarningAsError=true','--run','test/UARTBufferedSupervisor.lean','--emit',compiled],'compile')
    images = compiler_images(evidence.capture(compiled/'images.txt','images.txt'))
    entries = metadata(evidence.capture(compiled/'metadata.json','metadata.json'),images)
    compatibility_images={}
    for label,entrypoint in [('spi','SPITransactions'),('i2c','I2CWriteTransactions')]:
        destination=out/('compatibility-'+label)
        run(['lake','env','lean','-DwarningAsError=true','--run','test/'+entrypoint+'.lean',destination],
            'compile-compatibility-'+label)
        compatibility_images[label]=compiler_images(evidence.capture(destination/'images.txt',label+'-images.txt'))
        evidence.capture(destination/'metadata.json',label+'-metadata.json')
    run(['lake','env','lean','-DwarningAsError=true','--run','test/PairedStreamEmit.lean',out],'emit')
    evidence.freeze_generated(out/'core.mlir')
    evidence.freeze_generated(out/'assembly.json')
    artifact_digests = {}
    for name in ('chip','host-result-component'):
        mlir=out/(name+'.mlir')
        artifact_digests[mlir.name]=evidence.freeze_generated(mlir)
        text=run([circt,mlir,'--canonicalize','--lower-seq-to-sv','--lower-hw-to-sv',
            '--hw-legalize-modules','--export-verilog','-o','/dev/null'],'export-'+name)
        path=out/('design.sv' if name=='chip' else name+'.sv')
        path.write_text(text)
        artifact_digests[path.name]=evidence.freeze_generated(path)
    executable=out/'host.vvp'
    run([cad/'iverilog','-B',closure.backend,'-g2012','-DFUNCTIONAL','-s','host_bridge','-o',executable,
         out/'design.sv',ROOT/'test/host_bridge.sv',ROOT/'test/paired_chip.sv',*models],'compile-simulation')
    artifact_digests[executable.name]=evidence.freeze_generated(executable)
    closure.check_executable(executable)
    vectors=component_vectors()
    tb=out/'buffer-tb.sv'
    tb.write_text(component_testbench(vectors))
    evidence.freeze_generated(tb)
    buffer_executable=out/'buffer.vvp'
    run([cad/'iverilog','-B',closure.backend,'-g2012','-s','uart_stream_result_tb','-o',buffer_executable,
        out/'host-result-component.sv',tb],'compile-buffer')
    evidence.freeze_generated(buffer_executable)
    closure.check_executable(buffer_executable)
    buffer_log=run([cad/'vvp',buffer_executable],'buffer-rtl')
    require(f'UART buffer RTL: {len(vectors)} vectors passed.' in buffer_log,'UART buffer vectors incomplete')
    cases=[]
    timings=[]
    with Simulation(cad/'vvp',executable) as simulation:
        host=Host(simulation,image_format=PAIRED_FORMAT)
        host.reset()
        for item in entries:
            source=load(host,evidence,run,item['name'],images[item['name']])
            period=item['bit_cycles']
            payload=[0,255,0x55,0xaa,0x53,0xa6,0,0] if period<=16 else [0x53]
            peer=scheduled_peer(simulation,item,payload)
            result=observe_stream(simulation,host,item,peer)
            cases.append(dict(name=item['name']+'-ready',**result))
            tx_cycles=period if period<=256 else 1
            timings.append(certify_timing(evidence,run,item['name'],bit_cycles=period,
                input_pin=item['input_pin'],tx_cycles=tx_cycles,tx_tick=period*100//tx_cycles,
                rx_tick=100,phase=0,start=peer.frames[0].start,payload=payload))
            if period==16:
                for suffix,policy,payload,kwargs in [
                    ('bad-stop','ready',[0x53,0xa6],dict(stops=[0,1],gap=16)),
                    ('false-start','ready',[0x53],dict(false_start=True)),
                    ('held-low','ready',[0xa6],dict(initial_low=True)),
                    ('stall','stall',[0x53,0xa6,0x53],{}),
                    ('simultaneous','simultaneous',[0x53,0xa6],{}),
                    ('clear-drop','clear-drop',[0x53,0xa6,0x53],{})]:
                    peer=scheduled_peer(simulation,item,payload,**kwargs)
                    cases.append(dict(name=item['name']+'-'+suffix,
                        **observe_stream(simulation,host,item,peer,policy=policy)))
                for tick,phase in itertools.product((97,103),(0,99)):
                    name=item['name']+f'-tick{tick}-phase{phase}'
                    peer=scheduled_peer(simulation,item,[0x53,0xa6,0,0],tx_tick=tick,rx_phase=phase)
                    cases.append(dict(name=name,**observe_stream(simulation,host,item,peer)))
                    timings.append(certify_timing(evidence,run,name,bit_cycles=period,input_pin=item['input_pin'],
                        tx_cycles=period,tx_tick=tick,rx_tick=100,phase=phase,start=peer.frames[0].start,payload=[0x53,0xa6,0,0]))
        control_item=next(x for x in entries if x['bit_cycles']==16 and x['input_pin']==0)
        control_source=images[control_item['name']]
        controls=session_controls(simulation,host,control_item,control_source,evidence,run)
        load(host,evidence,run,'uart-reservation-source',control_source)
        controls.append(completion_edge_reservation(simulation,host,control_item))
        long_item=next(x for x in entries if x['bit_cycles']==257 and x['input_pin']==0)
        controls.append(active_stop_control(simulation,host,long_item,images[long_item['name']],evidence,run))
        faults=fault_controls(simulation,host,evidence,run)
        short_item=next(x for x in entries if x['bit_cycles']==8 and x['input_pin']==0)
        controls.append(spacing_control(simulation,host,short_item,images[short_item['name']],evidence,run))
        program_negatives=program_mutation_controls(simulation,host,control_item,control_source,evidence,run)
        compatibility=disabled_compatibility(simulation,host,control_item,control_source,
            compatibility_images['spi']['spi-mode0-2bytes'],
            compatibility_images['i2c']['i2c-write-2-success'],evidence,run)
    negatives=rtl_mutation_controls(evidence,run,closure,cad,models,control_source,control_item,tb)
    unsafe=out/'unsafe-clock-certificate.lean'
    unsafe_text=timing_certificate('Unsafe',8,0,1,770,100,0,43001,[0,0])
    unsafe_text=unsafe_text.replace('theorem safe :','theorem single_safe : Link.Safe timing latency := by decide\ntheorem safe :')
    unsafe.write_text(unsafe_text)
    evidence.freeze_generated(unsafe)
    unsafe_log=run(['lake','env','lean','-DwarningAsError=true',unsafe],'unsafe-clock-rejected',reject='decide')
    require(run.records[-1]['exit_code']!=0 and
            'Tactic `decide` proved that the proposition\n  StreamLink.Safe timing latency\nis false' in unsafe_log,
            'Unsafe UART stream timing certificate was not kernel refused')
    require(run(['lake','env','lean','--version'],'lean-version-closeout').strip()==lean_version,
            'UART Lean version changed')
    closure.closeout()
    evidence.closeout()
    report=dict(schema=1,status='passed',candidate='paired-uart-stream-digital',A_accepted=False,
        physical_evidence_reused=False,cad_seconds=0,pad_map=PAD_MAP,lean_version=lean_version,
        lean_version_unchanged=True,mlir_sha256=artifact_digests['chip.mlir'],rtl_sha256=artifact_digests['design.sv'],
        executable_sha256=artifact_digests['host.vvp'],buffer_rtl_vectors=len(vectors),cases=cases,
        session_controls=controls,failure_controls=faults,disabled_compatibility=compatibility,
        semantic_corruptions=program_negatives+negatives,
        unsafe_clock_control=dict(rx_cycles=8,tx_cycles=1,tx_tick=770,rx_tick=100,
            single_frame_safe=True,
            safe_certificate_rejected=True,log='unsafe-clock-rejected.log',
            boundary='Failure of the stronger sufficient stream bound; no universal failure claim outside it.'),
        timing_certificates=timings,bundled_tool_closure=closure.identity(),commands=run.records,
        elapsed_seconds=round(time.monotonic()-started,3),**evidence.identity(),
        boundary='Finite resolved digital UART streams and actual buffer expressions; '
            'clock certificates prove digital sufficient premises separately. No metastability, analog baud, '
            'concurrent TX/RX scheduling, extra FIFO or physical acceptance claim.')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(dict(status='passed',cases=len(cases),buffer_vectors=len(vectors),timings=len(timings)),indent=2))
    print(out/'report.json')


if __name__=='__main__':
    main()
