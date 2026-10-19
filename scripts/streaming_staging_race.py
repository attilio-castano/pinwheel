"""Public-pin terminal-entry staging race for streaming-quad-v1.

The request close is aligned using resolved protocol clock edges only. No DUT
register, source-state prediction or private hierarchy drives the stimulus.
This additional producer leaves the first16 and extra7 case suites unchanged.
"""
from dataclasses import asdict
import json
from pathlib import Path
import re

from pad_io import OUTPUT_MASK, PadDrive
from streaming_adversarial import physical_case
from streaming_compile import Cell, Instruction, lower, validate_image
from streaming_transport import Code, Opcode, QuadTransport
from streaming_wire_cases import require


HALF_CYCLES = 256
VARIANTS = ((33, 32), (65, 64))


def reply_for(bit_count):
    if bit_count not in (33, 65):
        raise ValueError('The staging corpus uses33 or65 protocol bits')
    return tuple(bool((0xA5C39669D28F017B >> bit) & 1)
        for bit in range(63, 63 - (bit_count - 1), -1)) + (True,)


def image_for(terminal):
    if terminal not in ('halt', 'fault'):
        raise ValueError('A staging race requires HALT or FAULT')
    cell = Cell(low_cycles=HALF_CYCLES, high_cycles=HALF_CYCLES,
        low_levels=0, low_enabled=7, high_levels=2, high_enabled=7,
        transmit=False, receive=True)
    image = lower((Instruction('stream', cell), Instruction(terminal)),
        idle_levels=0, idle_enabled=7)
    validate_image(image)
    return image


class ReceivePeer:
    """Independent receive source; validates physical clock chronology."""
    def __init__(self, bit_count):
        self.bit_count, self.reply = bit_count, reply_for(bit_count)
        self.previous_clock = 0
        self.rises, self.falls, self.bits = [], [], []
        self.miso, self.pending = self.reply[0], None

    def drive(self, cycle, pads, ui=0):
        pads.logical
        clock, mosi = pads.bit(3), pads.bit(2)
        if pads.enabled != OUTPUT_MASK:
            require(pads.enabled == 0 and (not self.rises or len(self.falls) == self.bit_count),
                'Race program must drive all three protocol pads while executing')
            return PadDrive(int(self.miso), 1)
        if clock != self.previous_clock:
            if clock:
                require(len(self.rises) < self.bit_count, 'Race peer observed an extra protocol rising edge')
                if self.falls:
                    require(cycle - self.falls[-1] >= HALF_CYCLES,
                        'Race peer observed a shortened low phase')
                self.rises.append(cycle)
                self.bits.append(bool(mosi))
            else:
                require(len(self.falls) < len(self.rises), 'Race peer observed an unmatched falling edge')
                require(cycle - self.rises[-1] == HALF_CYCLES,
                    'Race peer observed a stalled or shortened high phase')
                self.falls.append(cycle)
                self.pending = (cycle + 1, self.reply[min(len(self.falls), self.bit_count - 1)])
        if self.pending is not None and cycle >= self.pending[0]:
            self.miso, self.pending = self.pending[1], None
        self.previous_clock = clock
        # High-phase decoys distinguish the LOW→HIGH pre-edge sample from a
        # later receipt or high-phase sample.
        return PadDrive(int(not self.miso if clock else self.miso), 1)

    def check(self):
        require(len(self.rises) == len(self.falls) == self.bit_count,
            'Race peer did not observe the exact number of complete protocol cells')
        require(not any(self.bits), 'Receive-only generic cell unexpectedly changed its TX pad')
        return dict(bits=self.bit_count, clock_edges=self.bit_count * 2,
            high_phase_edges=sorted(set(fall - rise for rise, fall in zip(self.rises, self.falls))),
            final_rise=self.rises[-1], final_fall=self.falls[-1],
            callback_delay_cycles=1, sampler_delay_cycles=2, peer_tco_cycles=1)


class CloseOnFinalFall:
    """Hold one complete host request until a public protocol clock boundary."""
    def __init__(self, rtl, peer):
        self.rtl, self.peer = rtl, peer
        self.csn, self.sck, self.mosi, self.count = 1, 0, 0, 0
        self.armed, self.trigger = False, None

    @property
    def cycle(self): return self.rtl.cycle

    def cold_reset(self):
        self.rtl.cold_reset()
        self.csn, self.sck, self.mosi, self.count = 1, 0, 0, 0

    def arm(self):
        require(not self.armed and self.trigger is None, 'Only one race alignment is permitted')
        self.armed = True

    def tick(self, *, csn, sck, mosi):
        if not csn and self.csn:
            self.count = 0
        if not csn and sck and not self.sck:
            self.count += 1
        if self.armed and csn and not self.csn:
            require(self.count == 44, 'Race alignment requires an exact completed44-nibble request')
            held_from = self.rtl.cycle
            while len(self.peer.rises) < self.peer.bit_count:
                require(self.rtl.cycle - held_from < 2048, 'Final public protocol rising edge was not reached')
                self.rtl.tick(csn=0, sck=self.sck, mosi=self.mosi)
            closing_cycle = self.peer.rises[-1] + HALF_CYCLES
            require(self.rtl.cycle < closing_cycle, 'Completed request arrived after the final falling edge')
            while self.rtl.cycle < closing_cycle - 1:
                self.rtl.tick(csn=0, sck=self.sck, mosi=self.mosi)
            result = self.rtl.tick(csn=csn, sck=sck, mosi=mosi)
            require(self.peer.falls and self.peer.falls[-1] == self.rtl.cycle == closing_cycle,
                'Physical request close did not coincide with the final protocol falling edge')
            self.trigger = dict(request_nibbles=self.count, held_from=held_from,
                held_edges=closing_cycle - held_from - 1, closing_cycle=closing_cycle,
                final_rise=self.peer.rises[-1], final_fall=self.peer.falls[-1],
                alignment='resolved public protocol rising edge plus declared high duration')
            self.armed = False
        else:
            result = self.rtl.tick(csn=csn, sck=sck, mosi=mosi)
        self.csn, self.sck, self.mosi = csn, sck, mosi
        return result


def terminal_race(rtl, *, depth, terminal, bit_count=33, offered_bits=32):
    if (bit_count, offered_bits) not in VARIANTS:
        raise ValueError('Unsupported terminal staging variant')
    image = image_for(terminal)
    peer = ReceivePeer(bit_count)
    # Attach after installing idle enables; every peer observation then has
    # fully resolved driven protocol pads.
    link = CloseOnFinalFall(rtl, peer)
    transport = QuadTransport(link)
    transport.cold_reset()
    for address, word in enumerate(image.words):
        require(transport.request(Opcode.WRITE, address=address, word=word).code is Code.ACCEPTED,
            'Race image row was not accepted')
    commit = transport.request(Opcode.COMMIT, count=len(image.words), idle_levels=0, idle_enabled=7)
    require(commit.code is Code.ACCEPTED and commit.valid, 'Race image COMMIT failed')
    rtl.device = peer
    started = transport.request(Opcode.START, expected_generation=commit.generation, bit_count=bit_count)
    require(started.code is Code.ACCEPTED, 'Race START was not accepted')
    while len(peer.rises) < 32:
        require(rtl.cycle < 40000, 'First32 receive captures did not occur')
        transport.idle(1)
    exported = transport.exchange(started.tag, 0, 0)
    require(exported.code is Code.ACCEPTED and exported.busy and exported.rx_valid == 32 and
        exported.rx_bits == peer.reply[:32] and exported.tx_accepted == 0,
        'Race fixture lacks a busy owner with an outstanding32-bit exported interval')
    require(len(peer.rises) == 32, 'Export took too long to align the final stream cell')
    if bit_count == 65:
        while len(peer.rises) < 64:
            require(rtl.cycle < 40000, 'Second32 receive captures did not occur')
            transport.idle(1)
        exported = transport.exchange(started.tag, 0, 32)
        require(exported.code is Code.ACCEPTED and exported.busy and exported.rx_start == 32 and
            exported.rx_bits == peer.reply[32:64], 'Second exported interval differs from the independent peer')
        require(len(peer.rises) == 64, 'Second export took too long to align the final stream cell')
    link.arm()
    raced = transport.exchange(started.tag, 0, bit_count - 1, (False,) * offered_bits)
    require(link.trigger is not None, 'No actual terminal-entry request alignment occurred')
    require(raced.code is Code.ACCEPTED and raced.tx_accepted == offered_bits and raced.retained and
        not raced.busy and raced.fault == (terminal == 'fault') and
        raced.rx_start == bit_count - 1 and raced.rx_bits == peer.reply[-1:] and
        raced.tx_free == depth - offered_bits // 32 and raced.rx_queued == 0,
        'A bulk request admitted before terminal entry lost its staged TX prefix or custody: ' +
        repr(asdict(raced)) + '; alignment=' + repr(link.trigger))
    require(raced.tag == exported.tag == started.tag, 'Terminal staging changed the owner identity')
    held_export = transport.request(Opcode.RELEASE, tag=started.tag)
    require(held_export.code is Code.REJECTED and held_export.retained,
        'Matching RELEASE discarded the simultaneously exported final sample')
    acknowledged = transport.exchange(started.tag, offered_bits, bit_count)
    require(acknowledged.code is Code.ACCEPTED and not acknowledged.rx_valid and not acknowledged.rx_queued,
        'Final RX acknowledgement failed')
    held = transport.request(Opcode.RELEASE, tag=started.tag)
    require(held.code is Code.REJECTED and held.retained and held.tx_accepted == offered_bits,
        'Matching RELEASE discarded the admitted but unconsumed TX word')
    cancelled = transport.request(Opcode.WARM_RESET)
    require(cancelled.code is Code.ACCEPTED and not cancelled.busy and not cancelled.retained and
        not cancelled.valid and cancelled.generation == started.generation and
        cancelled.transfer == started.transfer and not cancelled.tx_accepted and not cancelled.rx_queued,
        'Explicit reset did not cancel retained staging while preserving allocation counters')
    return dict(kind='terminal_staging_race', depth=depth, terminal=terminal,
        owner_tag=started.tag, bit_count=bit_count, image_words=list(image.words),
        old_export_start=bit_count - 33, old_export_bits=32, alignment=link.trigger,
        admitted_tx_bits=offered_bits, staged_beats=offered_bits // 32,
        tx_accepted_after_terminal=raced.tx_accepted, terminal_retained=True,
        final_sample_preserved=True, simultaneous_rx_pop=True, old_export_ack_applied_once=True,
        release_blocks_unconsumed_tx=True, explicit_cancel=True,
        raced_reply=asdict(raced), held_export_reply=asdict(held_export), held_reply=asdict(held),
        cancelled_reply=asdict(cancelled), peer=peer.check())


def check_races(result):
    if (result.get('schema') != 'pinwheel.streaming-terminal-staging.v1' or
            result.get('passed') is not True or result.get('depth') not in (2, 4) or
            [(case.get('bit_count'), case.get('terminal')) for case in result.get('cases', [])] !=
                [(bits, terminal) for bits, _ in VARIANTS for terminal in ('halt', 'fault')]):
        raise RuntimeError('Both word counts and both distinct terminal-entry staging cases are mandatory')
    for case in result['cases']:
        bits = case['bit_count']
        offered = bits - 1
        if (case.get('passed') is not True or case.get('depth') != result['depth'] or
                case.get('owner_tag') != 65537 or
                case.get('old_export_start') != bits - 33 or case.get('old_export_bits') != 32 or
                case.get('admitted_tx_bits') != offered or case.get('staged_beats') != offered // 32 or
                case.get('tx_accepted_after_terminal') != offered or
                any(case.get(key) is not True for key in ('terminal_retained', 'final_sample_preserved',
                    'simultaneous_rx_pop', 'old_export_ack_applied_once', 'release_blocks_unconsumed_tx', 'explicit_cancel')) or
                case.get('physical_edges', 0) <= 0 or
                case.get('trace', {}).get('edges') != case.get('physical_edges') or
                case.get('trace', {}).get('bytes') != case['physical_edges'] * 20 or
                not re.fullmatch(r'[0-9a-f]{64}', case.get('trace', {}).get('sha256', ''))):
            raise RuntimeError('Incomplete actual-wire terminal staging/custody case')
        alignment, peer = case.get('alignment', {}), case.get('peer', {})
        if (alignment.get('request_nibbles') != 44 or alignment.get('held_edges', 0) <= 0 or
                alignment.get('closing_cycle') != alignment.get('final_fall') or
                alignment.get('final_fall', 0) - alignment.get('final_rise', 0) != HALF_CYCLES or
                peer.get('bits') != bits or peer.get('clock_edges') != bits * 2 or
                peer.get('high_phase_edges') != [HALF_CYCLES] or
                peer.get('final_fall') != alignment.get('closing_cycle')):
            raise RuntimeError('Terminal race lacks distinguishing public-edge alignment evidence')
        raced, held, cancelled = (case.get(name, {}) for name in ('raced_reply', 'held_reply', 'cancelled_reply'))
        if (raced.get('code') != Code.ACCEPTED or raced.get('tag') != case['owner_tag'] or
                raced.get('tx_accepted') != offered or raced.get('rx_start') != bits - 1 or
                raced.get('rx_valid') != 1 or raced.get('data') != 1 or
                raced.get('tx_free') != result['depth'] - offered // 32 or raced.get('rx_queued') != 0 or
                raced.get('flags') != (13 if case['terminal'] == 'fault' else 5) or
                held.get('code') != Code.REJECTED or held.get('tag') != case['owner_tag'] or
                held.get('tx_accepted') != offered or not held.get('flags', 0) & 4 or
                cancelled.get('code') != Code.ACCEPTED or cancelled.get('tag') != case['owner_tag'] or
                cancelled.get('flags') != 0 or cancelled.get('tx_accepted') != 0 or cancelled.get('rx_queued') != 0):
            raise RuntimeError('Terminal race receipts do not establish retained storage and explicit cancellation')
    if result.get('physical_edges') != sum(case['physical_edges'] for case in result['cases']):
        raise RuntimeError('Terminal race aggregate edge count differs')


def run_races(vvp, executable, directory, *, depth):
    if depth not in (2, 4):
        raise ValueError('Qualified staging depths are2 or4')
    directory = Path(directory)
    directory.mkdir(parents=True, exist_ok=False)
    cases = []
    for bits, offered in VARIANTS:
        for terminal in ('halt', 'fault'):
            result = physical_case(vvp, executable, directory / (str(bits) + '-' + terminal),
                lambda rtl, terminal=terminal, bits=bits, offered=offered: terminal_race(rtl,
                    depth=depth, terminal=terminal, bit_count=bits, offered_bits=offered))
            result.update(terminal=terminal, bit_count=bits)
            cases.append(result)
    result = dict(schema='pinwheel.streaming-terminal-staging.v1', depth=depth,
        passed=all(case.get('passed') is True for case in cases), cases=cases,
        physical_edges=sum(case.get('physical_edges', 0) for case in cases))
    if result['passed']:
        check_races(result)
    (directory / 'report.json').write_text(json.dumps(result, indent=2) + '\n')
    return result
