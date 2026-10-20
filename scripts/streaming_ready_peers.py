"""Independent resolved SCL/SDA target for the sampled-ready I2C corpus.

Normal stretch timers start at observed SCL falls. The last-poll diagnostic
alone observes the public output-enable release transition for alignment; no
private phase, FIFO, source state or status supplies data or expected results.
"""
from pad_io import PadDrive
from streaming_ready_transport import I2cPlan


def require(value, message):
    if not value:
        raise RuntimeError(message)


def payloads():
    write = bytes([0, 255, 128, 1, 0x55, 0xaa, 0x96, 0x69] +
        [((73 * index + 0x5d) ^ (index >> 1)) & 255 for index in range(8, 64)])
    read = bytes([255, 0, 1, 128, 0xaa, 0x55, 0x3c, 0xc3] +
        [((151 * index + 0xa7) ^ ((3 * index) >> 2)) & 255 for index in range(8, 64)])
    return write, read


def expected_rx(plan, read_data, *, address_ack=True):
    if type(plan) is not I2cPlan or type(address_ack) is not bool or type(read_data) is not bytes or (
            plan.direction == 'read' and len(read_data) != plan.length):
        raise ValueError('Independent I2C target requires exact immutable read data')
    result = list(plan.tx_bits)
    result[8] = not address_ack
    for index in range(plan.length):
        start = 9 + index * 9
        if plan.direction == 'read':
            value = read_data[index] if address_ack else 255
            result[start:start + 8] = [bool((value >> bit) & 1) for bit in range(7, -1, -1)]
        else:
            result[start + 8] = not address_ack
    return tuple(result)


class StreamingI2cPeer:
    PROFILES = ('clean', 'varying', 'lastpoll', 'timeout', 'late')

    def __init__(self, plan, read_data=b'', *, address_ack=True, profile='clean',
            low_cycles=4, high_cycles=4, wait_budget=31, peer_tco=1,
            deadline_slot=11, timeout_slot=50):
        if (profile not in self.PROFILES or type(low_cycles) is not int or type(high_cycles) is not int or
                type(peer_tco) is not int or peer_tco < 0 or low_cycles < peer_tco + 3 or high_cycles < 1 or
                type(wait_budget) is not int or not 3 <= wait_budget <= 255):
            raise ValueError('I2C requires a fresh LOW sampler window and bounded ready budget')
        self.expected = expected_rx(plan, read_data, address_ack=address_ack)
        slots = (deadline_slot,) if profile in ('lastpoll', 'late') else (timeout_slot,) if profile == 'timeout' else ()
        for slot in slots:
            if type(slot) is not int or not 0 < slot < plan.bit_count:
                raise ValueError('Stretch diagnostic slot must be inside the stream')
        self.plan, self.read_data, self.address_ack = plan, read_data, address_ack
        self.profile, self.low_cycles, self.high_cycles = profile, low_cycles, high_cycles
        self.wait_budget, self.tco = wait_budget, peer_tco
        self.deadline_slot, self.timeout_slot = deadline_slot, timeout_slot
        self.previous_scl = self.previous_sda = 1
        self.previous_master_low = False
        self.started_at = self.stopped_at = self.abort_stop_at = self.stop_rise = None
        self.last_fall = self.last_rise = self.last_sda_change = None
        self.bits, self.rises, self.falls = [], [], []
        self.high_durations, self.low_durations, self.master_low_extensions = [], [], []
        self.target_extension_edges = 0
        self.sda = True
        self.pending_sda = None
        self.hold_active, self.hold_until, self.hold_slot = False, None, None
        self.applied_hold = False
        self.stretches, self.deadline_alignment = [], None
        self.callback_cycle = None

    def _target_owns(self, index):
        if index == 8:
            return True
        if index < 9 or not self.address_ack:
            return False
        offset = (index - 9) % 9
        return offset < 8 if self.plan.direction == 'read' else offset == 8

    def _next_sda(self, cycle):
        index = len(self.bits)
        value = self.expected[index] if index < self.plan.bit_count and self._target_owns(index) else True
        self.pending_sda = (cycle + self.tco, value)

    def _arm(self, cycle):
        index = len(self.bits)
        duration = None
        if self.profile == 'varying':
            extra = {11: 5, 31: 9, 127: 3, 255: 13, 512: 7}.get(index)
            if extra is not None:
                duration = self.low_cycles + extra
            elif index == self.plan.bit_count:
                duration = 2 * (self.low_cycles + self.high_cycles) + 8
        diagnostic = self.profile in ('lastpoll', 'late') and index == self.deadline_slot
        timeout = self.profile == 'timeout' and index == self.timeout_slot
        if duration is None and not diagnostic and not timeout:
            return
        self.hold_active, self.hold_until, self.hold_slot = True, (
            cycle + duration if duration is not None else None), index
        self.stretches.append(dict(slot=index, fall=cycle, release_callback=self.hold_until,
            stimulus='public OE release aligned' if diagnostic else 'resolved fall timer' if not timeout else 'held through fault'))
        # While stretched LOW a target may change data. Keep an opposite decoy
        # early, then meet setup before release. A LOW-end capture gets it wrong.
        if index < self.plan.bit_count and self.plan.direction == 'read' and self._target_owns(index):
            self.pending_sda = (cycle + self.tco, not self.expected[index])

    def drive(self, cycle, pads, ui=0):
        if self.callback_cycle is not None and cycle == self.callback_cycle:
            raise RuntimeError('I2C peer requires one callback per recorded edge')
        self.callback_cycle = cycle
        pads.logical
        require(not (pads.levels & pads.enabled & 12), 'I2C master drove a linked wire HIGH')
        require(not pads.enabled & 16, 'I2C unexpectedly drove its unused third protocol output')
        scl, sda = pads.bit(0), pads.bit(1)
        master_low = bool(pads.enabled & 4)
        if self.applied_hold and not master_low and not scl:
            self.target_extension_edges += 1
        if sda != self.previous_sda:
            self.last_sda_change = cycle
            if scl and self.previous_scl:
                if not sda:
                    require(self.started_at is None and self.stopped_at is None, 'I2C extra START or HIGH-phase SDA glitch')
                    self.started_at = cycle
                elif self.started_at is not None:
                    if len(self.bits) == self.plan.bit_count and self.stop_rise is not None:
                        require(self.stopped_at is None and cycle - self.stop_rise >= self.high_cycles,
                            'I2C STOP setup interval is too short')
                        self.stopped_at = cycle
                    else:
                        require(self.profile in ('timeout', 'late'), 'I2C early STOP or HIGH-phase SDA glitch')
                        self.abort_stop_at = cycle
        if self.started_at is not None and self.stopped_at is None and scl != self.previous_scl:
            if scl:
                if self.last_fall is not None:
                    duration = cycle - self.last_fall
                    require(duration >= self.low_cycles, 'I2C LOW phase is shorter than declared')
                    self.low_durations.append(duration)
                if len(self.bits) < self.plan.bit_count:
                    index = len(self.bits)
                    # A late-release timeout may expose one physical rise that
                    # the source never captures. Preserve it as an abort event.
                    abort_tail = self.profile == 'late' and index >= self.deadline_slot
                    if not abort_tail:
                        require(bool(sda) == self.expected[index], 'I2C resolved data/ACK differs at slot ' + str(index))
                    self.bits.append(bool(sda))
                    self.rises.append(cycle)
                else:
                    require(self.stop_rise is None and not sda, 'I2C extra data clock or invalid STOP preparation')
                    self.stop_rise = cycle
                self.last_rise = cycle
            else:
                require(self.stop_rise is None or self.profile in ('timeout', 'late'),
                    'I2C SCL fell after STOP setup began')
                if self.last_rise is not None:
                    duration = cycle - self.last_rise
                    require(self.high_cycles <= duration <= self.high_cycles + 3 or
                        self.profile == 'late' and len(self.bits) > self.deadline_slot,
                        'I2C HIGH phase stalled or violated its sampler-window bound')
                    self.high_durations.append(duration)
                self.last_fall = cycle
                self.falls.append(cycle)
                self._next_sda(cycle)
                self._arm(cycle)
        if self.started_at is not None and self.last_fall is not None and self.previous_master_low and not master_low:
            if len(self.bits) < self.plan.bit_count:
                self.master_low_extensions.append(max(0, cycle - self.last_fall - self.low_cycles - 1))
            if self.profile in ('lastpoll', 'late') and self.hold_active and self.hold_slot == self.deadline_slot:
                require(self.deadline_alignment is None, 'I2C deadline release transition repeated')
                release = cycle + self.wait_budget - 3 + (self.profile == 'late')
                self.hold_until = release
                self.stretches[-1]['release_callback'] = release
                self.deadline_alignment = dict(slot=self.deadline_slot, master_release=cycle,
                    release_callback=release, first_raw_high=release + 1, expected_stage2_ready=release + 3,
                    expected_last_poll=cycle + self.wait_budget,
                    access='resolved SCL/SDA plus public SCL output-enable transition; no private state')
        if self.hold_active and self.hold_until is not None:
            setup_at = self.hold_until - self.tco - 3
            index = self.hold_slot
            if self.plan.direction == 'read' and index < self.plan.bit_count and self._target_owns(index) and cycle >= setup_at:
                self.sda, self.pending_sda = self.expected[index], None
            if cycle >= self.hold_until:
                self.hold_active = False
        if self.pending_sda is not None and cycle >= self.pending_sda[0]:
            self.sda, self.pending_sda = self.pending_sda[1], None
        self.previous_scl, self.previous_sda, self.previous_master_low = scl, sda, master_low
        self.applied_hold = self.hold_active
        return PadDrive(0, (1 if self.hold_active else 0) | (0 if self.sda else 2), links=3)

    def check(self, rx_bits, *, fault=False, require_host_stall=False):
        expected_count = self.timeout_slot if self.profile == 'timeout' else self.deadline_slot if self.profile == 'late' else self.plan.bit_count
        expected_fault = self.profile in ('timeout', 'late')
        require(type(rx_bits) is tuple and fault is expected_fault and len(rx_bits) == expected_count,
            'I2C terminal status or captured-prefix length differs from the independent schedule')
        require(rx_bits == self.expected[:expected_count], 'I2C captured prefix differs from the independent target')
        require(tuple(self.bits[:expected_count]) == self.expected[:expected_count], 'I2C physical data prefix differs')
        if not expected_fault:
            require(len(self.bits) == self.plan.bit_count and self.stopped_at is not None and self.stop_rise is not None,
                'I2C did not complete exactly one stream followed by one guarded STOP rise')
        elif self.profile == 'timeout':
            require(len(self.bits) == expected_count and self.hold_active, 'Timeout fixture did not hold SCL through fault')
        else:
            require(len(self.bits) in (expected_count, expected_count + 1), 'Late timeout has unexplained physical clocks')
        require(self.started_at is not None, 'I2C never generated its START')
        require(not require_host_stall or sum(self.master_low_extensions) > 0, 'Fixture did not observe a host LOW stall')
        if self.profile in ('varying', 'lastpoll', 'late', 'timeout'):
            require(self.target_extension_edges > 0, 'Fixture did not observe target-only SCL stretching')
        if self.profile in ('lastpoll', 'late'):
            require(self.deadline_alignment is not None and self.deadline_alignment['expected_stage2_ready'] ==
                self.deadline_alignment['expected_last_poll'] + (self.profile == 'late'),
                'Deadline fixture lacks the precise declared callback/sampler alignment')
        return dict(protocol='i2c', direction=self.plan.direction, bytes=self.plan.length,
            address=self.plan.address, address_ack=self.address_ack, stream_slots=self.plan.bit_count,
            captured_prefix_bits=expected_count, physical_data_rises=len(self.bits),
            stop_preparation_rises=int(self.stop_rise is not None), start_count=1,
            stop_count=int(self.stopped_at is not None), aborted=expected_fault,
            abort_stop_at=self.abort_stop_at, profile=self.profile,
            target_stretch_edges=self.target_extension_edges, host_low_extra_edges=sum(self.master_low_extensions),
            low_min_edges=min(self.low_durations, default=0), high_phase_edges=sorted(set(self.high_durations)),
            low_cycles=self.low_cycles, high_cycles=self.high_cycles, wait_budget=self.wait_budget,
            peer_tco_cycles=self.tco, callback_delay_cycles=1, sampler_delay_cycles=2,
            stretches=self.stretches, deadline_alignment=self.deadline_alignment,
            stimulus_access='resolved pads; public OE for coverage' +
                (' and deadline alignment' if self.profile in ('lastpoll', 'late') else ' only'),
            payload_accepted=self.address_ack and not expected_fault)
