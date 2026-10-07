"""Independent sampled-wire schedule oracle for serial package acceptance.

This record model reconstructs delivered commands from observed CS/SCK/MOSI.
It never reads frontend or SRAM state. The unchanged typed SRAM exporter then
checks every physical edge and every frozen receipt against those commands.
"""
from dataclasses import dataclass


FIELDS = (
    ('valid', 1), ('busy', 1), ('retained', 1), ('pending', 1), ('rejected', 1),
    ('mode', 2), ('pc', 8), ('remaining', 8), ('levels', 3), ('enabled', 3),
    ('tx_consumed', 6), ('rx_length', 6), ('rx_data', 32), ('read_valid', 1),
    ('read_bit', 1), ('generation', 16), ('transfer', 16), ('exhausted', 1),
    ('stage1', 2), ('stage2', 2), ('virtual_pc', 10), ('env0', 3), ('env1', 3),
    ('phase', 3), ('wait_left', 8), ('scratch', 16),
)
USED = {0: 5, 1: 98, 2: 24, 3: 60, 4: 32, 6: 60, 7: 0, 8: 0}


def field(word, offset, width):
    return (word >> offset) & ((1 << width) - 1)


def classify(word, count):
    """Classify complete wire words by the documented ABI, independently."""
    if count != 160:
        return 1, 0
    sequence = field(word, 128, 16)
    if word >> 148 != 0xA71:
        return 2, sequence
    opcode = field(word, 144, 4)
    payload = word & ((1 << 128) - 1)
    if opcode not in USED or payload >> USED[opcode]:
        return 3, sequence
    return 0, sequence


def command_fields(word, delivering):
    """Reconstruct effective core fields, including quiet indexed reads."""
    opcode = field(word, 144, 4)
    payload = word & ((1 << 128) - 1)
    values = dict(command=opcode if delivering and opcode != 8 else 0,
                  initialize=int(delivering and opcode == 8))
    if delivering:
        if opcode == 1:
            values.update(address=field(payload, 92, 6), word=field(payload, 0, 64),
                          control=field(payload, 64, 24), branch=field(payload, 88, 4))
        elif opcode == 2:
            values.update(count=field(payload, 0, 7), virtual_span=field(payload, 7, 11),
                          idle_levels=field(payload, 18, 3), idle_enabled=field(payload, 21, 3))
        elif opcode == 3:
            values.update(tx_data=field(payload, 0, 32), tx_length=field(payload, 32, 6),
                          rx_capacity=field(payload, 38, 6), expected_generation=field(payload, 44, 16))
        elif opcode == 4:
            values.update(expected_generation=field(payload, 0, 16),
                          expected_transfer=field(payload, 16, 16))
        elif opcode == 6:
            values.update(address=field(payload, 56, 4), branch=field(payload, 0, 56))
    # This combinational indexed-read selector can change while a request is
    # arriving; it cannot issue a command or mutate the retained result.
    values['read_index'] = field(payload, 0, 5) if word >> 144 == 0xA710 and payload >> 5 == 0 else 0
    return {name: value for name, value in values.items() if value or name == 'command'}


@dataclass
class WireSchedule:
    previous_cs: int = 0
    previous_sck: int = 0
    selected: bool = False
    response_read: bool = False
    count: int = 0
    word: int = 0
    dispatch: bool = False
    capture: bool = False
    code: int = 0
    sequence: int = 0
    ready: bool = False
    receipt: int | None = None
    receipts: int = 0
    delivery_edge: int | None = None
    edges: int = 0

    def step(self, pins):
        """Return this edge's core command and post-edge receipt bookkeeping."""
        for name in ('initialize', 'csn', 'sck', 'mosi'):
            if type(pins[name]) is not int or pins[name] not in (0, 1):
                raise ValueError('Wire schedule requires Boolean integer pins')
        index = self.edges
        self.edges += 1
        initialize, cs, clock, bit = (pins[name] for name in ('initialize', 'csn', 'sck', 'mosi'))
        delivering = self.dispatch and self.code == 0 and not initialize
        command = command_fields(self.word, delivering)
        if initialize:
            command = dict(initialize=1, command=0)
        annotation = dict(command=command, expected_ready=0, miso_receipt=None,
                          miso_index=None, captured=None, delivered=bool(delivering))
        if not initialize and self.selected and self.response_read and self.count < 192:
            annotation.update(miso_receipt=self.receipt, miso_index=191-self.count)
        if initialize:
            # Keep the transcript index while resetting only endpoint state.
            fresh = WireSchedule(previous_cs=cs, previous_sck=clock, edges=self.edges,
                                 receipts=self.receipts)
            self.__dict__.update(fresh.__dict__)
            return annotation

        begin = (self.previous_cs == 1 and cs == 0 and clock == 0 and
                 not self.selected and not self.dispatch and not self.capture)
        close = self.selected and cs == 1
        rise = self.selected and cs == 0 and clock == 1 and self.previous_sck == 0
        dispatch_next = close and not self.response_read
        capture_next = self.dispatch
        if delivering:
            self.delivery_edge = index
        elif self.dispatch:
            self.delivery_edge = None
        if self.capture:
            self.receipts += 1
            self.receipt = self.receipts
            self.ready = True
            annotation['captured'] = dict(receipt=self.receipt, capture_edge=index,
                state_edge=index-1, delivery_edge=self.delivery_edge,
                code=self.code, sequence=self.sequence)
        elif close and self.response_read and self.count == 192:
            self.ready = False
        if dispatch_next:
            self.code, self.sequence = classify(self.word, self.count)
        if begin:
            self.selected = True
            self.response_read = self.ready
            self.count = 0
            if not self.ready:
                self.word = 0
        elif close:
            self.selected = False
        if rise:
            self.count = min(193, self.count+1)
            if not self.response_read:
                self.word = ((self.word << 1) | bit) & ((1 << 160)-1)
        self.dispatch, self.capture = bool(dispatch_next), bool(capture_next)
        self.previous_cs, self.previous_sck = cs, clock
        annotation['expected_ready'] = int(self.ready)
        return annotation


def expected_receipt(event, vectors):
    """Build a full response from the independent controller edge oracle."""
    state = dict(vectors[event['state_edge']]['state'])
    rejected = 0 if event['delivery_edge'] is None else vectors[event['delivery_edge']]['state']['rejected']
    state['rejected'] = rejected
    code = 4 if event['code'] == 0 and rejected else event['code']
    payload, offset = 0, 0
    for name, width in FIELDS:
        value = state[name]
        if type(value) is not int or not 0 <= value < 1 << width:
            raise RuntimeError('Independent controller status exceeds width: ' + name)
        payload |= value << offset
        offset += width
    if offset != 155:
        raise RuntimeError('Independent receipt layout does not occupy 155 bits')
    word = ((0x5A10 | code) << 176) | (event['sequence'] << 160) | payload
    return word, state, code


def check_trace(records, annotations, exported):
    """Check all serial bits, ready edges, visible pin drivers and receipts."""
    if len(records) != len(annotations) or len(records) != len(exported):
        raise RuntimeError('Serial trace/oracle lengths differ')
    receipts = {}
    for entry in annotations:
        if entry['captured'] is not None:
            event = entry['captured']
            receipts[event['receipt']] = expected_receipt(event, exported)
    bit_checks = driver_checks = 0
    seen = {receipt:set() for receipt in receipts}
    for index, (record, annotation, vector) in enumerate(zip(records, annotations, exported, strict=True)):
        observed = record['observation']
        if observed['ready'] != annotation['expected_ready']:
            raise RuntimeError(f'Independent serial READY mismatch at edge {index}')
        word = receipts[annotation['miso_receipt']][0] if annotation['miso_receipt'] is not None else 0
        expected_bit = (word >> annotation['miso_index']) & 1 if annotation['miso_index'] is not None else 0
        if observed['miso'] != expected_bit:
            raise RuntimeError(f'Independent serial MISO mismatch at edge {index}')
        if annotation['miso_receipt'] is not None:
            bit_checks += 1
            seen[annotation['miso_receipt']].add(annotation['miso_index'])
        for field_name in ('busy', 'levels', 'enabled'):
            if observed[field_name] != vector['state'][field_name]:
                raise RuntimeError(f'Independent protocol driver mismatch: {field_name} at edge {index}')
            driver_checks += 1
    field_checks = 0
    for bits in seen.values():
        offset = 0
        for _,width in FIELDS:
            field_checks += int(set(range(offset,offset+width)) <= bits)
            offset += width
    return dict(physical_edges=len(records), response_bit_checks=bit_checks,
                ready_checks=len(records), public_driver_checks=driver_checks,
                frozen_receipts=len(receipts), frozen_status_field_checks=field_checks,
                complete_receipt_checks=sum(len(bits)==192 for bits in seen.values()),
                deliveries=sum(entry['delivered'] for entry in annotations))
