"""Independent integer/bit-period oracle for the composed digital MMIO UART.

No Lean, Expr, generated RTL, or production model is evaluated here. RX is an
already synchronous sampled bit. Analog/CDC/clock-tolerance claims are absent.
"""
from collections import Counter

INPUT_ROLES = ('reset','request_valid','device','write','word','data','gpio_input','rx')
INPUT_WIDTHS = (1,1,2,1,6,32,32,1)
OUTPUT_ROLES = ('request_ready','response_valid','response_code','response_data','gpio_output',
                'held_tx_active','held_tx_data','tx','tx_ready','tx_complete','rx_valid','rx_data','framing_error')
OUTPUT_WIDTHS = (1,1,3,32,32,1,8,1,1,1,1,8,1)
REGISTER_ROLES = ('gpio','timer','held_tx_active','held_tx_data','held_rx_valid','held_rx_data','overrun','framing',
                  'tx_active','tx_count','tx_byte','rx_phase','rx_count','rx_byte')
MASK = (1 << 32)-1


def widths(divisor):
    if type(divisor) is not int or divisor < 4 or divisor % 2:
        raise ValueError('Divisor must be even and at least four')
    w = (10*divisor).bit_length()
    return (32,32,1,8,1,8,1,1,1,w,8,2,w,8)


def row(**kw):
    result = dict(reset=False, request_valid=False, device=0, write=False, word=0, data=0, gpio_input=0, rx=True)
    result.update(kw)
    validate_row(result)
    return result


def validate_row(i):
    if type(i) is not dict or set(i) != set(INPUT_ROLES):
        raise ValueError('Incomplete or extra input pins')
    for name, width in zip(INPUT_ROLES, INPUT_WIDTHS, strict=True):
        expected_type = bool if width == 1 else int
        if type(i[name]) is not expected_type or not 0 <= int(i[name]) < 1 << width:
            raise ValueError('Invalid input type or width: '+name)


def restore(divisor, s):
    ws = widths(divisor)
    if type(s) is not list or len(s) != len(ws) or any(type(v) is not int or not 0 <= v < 1 << w for v,w in zip(s,ws,strict=True)):
        raise ValueError('Invalid raw register image')
    return s.copy()


def frontend(d, i, s):
    if i['reset']:
        return [1,0,0,0,0,0]
    active, elapsed, byte = s[8:11]
    symbols = [0]+[(byte >> k)&1 for k in range(8)]+[1]
    line = symbols[elapsed//d] if active and elapsed < 10*d else 1
    complete = active and elapsed == 10*d-1
    stop = s[11] == 1 and s[12] == d//2+9*d-1
    arrived, error = stop and i['rx'], stop and not i['rx']
    return [line,1-active,int(complete),int(arrived),s[13] if arrived else 0,int(error)]


def access(i,s):
    dev, reg, write = i['device'],i['word'],i['write']
    if dev == 0 and reg == 0:
        return (3,0) if write else (0,i['gpio_input'])
    if dev == 0 and reg == 1:
        return (1,0) if write else (0,s[0])
    if dev == 1 and reg == 0:
        return (3,0) if write else (0,s[1])
    if dev != 2 or reg > 3:
        return 2,0
    if reg == 0:
        return (3,0) if write else (0,(1-s[2])+2*s[4]+4*s[6]+8*s[7])
    if reg == 1:
        return (4 if s[2] else 1,0) if write else (3,0)
    if reg == 2:
        return (3,0) if write else ((0,s[5]) if s[4] else (5,0))
    return (1,0) if write else (3,0)


def output(d,i,s):
    front = frontend(d,i,s)
    if i['reset']:
        return [0]*7+front
    code,data = access(i,s) if i['request_valid'] else (0,0)
    return [1,int(i['request_valid']),code,data,s[0],s[2],s[3] if s[2] else 0]+front


def step(d,i,s):
    validate_row(i); restore(d,s)
    if i['reset']:
        return [0]*14
    nxt = s.copy()
    front = frontend(d,i,s)
    code,_ = access(i,s)
    operation = i['request_valid']
    start = operation and i['device'] == 2 and i['word'] == 1 and code == 1
    consume = operation and i['device'] == 2 and i['word'] == 2 and code == 0
    clear = operation and i['device'] == 2 and i['word'] == 3 and code == 1
    if operation and i['device'] == 0 and i['word'] == 1 and code == 1:
        nxt[0] = i['data']
    nxt[1] = (s[1]+1)&MASK
    if start:
        nxt[2:4] = [1,i['data']&255]
    elif front[2]:
        nxt[2] = 0
    if consume:
        nxt[4] = 0
    if clear:
        nxt[6] &= 1-((i['data']>>2)&1)
        nxt[7] &= 1-((i['data']>>3)&1)
    if front[3]:
        if nxt[4]:
            nxt[6] = 1
        else:
            nxt[4:6] = [1,front[4]]
    if front[5]:
        nxt[7] = 1
    # CPU-only offer: autonomous completion cannot feed the admission mux.
    offered = start or bool(s[2])
    offered_byte = i['data']&255 if start else s[3]
    if not s[8]:
        if offered:
            nxt[8:11] = [1,0,offered_byte]
    elif s[9] < 10*d-1:
        nxt[9] = s[9]+1
    else:
        nxt[8] = 0
    # Malformed counters/phases recover quietly, preserving inactive metadata.
    phase, elapsed = s[11],s[12]
    if phase == 0:
        if not i['rx']:
            nxt[11:14] = [1,0,0]
    elif phase == 1:
        next_sample = elapsed+1
        if elapsed >= d//2+9*d or (next_sample == d//2 and i['rx']):
            nxt[11] = 0
        elif next_sample == d//2+9*d:
            nxt[11] = 0 if i['rx'] else 2
        else:
            nxt[12] = next_sample
            for k in range(8):
                if next_sample == d//2+(k+1)*d:
                    nxt[13] = (s[13]&~(1<<k)) | (int(i['rx'])<<k)
    elif phase == 2:
        if i['rx']:
            nxt[11] = 0
    else:
        nxt[11] = 0
    return nxt


def oracle(d, startup, rows, *, owned=False):
    s = restore(d,startup)
    frames,events,counts = [],[],Counter()
    tx_pending = None
    rx_pending = None
    next_tx = next_rx = 0
    for cycle,i in enumerate(rows):
        validate_row(i)
        pre,after = output(d,i,s),step(d,i,s)
        old_tx_pending = tx_pending
        front = pre[7:]
        e = {'cycle':cycle,'response':pre[2:4] if pre[1] else None,'sampled_gpio':i['gpio_input'],
             'reset':i['reset'],'tx_start':False,'tx_complete':bool(front[2]),'rx_arrival':front[4] if front[3] else None,
             'rx_consumed':None,'rx_dropped':None,'framing_error':bool(front[5])}
        if i['reset']:
            counts['resets'] += 1
            if tx_pending is not None: counts['tx_cancelled'] += 1
            if rx_pending is not None: counts['rx_cancelled'] += 1
            tx_pending = rx_pending = None
        else:
            counts['ticks'] += 1
            if pre[1]:
                counts['responses'] += 1
                counts['reads' if pre[2] == 0 else 'stores' if pre[2] == 1 else 'faults'] += 1
                if i['device'] == 3: counts['invalid_selectors'] += 1
            start = bool(pre[1] and i['device']==2 and i['word']==1 and pre[2]==1)
            consume = bool(pre[1] and i['device']==2 and i['word']==2 and pre[2]==0)
            if front[2]:
                counts['tx_completions'] += 1
                if owned:
                    if tx_pending is None or tx_pending['byte'] != s[10] or cycle-tx_pending['edge'] != 10*d:
                        raise AssertionError('Completion lacks its unique, exact-duration accepted write')
                    e['completed_occurrence'] = tx_pending
                    tx_pending = None
            if start:
                counts['tx_starts'] += 1; e['tx_start'] = True
                if owned and tx_pending is not None: raise AssertionError('Overlapping accepted TX writes')
                tx_pending = {'id':next_tx,'byte':i['data']&255,'edge':cycle}; next_tx += 1
                e['started_occurrence'] = tx_pending
            if owned and s[8]:
                if old_tx_pending is None: raise AssertionError('Unowned transmitted period')
                age = cycle-old_tx_pending['edge']-1
                symbols = [0]+[(old_tx_pending['byte']>>k)&1 for k in range(8)]+[1]
                if not 0 <= age < 10*d or pre[7] != symbols[age//d]: raise AssertionError('Wrong TX bit period')
            if consume:
                counts['rx_consumed'] += 1; e['rx_consumed'] = s[5]
                if owned and (rx_pending is None or rx_pending['byte'] != s[5]): raise AssertionError('RX consumed wrong occurrence')
                e['consumed_occurrence'] = rx_pending; rx_pending = None
            if front[3]:
                counts['rx_arrivals'] += 1
                if consume: counts['rx_refills'] += 1
                occurrence = {'id':next_rx,'byte':front[4],'edge':cycle}; next_rx += 1
                if s[4] and not consume:
                    counts['rx_dropped'] += 1; e['rx_dropped'] = occurrence
                else:
                    counts['rx_captured'] += 1; rx_pending = occurrence
                    e['captured_occurrence'] = occurrence
            if front[5]: counts['framing_errors'] += 1
        frames.append(dict(cycle=cycle,input=i,pre=pre,post=output(d,i,after),registers=after))
        events.append(e); s=after
    if owned:
        if counts['tx_starts'] != counts['tx_completions']+counts['tx_cancelled']+int(tx_pending is not None):
            raise AssertionError('TX occurrence balance')
        if counts['rx_arrivals'] != counts['rx_dropped']+counts['rx_consumed']+counts['rx_cancelled']+int(rx_pending is not None):
            raise AssertionError('RX occurrence balance')
    return frames,events,dict(counts,edges=len(rows),owned_initial=owned,tx_pending=int(tx_pending is not None),rx_pending=int(rx_pending is not None))


def wire_frame(d, byte, stop=True):
    return [False]*d+[bool((byte>>k)&1) for k in range(8) for _ in range(d)]+[stop]*d


def stimulus(d):
    widths(d)
    rows = [row(reset=True,request_valid=True,device=2,write=True,word=1,data=255,rx=False),row()]
    # Full register decode and both directions, including all device3 addresses.
    for dev in range(4):
        for reg in range(64):
            for write in (False,True):
                rows.append(row(request_valid=True,device=dev,word=reg,write=write,data=0x89abcdef,gpio_input=0xfedcba98))
    rows += [row(reset=True),row()]
    values = range(256) if d == 4 else (0,1,2,3,0x55,0x80,0xa5,0xff)
    # UART writes bypass on admission; held writes fault through completion and
    # may start another frame only on the following idle edge.
    for byte in values:
        rows.append(row(request_valid=True,device=2,word=1,write=True,data=0xabc00000|byte))
        rows += [row(request_valid=True,device=2,word=1,write=True,data=byte^255) for _ in range(10*d)]
        rows += [row(),row()]
    # Incoming bitstreams: preserve full RX, consume/refill at the stop sample,
    # distinguish empty+arrival from an immediately readable byte.
    for k,byte in enumerate((0x35,0xa6,0xff,0,0x81,0x7e)):
        bits = wire_frame(d,byte)
        for offset,bit in enumerate(bits):
            kw = dict(rx=bit)
            if offset == d//2+9*d:
                kw.update(request_valid=True,device=2,word=2,write=False)
            rows.append(row(**kw))
        if k % 2: rows.append(row(request_valid=True,device=2,word=2))
    # Full-slot overflow, W1C with new overrun, new framing over clear, ignored glitch.
    for n,byte in enumerate((0x22,0x99)):
        for offset,bit in enumerate(wire_frame(d,byte)):
            rows.append(row(rx=bit,request_valid=(n==1 and offset==d//2+9*d),device=2,word=3,write=True,data=12))
    for offset,bit in enumerate(wire_frame(d,0x5a,False)):
        rows.append(row(rx=bit,request_valid=(offset==d//2+9*d),device=2,word=3,write=True,data=12))
    rows += [row(rx=False)]*(2*d)+[row(),row(rx=False)]+[row()]*d
    # Abort TX/RX at admission, symbol boundaries and the completion edge.
    for cut in (0,1,d-1,d,9*d,10*d-1):
        rows += [row(reset=True),row(request_valid=True,device=2,word=1,write=True,data=0xa5,rx=False)]
        rows += [row(rx=False)]*cut
        rows += [row(reset=True,request_valid=True,device=2,word=1,write=True,data=0x5a,rx=False),row()]
    rows.append(row(reset=True))
    startup = [0xfedcba98,0xffffffff,1,0xa5,1,0x39,1,1,1,10*d-1,0xa5,1,d//2+9*d-1,0x39]
    return startup,rows


def raw_segments(d):
    w = widths(d)[9]; frame,stop = 10*d,d//2+9*d
    counts = (0,d//2-1,d//2+d-1,stop-1,frame-1,frame,(1<<w)-1,7)
    segments=[]
    for dev in range(4):
        for reg in range(64):
            for wr in (False,True):
                k = (dev*128+reg*2+int(wr))
                bank = [0x80000000+k,0xffffffff,k%2,(k*73)&255,(k//2)%2,(k*29)&255,(k//4)%2,(k//8)%2,
                        (k//16)%2,counts[k%8],(k*37)&255,(k//32)%4,counts[(k+3)%8],(k*97)&255]
                segments.append(dict(name=f'raw-{k}',startup=bank,rows=[row(request_valid=True,device=dev,word=reg,write=wr,
                                  data=0xdeadbeef,gpio_input=0x12345678,rx=bool(k%2)),row(reset=True,rx=False)]))
    # Explicit coherent and malformed simultaneous completion/reset fixtures.
    for reset in (False,True):
        for valid in (False,True):
            for rx in (False,True):
                bank=[0xa5,0xffffffff,1,0x96,1,0x3c,1,1,1,frame-1,0x96,1,stop-1,0xc3]
                segments.append(dict(name=f'race-{int(reset)}-{int(valid)}-{int(rx)}',startup=bank,
                    rows=[row(reset=reset,request_valid=valid,device=2,word=2,rx=rx),row(),row(reset=True)]))
    return segments
