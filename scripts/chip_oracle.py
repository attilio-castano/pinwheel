"""External-pin driver and independent reference model for the result interface.

Only compiled program images come from Lean; expected states and host waveforms
are computed here using the existing independent atomic/E64 oracle.
"""
import json
from pathlib import Path
import runpy
from host_demo import SPI, UARTTransmit
from pinwheel_host import Pins

ROOT = Path(__file__).resolve().parents[1]
loader = runpy.run_path(str(ROOT/'scripts/loader-vectors.py'))
pack, fields = loader['pack'], loader['core']['fields']


class Chip:
    def __init__(self, output, ready=False):
        self.m = loader['Atomic']()
        self.output, self.ready = output, ready
        self.ui, self.incoming = 4, 3
        self.first = self.second = (1, 0, 0, 1, 3)
        self.serial = dict(previous=0, count=0, shift=0, command=0, fire=0)
        self.host = dict(r1=0,r2=0,p1=0,p2=0,c1=0,c2=0,consume=0,clear=0,
                         active=0,samples=0,outcome=0,valid=0,overrun=0,rejected=0)
        self.edges, self.frames, self.cases = 0, 0, []
        self.device = None
        for _ in range(8): self.tick(rst=0, check=False)
        for _ in range(4): self.tick()

    @property
    def s(self): return self.m.s

    def inputs(self):
        init,_,_,_,incoming = self.second
        x = self.serial
        command = x['command'] if x['fire'] and x['command'] != 7 else 0
        data = x['shift']
        c = self.m.cursor
        capacity = c<32 or c<64 and data==4 or 64<=c<320 and data<32 or c>=320
        d = fields(data)
        admissible = not self.ready or not (d['kind']==2 and d['finish']==2 and d['duration']==0)
        if command==2 and not (capacity and admissible): command=6
        return dict(init=init,reset=int(x['fire'] and x['command']==7),
                    command=command,data=data,incoming=incoming)

    def gates(self, i):
        m = self.m
        enabled = not (i['init'] or i['reset'] or 1<=m.s[0]<=4)
        c,d,cmd = m.cursor,i['data'],i['command']
        good = loader['valid'](d) if c<64 else d<(64 if c<321 else 256)
        push = enabled and cmd==2 and m.pending and c<322 and good
        commit = enabled and cmd==3 and m.pending and c==322
        start = enabled and cmd==5 and m.committed
        accepted = enabled and (cmd in (0,1,4) or push or commit or start)
        rejected = not(i['init'] or i['reset']) and cmd!=0 and not accepted
        return bool(start), bool(rejected)

    def shown(self, rejected):
        m,h = self.m,self.host
        page=h['p2']
        if page==1: value=h['samples']&255
        elif page==2: value=h['samples']>>8
        elif page==3: value=(h['outcome']<<5)|16|(h['rejected']<<2)|(h['overrun']<<1)|h['valid']
        else: value=(m.s[0]<<5)|(int(rejected)<<4)|(m.active<<3)|(m.pending<<2)|(m.committed<<1)|int(1<=m.s[0]<=4)
        return [value,m.s[4],m.s[5]]

    def tick(self, incoming=None, rst=1, check=True):
        if incoming is not None: self.incoming=incoming
        if self.device is not None:
            self.incoming = self.device(self.edges, Pins(*self.shown(self.gates(self.inputs())[1])), self.ui)
        i=self.inputs()
        started,rejected=self.gates(i)
        before=self.shown(rejected)
        h=self.host
        reset=not(rst and h['r1'] and h['r2'])
        consume=bool(h['c2']&1 and not h['consume'])
        clear=bool(h['c2']&2 and not h['clear'])
        busy=1<=self.m.s[0]<=4
        arrival=bool(h['active'] and not busy and self.m.s[0] in (5,6,7))
        occupied=h['valid'] and not consume
        new=dict(r1=rst,r2=h['r1'],p1=(self.ui>>3)&3,p2=h['p1'],
                 c1=(self.ui>>5)&3,c2=h['c1'],consume=int(not reset and h['c2']&1!=0),
                 clear=int(not reset and h['c2']&2!=0),active=int(not reset and (busy or started)),
                 samples=0 if reset else self.m.s[6] if arrival and not occupied else h['samples'],
                 outcome=0 if reset else self.m.s[0] if arrival and not occupied else h['outcome'],
                 valid=int(not reset and (occupied or arrival)),
                 overrun=int(not reset and ((h['overrun'] and not clear) or (arrival and occupied))),
                 rejected=int(not reset and ((h['rejected'] and not clear) or rejected)))
        self.m.edge(**i)
        # The independent core oracle records rows for its own runner. Discard
        # them here: chip evidence is streamed to the external-pin vector file.
        self.m.rows.clear()
        init,sck,mosi,csn,_=self.second
        x=self.serial
        taking=not(init or csn) and sck and not x['previous']
        self.serial=dict(previous=sck,count=0 if init or csn else (0 if x['count']==71 else x['count']+1) if taking else x['count'],
                         shift=((x['shift']<<1)|mosi)&((1<<64)-1) if taking else x['shift'],
                         command=x['shift']%4*2+mosi if taking and x['count']==7 else x['command'],
                         fire=int(taking and x['count']==71))
        self.second,self.first=self.first,(int(not rst),self.ui&1,(self.ui>>1)&1,(self.ui>>2)&1,self.incoming)
        self.host=new
        after=self.shown(self.gates(self.inputs())[1])
        self.output.write(' '.join(map(str,[rst,self.ui,self.incoming,int(check),*before,*after]))+'\n')
        self.edges+=1

    def frame(self, command, data=0, uneven=False):
        bits=f'{command:08b}{data:064b}'
        for k,bit in enumerate(bits):
            self.ui=(self.ui&~7)|(int(bit)<<1)
            for _ in range(1+(k%2 if uneven else 0)): self.tick()
            self.ui|=1
            for _ in range(2+(k%3 if uneven else 0)): self.tick()
        self.ui=(self.ui&~7)|4
        self.tick(); self.tick()
        self.frames+=1

    def edge(self, incoming=3, start=0, **ignored):
        self.incoming=incoming
        if start and not 1<=self.s[0]<=4: self.frame(5)
        else: self.tick()

    def page(self, p):
        self.ui=(self.ui&~24)|(p<<3)
        for _ in range(3): self.tick()

    def pulse(self, bit):
        self.ui|=1<<bit
        for _ in range(4): self.tick()
        self.ui&=~(1<<bit)
        for _ in range(4): self.tick()

    def load(self, name, words, last, idle=(0,0)):
        self.cases.append(dict(name=name,edge=self.edges))
        self.frame(7); self.frame(1)
        data=loader['stream'](words,last,idle)
        assert all(w==4 for w in data[32:64]) and all(w<32 for w in data[64:320])
        for word in data: self.frame(2,word)
        assert self.m.cursor==322
        self.frame(3)
        assert self.m.committed and not self.m.pending


def generate(out, ready=False):
    images={}
    for line in (ROOT/'build/loader/images.txt').read_text().splitlines():
        name,*xs=line.split(); last,l,e,*words=map(int,xs)
        images[name]=(words,last,(l,e))
    with (out/'vectors.txt').open('w') as f:
        c=Chip(f,ready)
        # Partial frame, then abort via select; no delivered command.
        c.cases.append(dict(name='partial-frame-and-invalid-commands',edge=c.edges))
        for bit in [1,0,1,1,0,1,0]:
            c.ui=bit<<1; c.tick(); c.ui|=1; c.tick(); c.tick()
        c.ui=4
        for _ in range(5): c.tick()
        assert not c.m.pending
        c.frame(6,uneven=True); c.tick()
        assert c.host['rejected']
        c.page(3); c.pulse(6); assert not c.host['rejected']
        c.frame(1); c.frame(2,1<<63); assert c.m.cursor==0
        if ready:
            c.pulse(6); assert not c.host['rejected']
            c.frame(2,pack(dict(kind=2,finish=2,yes=1,no=2)))
            assert c.m.cursor==0 and c.host['rejected']
        # Capacity failures do not advance staging; retrying with valid data does.
        for _ in range(32): c.frame(2,4)
        c.pulse(6); assert not c.host['rejected']
        c.frame(2,pack(dict(kind=0))); assert c.m.cursor==32
        c.frame(4)
        # Reset during a partial upload; control returns to an empty invalid chip.
        c.frame(1); c.frame(2,4)
        for _ in range(6): c.tick(rst=0)
        for _ in range(4): c.tick()
        assert not(c.m.committed or c.m.pending or c.host['valid'])
        # Capture every slot, verifying both bytes and their bit order.
        words=[pack(dict(kind=0,duration=3,entry=1+4*k)) for k in range(16)]+[4]
        c.load('all-sixteen-captures',words,16)
        c.edge(start=1,incoming=1)
        pattern=0xa653
        while 1<=c.s[0]<=4:
            c.tick(incoming=(pattern>>min(c.s[1]+1,15))&1)
        c.tick()
        assert c.host['samples']==pattern and c.host['valid']
        for p in [1,2,3,1,0,2]: c.page(p)
        assert c.host['samples']==pattern
        # New execution overflows without changing the unread result.
        c.edge(start=1,incoming=0)
        while 1<=c.s[0]<=4: c.tick(incoming=0)
        c.tick(); assert c.host['overrun'] and c.host['samples']==pattern
        c.pulse(5); assert not c.host['valid']
        c.pulse(5); assert not c.host['valid']
        c.pulse(6); assert not c.host['overrun']
        # Busy commands cannot alter either program. Serial delivery fits inside
        # this instruction, including the pin sampler and receiver tail.
        c.load('busy-rejection',[pack(dict(kind=0,duration=255)),4],1)
        c.edge(start=1); c.frame(1); c.tick()
        assert c.host['rejected'] and not c.m.pending
        while 1<=c.s[0]<=4: c.tick()
        c.tick(); c.pulse(5); c.pulse(6)
        # Peers inspect only protocol pins. Exercise both transmit examples at
        # the complete-chip boundary, behind the real input/serial samplers.
        for name, image, device, samples in [('compiled-uart-tx', 'uart', UARTTransmit(), 0),
                                              ('compiled-spi', 'spi', SPI(), 0x69)]:
            c.load(name, *images[image])
            c.page(0)
            c.device = device
            c.frame(5)
            while 1 <= c.s[0] <= 4:
                c.tick()
            c.tick()
            device.check()
            c.device = None
            assert c.host['valid'] and c.host['samples'] == samples and c.host['outcome'] == 5
            for page in [1, 2, 3]: c.page(page)
            c.pulse(5)
        # Compiled I2C register read, with a live independently modeled target.
        c.load('compiled-i2c-read',*images['i2c-read'])
        loader['core']['i2c'](c,True,byte=0x96,stretched=True)
        c.tick(); assert c.host['samples']==0x69 and c.host['outcome']==5
        c.page(1); c.page(2); c.page(3)
        retained=c.host['samples']
        # A program replacement preserves an unconsumed result. A halt-only
        # start still generates completion even without a busy interval.
        c.load('halt-only-replacement',[4],0)
        assert c.host['valid'] and c.host['samples']==retained
        c.pulse(5); c.frame(5); c.tick()
        assert c.host['valid'] and c.host['samples']==0 and c.host['outcome']==5
        c.pulse(5)
        if not ready:
            c.load('compiled-uart-rx',*images['uart-rx'])
            for byte,stop in [(0xa6,1),(0x53,0)]:
                c.edge(start=1,incoming=1)
                for t in range(1,180):
                    symbol=(t-5)//16
                    wire=1 if t<5 else 0 if symbol==0 else (byte>>(symbol-1))&1 if 1<=symbol<=8 else stop if symbol==9 else 1
                    c.tick(incoming=wire)
                assert c.host['valid'] and c.host['samples']&255==byte
                assert (c.host['samples']>>9)&1==stop and c.host['outcome']==5
                c.page(1); c.page(2); c.page(3); c.pulse(5)
        # Unknown storage is never asserted known at startup; global reset must
        # clear even a retained result and sticky errors without touching SRAM.
        for _ in range(6): c.tick(rst=0)
        for _ in range(4): c.tick()
        c.page(3)
        assert not(c.host['valid'] or c.host['overrun'] or c.host['rejected'])
    result=dict(edges=c.edges,frames=c.frames,ready=ready,cases=c.cases)
    (out/'coverage.json').write_text(json.dumps(result,indent=2)+'\n')
    return result
