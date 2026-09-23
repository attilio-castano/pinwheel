"""Independent packed-model/E64/peer vectors for the actual paired circuit.

The existing serial/pin/mailbox oracle is reused at package pins. Expected
execution values come from Python and E64, never from Lean or emitted RTL.
"""
import json
from pathlib import Path
import random
import runpy

import chip_oracle
from paired_execution import Machine, compile_e64, uart_image, spi_image, valid_token

ROOT=Path(__file__).resolve().parents[1]
LEGACY=runpy.run_path(str(ROOT/'scripts/reactive-core-vectors.py'))
pack=LEGACY['pack']


def images():
    result={}
    for line in (ROOT/'build/loader/images.txt').read_text().splitlines():
        name,*numbers=line.split()
        last,levels,enables,*words=map(int,numbers)
        result[name]=(words,last,(levels,enables))
    return result


def gates(m,i):
    """Combinational admission for the package oracle's before-edge observation."""
    enabled=not(i['init'] or i['reset'] or i['command']==7 or 1<=m.s[0]<=4)
    c,d,command=m.cursor,i['data'],i['command']
    good=False
    if enabled and command==2 and m.pending:
        if c<32: good=d<1<<20
        elif c<288: good=all(valid_token(d>>(32*k)&0xffffffff,m.parameters[1-m.active]) for k in range(2))
        elif c==288: good=d<1<<32 and valid_token(d,m.parameters[1-m.active])
        elif c==289: good=d<64
    push=enabled and command==2 and m.pending and c<290 and good
    commit=enabled and command==3 and m.pending and c==290
    start=enabled and command==5 and m.committed
    accepted=enabled and (command in (0,1,4) or push or commit or start)
    rejected=not(i['init'] or i['reset'] or command==7) and command!=0 and not accepted
    return tuple(map(bool,(push,commit,start,rejected)))


class Logged(Machine):
    def __init__(self, stream):
        super().__init__()
        self.stream,self.edges,self.reference=stream,0,None
        self.e64_edges=0
        self.edge(init=1)

    def edge(self, command=0,data=0,incoming=0,reset=False,init=False,**kw):
        before=self.busy
        i=dict(command=command,data=data,incoming=incoming,reset=reset,init=init)
        expected_gates=gates(self,i)
        super().edge(**i,**kw)
        assert self.gates==expected_gates
        if self.reference is not None:
            if init:
                self.reference=None
            elif reset or command==7:
                self.reference.edge(reset=1,incoming=incoming)
            elif before:
                self.reference.edge(incoming=incoming)
            elif self.gates[2]:
                self.reference.edge(start=1,incoming=incoming)
            if self.reference is not None:
                assert self.s==self.reference.s,('independent E64 mismatch',self.edges,self.s,self.reference.s)
                self.e64_edges+=1
                self.reference.rows.clear()
        values=[init,reset,command,data,incoming,*self.gates,
                self.active,self.committed,self.pending,self.cursor,*self.s]
        self.stream.write(' '.join(str(int(x)) for x in values)+'\n')
        self.edges+=1

    def load_e64(self,words,last=None,idle=(0,0)):
        self.reference=None
        self.edge(reset=1)
        self.load(compile_e64(words,idle,last))
        self.reference=LEGACY['Machine'](False)
        self.reference.load('paired-rtl',words,len(words)-1 if last is None else last,idle)
        assert self.s==self.reference.s


class Peer:
    def __init__(self,m): self.m,self.count=m,0
    @property
    def s(self): return self.m.s
    def edge(self,incoming=0,start=0,write=0,**ignored):
        command=self.count%6+1 if write else 5 if start else 0
        self.count+=1
        self.m.edge(command=command,data=(1<<64)-1,incoming=incoming)
        if write: assert self.m.gates==(False,False,False,True)
    def load(self,name,words,last,idle): self.m.load_e64(words,last,idle)


def core_vectors(out):
    rng=random.Random(5126420)
    programs=images()
    with (out/'core-vectors.txt').open('x') as stream:
        m=Logged(stream)
        # All six-bit histories across consecutive branches, with independent
        # entry and terminal slots and all three row addresses in circulation.
        words=[pack(dict(kind=2,finish=2,entry=15,terminal=49,sample=12,
                         yes=(k+1)%3,no=(k+2)%3)) for k in range(3)]
        m.load_e64(words)
        for history in range(4096):
            m.edge(reset=1);m.edge(command=5,incoming=history&3)
            for k in range(6): m.edge(incoming=history>>(2*k)&3,command=k%6+1,data=0xff)
        m.edge(reset=1)
        # Every parameter slot, both atomic banks, and every executable row.
        dictionary=[pack(dict(entry=1+2*(k//16)+4*(k%16))) for k in range(32)]
        for offset in [0,7]:
            words=[dictionary[(k*17+offset)%32] for k in range(256)]
            m.load_e64(words);m.edge(command=5)
            for k in range(256):m.edge(incoming=k%4)
            assert m.mode==7
        # Full duration, renewed qualifying budgets, guards, waits and captures.
        for kind in [1,2,3]:
            for check in range(4 if kind==1 else 16):
                for budget in ([0,1,255] if kind==3 else [0]):
                    fields=dict(kind=kind,duration=2 if kind==3 else 0,check=check)
                    if kind==3:fields['budget']=budget
                    if kind==2:fields.update(entry=3,terminal=61,finish=2,sample=15,yes=0,no=1)
                    m.load_e64([pack(fields),4]);m.edge(command=5,incoming=check%4)
                    for k in range(24):m.edge(incoming=rng.randrange(4),command=k%6+1,data=255)
                    m.edge(reset=1)
        m.load_e64([pack(dict(duration=255,levels=1,enabled=1))]*255+[4])
        m.edge(command=5)
        for _ in range(255*256):m.edge()
        assert m.mode==5
        # Resident payloads: all bytes on unchanged UART and SPI images.
        m.reference=None;m.edge(reset=1);m.load(uart_image())
        for byte in range(256):
            m.edge(command=5,data=byte)
            for t in range(40):
                expected=0 if t<4 else byte>>((t//4)-1)&1 if t<36 else 1
                assert m.levels&1==expected and m.enabled==7
                m.edge(command=5,data=byte^255,incoming=t%4)
            assert m.mode==5
        m.edge(reset=1);m.load(spi_image())
        for byte in range(256):
            received=byte^0xa5
            m.edge(command=5,data=byte)
            for t in range(68):
                phase=t//4
                assert (m.levels>>1)&1==phase%2
                if phase<16:assert m.levels&1==byte>>(7-phase//2)&1
                m.edge(incoming=received>>min(7,(t+1)//8)&1,command=5,data=0)
            assert m.mode==5 and m.samples&255==received
        # Partial replacement at each ownership boundary; retained active code.
        m.edge(reset=1);m.load(uart_image())
        replacement=spi_image().upload()
        for cut in [0,1,31,32,33,287,288,289,290]:
            for ending in [4,7,1]:
                m.edge(command=1)
                for value in replacement[:cut]:m.edge(command=2,data=value)
                if cut<290:m.edge(command=3);assert m.gates[3]
                m.edge(command=ending)
                m.edge(command=5,data=0x53)
                for _ in range(40):m.edge()
                assert m.mode==5
        # Malformed parameters, either row half, boot width and idle width.
        m.edge(command=1);m.edge(command=2,data=1<<20);assert m.cursor==0
        for x in uart_image().upload():
            if m.cursor in [32,128,287]:
                for bad in [1<<30,1<<62]:m.edge(command=2,data=bad);assert m.gates[3]
            if m.cursor in [288,289]:m.edge(command=2,data=1<<63);assert m.gates[3]
            m.edge(command=2,data=x)
        m.edge(command=3)
        # Real compiled I2C and RX peers, including NACK/stretch and rearm.
        peer=Peer(m)
        peer.load('i2c-write',*programs['i2c-write'])
        durations=[LEGACY['i2c'](peer,False,stretched=True)]
        peer.load('i2c-read',*programs['i2c-read'])
        for byte in [0,1,0x55,0x80,0x96,0xaa,0xfe,0xff]:
            for stretch in [False,True]:durations.append(LEGACY['i2c'](peer,True,byte,stretched=stretch))
        for bits in range(7):durations.append(LEGACY['i2c'](peer,True,acks=tuple(bits>>k&1 for k in range(3)),stretched=True))
        rx=LEGACY['uart_rx']['exercise'](peer,programs)
        m.edge(init=1)
        result=dict(edges=m.edges,e64_compared_edges=m.e64_edges,branch_histories=4096,
                    consecutive_branch_edges=4096*6,resident_uart_bytes=256,resident_spi_pairs=256,
                    atomic_interruptions=27,i2c_cases=len(durations),i2c_edges=sum(durations),uart_rx_frames=rx)
    (out/'core-coverage.json').write_text(json.dumps(result,indent=2)+'\n')
    return result


class Chip(chip_oracle.Chip):
    def __init__(self,output):
        super().__init__(output)
        self.m=Machine();self.m.edge(init=1);self.m.rows=[]
    def inputs(self):
        init,_,_,_,incoming=self.second
        s=self.serial
        return dict(init=init,reset=int(s['fire'] and s['command']==7),
                    command=s['command'] if s['fire'] and s['command']!=7 else 0,
                    data=s['shift'],incoming=incoming)
    def gates(self,i):
        g=gates(self.m,i)
        return g[2],g[3]
    def load(self,name,words,last,idle=(0,0)):
        self.load_image(name,compile_e64(words,idle,last))
    def load_image(self,name,image):
        self.cases.append(dict(name=name,edge=self.edges))
        self.frame(7);self.frame(1)
        for word in image.upload():self.frame(2,word)
        assert self.m.cursor==290
        self.frame(3)
        assert self.m.committed and not self.m.pending


def chip_vectors(out):
    programs=images()
    with (out/'vectors.txt').open('x') as stream:
        c=Chip(stream)
        # Truncated serial input must not deliver a command.
        for bit in [1,0,1,1,0,1,0]:
            c.ui=bit<<1;c.tick();c.ui|=1;c.tick();c.tick()
        c.ui=4
        for _ in range(5):c.tick()
        assert not c.m.pending
        c.frame(6,uneven=True);c.tick();assert c.host['rejected']
        c.page(3);c.pulse(6);assert not c.host['rejected']
        c.frame(1);c.frame(2,1<<63);assert c.m.cursor==0
        c.load_image('resident-uart',uart_image())
        for byte in [0,1,0x53,0x80,0xa6,255]:
            c.frame(5,byte)
            for _ in range(48):c.tick()
            assert c.m.mode==5
        c.page(3);assert c.host['valid'] and c.host['overrun']
        c.pulse(5);assert not c.host['valid'];c.pulse(6);assert not c.host['overrun']
        c.load_image('resident-spi',spi_image())
        c.frame(5,0xa6)
        for _ in range(80):c.tick(incoming=1)
        assert c.m.samples&255==255
        c.page(1);assert c.shown(False)[0]==255
        c.load('captures',[pack(dict(entry=1+4*k,duration=3)) for k in range(16)]+[4],16)
        c.frame(5)
        for _ in range(80):c.tick(incoming=1)
        c.page(1);c.page(2);c.page(3)
        c.pulse(5);c.pulse(6)
        # Package pin checks reuse the sampled-input program with actual
        # serial command timing. A long-running branch loop exercises busy
        # upload rejection and a real command-7 reset.
        branch=[pack(dict(kind=2,finish=2,entry=15,terminal=49,sample=12,yes=0,no=1)),4]
        c.load('serial-branch',branch,1)
        c.incoming=1;c.frame(5)
        c.frame(5,255);c.frame(1);assert c.m.mode==3 and not c.m.pending
        c.incoming=0
        for _ in range(8):c.tick()
        assert c.m.mode==5
        c.frame(7);assert c.m.mode==0
        # UART receive uses the same independent peer; its waveform contract
        # is checked at the sampled core boundary by core_vectors above.
        c.load('uart-rx',*programs['uart-rx'])
        c.incoming=1;c.frame(5)
        for _ in range(20):c.tick()
        c.frame(7);assert c.m.mode==0
        c.frame(1)
        for word in spi_image().upload()[:33]:c.frame(2,word)
        c.frame(4);assert not c.m.pending
        for _ in range(8):c.tick(rst=0)
        for _ in range(6):c.tick()
        assert not(c.m.committed or c.host['valid'])
        result=dict(edges=c.edges,frames=c.frames,cases=c.cases,
                    boundary='actual serial pins and existing sampler/receiver/mailbox; Python paired execution oracle')
    (out/'chip-coverage.json').write_text(json.dumps(result,indent=2)+'\n')
    return result
