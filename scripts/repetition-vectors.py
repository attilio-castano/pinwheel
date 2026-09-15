#!/usr/bin/env python3
"""Independent bounded repetition decoder, atomic host model, literal-program peer and bus monitor."""
import collections
import json
import runpy
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'build/storage/repetition'
ns=runpy.run_path(str(ROOT/'scripts/loader-vectors.py'))


def fetch(image, pc):
    start,span,bits,stop=image[17:21]
    delta=(pc-start)&255; second=delta>=span
    within=(delta-span)&255 if second else delta
    body=start<=pc<stop
    index=pc&15 if pc<start else (2+(within&3) if within<bits else 6+((within-bits)&3)) if pc<stop else ((pc-stop)+10)&15
    word=image[index] if index<15 else 4
    if body and within<bits:
        bit=(image[15+second]>>(7-((within>>2)&7)))&1
        word=(word & ~(1<<7)) | ((1-bit)<<7)
    if body and within==(bits+2)&255: word=(word & ~(1<<37)) | (int(second)<<37)
    if body and within==(bits+3)&255 and second: word &= (1<<41)-1
    return 4 if pc>=((stop+5)&255) else word


class Repetition(ns['Atomic']):
    def __init__(self):
        super().__init__()
        self.peer=ns['core']['Machine'](False)
        self.peer.words=[4]*256
        self.expected_pending=[4]*256
    def read(self,pc): return fetch(self.images[self.read_bank],pc)
    def edge(self,init=0,reset=0,command=0,data=0,incoming=0):
        c=self.cursor; old_active=self.active; old_valid=self.committed; old_busy=1<=self.s[0]<=4
        good = True if c<15 else data<256 if c<17 else data==[2,36,32,74][c-17] if c<21 else data==4 if c<320 else True
        effective=6 if command==2 and not good else command
        super().edge(init,reset,effective,4 if 15<=c<64 else data,incoming)
        if self.gates[0]: self.images[1-old_active][c]=data
        self.rows[-1][2:4]=[command,data]
        self.peer.idle=list(self.idle); self.peer.last=self.last
        if self.gates[1]: self.peer.words=list(self.expected_pending)
        if init or reset or not old_valid or self.gates[1]: self.peer.stop(0,0)
        elif old_busy: self.peer.advance(incoming)
        elif self.gates[2]: self.peer.enter(0,0,incoming)
        assert self.peer.s==self.s, ('literal peer mismatch',len(self.rows),self.peer.s,self.s)
        self.rows[-1].append(self.peer.words[self.s[1]] if 1<=self.s[0]<=4 else 4)
    def load_profile(self,name):
        self.edge(reset=1); self.edge(command=1)
        self.expected_pending=profiles[name][1]
        for word in profiles[name][0]:
            self.edge(command=2,data=word); assert self.gates[0]
        self.edge(command=3); assert self.gates[1]


def transaction(m, outgoing=(0xa6,0xa6), acks=(1,1), stretched=False):
    m.edge(command=5,incoming=3)
    previous,previous_command=[1,1],[0,0]
    target_sda=stretch_left=releases=starts=0
    stopped=False; clocks=[]; pending=None; rise_at=fall_at=0
    for t in range(2000):
        assert m.s[4]==0 and m.s[5]<4
        command=[m.s[5]&1,(m.s[5]>>1)&1]
        if previous_command[0] and not command[0]:
            stretch_left=releases%4 if stretched else 0; releases+=1
        bus=[int(not(command[0] or stretch_left)),int(not(command[1] or target_sda))]
        if previous[0] and bus[0] and previous[1]!=bus[1]:
            assert t-rise_at>=4
            if previous[1]: starts+=1; assert starts==1
            else: assert starts; stopped=True
            pending=None
        if not previous[0] and bus[0] and starts and not stopped:
            assert t-fall_at>=4; rise_at,pending=t,bus[1]
        if previous[0] and not bus[0]:
            fall_at=t
            if pending is not None:
                assert t-rise_at>=4; clocks.append(pending); pending=None
        if not bus[0]:
            k=len(clocks); target_sda=acks[k//9] if k in [8,17] else 0
        bus=[bus[0],int(not(command[1] or target_sda))]
        if bus[0] and pending is not None and len(clocks)%9==8: assert not command[1]
        m.edge(command=t%7+1,data=(1<<64)-1,incoming=bus[0] | bus[1]<<1)
        assert m.gates==[0,0,0,1]
        previous,previous_command=bus,command; stretch_left=max(0,stretch_left-1)
        if m.s[0]>=5: break
    assert m.s[0]==5 and stopped and starts==1
    assert len(clocks)==(18 if acks[0] else 9)
    for k,bit in enumerate(clocks):
        expected=1-acks[k//9] if k%9==8 else (outgoing[k//9]>>(7-k%9))&1
        assert bit==expected,(k,bit,expected)
    return t+1


def generate():
    global profiles
    profiles={name:(list(map(int,(OUT/(name+'.txt')).read_text().split())),list(map(int,(OUT/(name+'-explicit.txt')).read_text().split()))) for name in ['image','changed']}
    assert all(len(raw)==322 and len(explicit)==256 for raw,explicit in profiles.values())
    assert profiles['image'][0][:15]==profiles['changed'][0][:15]
    m=Repetition(); m.edge(init=1)
    for command in range(8): m.edge(command=command,data=(1<<64)-1)
    m.load_profile('image')
    transfers=[]
    for stretched in [False,True]:
        for a in [0,1]:
            for b in [0,1]: transfers.append(transaction(m,acks=(a,b),stretched=stretched))
    interruptions=[]
    for cut in [0,14,15,16,17,20,21,63,64,319,320,321,322]:
        for ending in ['abort','reset','restart']:
            m.edge(command=1); m.expected_pending=profiles['changed'][1]
            for word in profiles['changed'][0][:cut]: m.edge(command=2,data=word)
            if cut<322: m.edge(command=3); assert m.gates[3]
            m.edge(reset=1) if ending=='reset' else m.edge(command=4 if ending=='abort' else 1)
            m.edge(command=3); assert m.gates[3]
            transfers.append(transaction(m,stretched=True))
            interruptions.append(dict(cut=cut,ending=ending))
    m.edge(command=1); m.expected_pending=profiles['changed'][1]
    rejected=0
    for c,word in enumerate(profiles['changed'][0]):
        bad=(1<<63) if c<15 else 256 if c<17 else 0 if c<320 else 64 if c==320 else 256
        m.edge(command=2,data=bad); assert m.gates[3] and m.cursor==c; rejected+=1
        m.edge(command=2,data=word); assert m.gates[0]
    transfers.append(transaction(m,stretched=True)) # full staging image cannot commit while busy
    m.edge(command=3); assert m.gates[1]
    transfers.append(transaction(m,(0x24,0x5a),stretched=True))
    m.edge(command=5,incoming=0)
    for _ in range(8): m.edge(incoming=0)
    assert m.s[0]==6
    m.edge(command=5,incoming=3); m.edge(reset=1,command=3); assert m.s[0]==0
    m.edge(init=1,command=5); assert not m.committed
    m.load_profile('image'); transfers.append(transaction(m))
    (OUT/'vectors.txt').write_text(''.join(' '.join(map(str,row))+'\n' for row in m.rows))
    names=[f'template{k}' for k in range(15)]+['byte0','byte1']+[f'descriptor{k}' for k in range(4)]
    observe='\n'.join(f'assign observed[{b*322+k}] = '+(f'dut.r_bank{b}_{names[k]}' if k<21 else "64'd4" if k<320 else f'dut.r_bank{b}_'+('idle' if k==320 else 'last'))+';' for b in range(2) for k in range(322))+'\n'
    (OUT/'observe.svh').write_text(observe)
    tb=(ROOT/'test/loader_tb.sv').read_text().replace('pinwheel_atomic_indexed','pinwheel_atomic_repetition').replace('build/loader/memory-observe.svh','build/storage/repetition/observe.svh').replace('build/loader/vectors.txt','build/storage/repetition/vectors.txt')
    tb=tb.replace('  reg [15:0] e_samples;', '  reg [15:0] e_samples; reg [63:0] e_word;')
    tb=tb.replace('%d %d %d %d\\n"','%d %d %d %d %d\\n"').replace('e_enabled, e_samples);','e_enabled, e_samples, e_word);').replace('status != 20','status != 21')
    tb=tb.replace('      for (k = 0;', '      if (busy && dut.r_cached_word !== e_word) $fatal(1,"LOADER edge %0d repetition cached word",count);\n      for (k = 0;')
    (OUT/'runtime_tb.sv').write_text(tb)
    coverage=dict(edges=len(m.rows),literal_peer_edges=len(m.rows),transfers=len(transfers),quiet_cycles=transfers[3],stretched_cycles=transfers[7],interruptions=interruptions,rejected_values=rejected,same_templates_changed_data=True)
    (OUT/'coverage.json').write_text(json.dumps(coverage,indent=2)+'\n')
    print(coverage['edges'],'repetition/literal peer edges;',len(transfers),'wire transactions',flush=True)
    return coverage

if __name__=='__main__':generate()
