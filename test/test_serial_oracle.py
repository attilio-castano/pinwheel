import sys
from pathlib import Path
import unittest
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
import serial_oracle as o

class SerialOracleTests(unittest.TestCase):
    def test_width_and_type_bounds(self):
        self.assertEqual([o.widths(d)[9] for d in (4,6,10,32)], [6,6,7,9])
        for d in (True,0,2,5):
            with self.assertRaises(ValueError): o.widths(d)
        for change in ({'reset':1},{'data':True},{'device':4},{'word':64},{'rx':0},{'extra':0}):
            with self.assertRaises(ValueError): o.validate_row(dict(o.row(),**change))
        for s in ([0]*13,[False]+[0]*13,[0]*9+[64]+[0]*4):
            with self.assertRaises(ValueError): o.restore(4,s)

    def test_every_tx_byte_period_and_unique_completion(self):
        for d in (4,6,10,32):
            for byte in range(256):
                s=[0]*14; i=o.row(request_valid=True,device=2,word=1,write=True,data=byte)
                s=o.step(d,i,s)
                self.assertEqual(s[8:11],[1,0,byte])
                observed=[]; completions=0
                for _ in range(10*d):
                    pre=o.output(d,o.row(),s); observed.append(pre[7]); completions+=pre[9]
                    s=o.step(d,o.row(),s)
                self.assertEqual(observed,[int(x) for x in o.wire_frame(d,byte)])
                self.assertEqual(completions,1); self.assertEqual((s[2],s[8]),(0,0))
                for _ in range(3):
                    self.assertEqual(o.output(d,o.row(),s)[9],0); s=o.step(d,o.row(),s)

    def test_rx_sample_schedule_and_no_duplicate_arrival(self):
        for d in (4,6,10,32):
            for byte in range(256):
                s=[0]*14; arrivals=[]
                for t,line in enumerate(o.wire_frame(d,byte)+[True]*d):
                    i=o.row(rx=line); p=o.output(d,i,s)
                    if p[10]: arrivals.append((t,p[11]))
                    s=o.step(d,i,s)
                self.assertEqual(arrivals,[(d//2+9*d,byte)])
                self.assertEqual(s[4:6],[1,byte])

    def test_rx_consume_refill_and_empty_arrival(self):
        for full in (0,1):
            s=[0]*14;s[4:6]=[full,0x3c];s[11:14]=[1,37,0xc3]
            i=o.row(request_valid=True,device=2,word=2)
            self.assertEqual(o.output(4,i,s)[2:4],[0,0x3c] if full else [5,0])
            self.assertEqual(o.step(4,i,s)[4:6],[1,0xc3])

    def test_full_overrun_and_new_errors_override_clear(self):
        s=[0]*14;s[4:6]=[1,0x3c];s[11:14]=[1,37,0xc3]
        i=o.row(request_valid=True,device=2,word=3,write=True,data=12)
        n=o.step(4,i,s);self.assertEqual(n[4:8],[1,0x3c,1,0])
        n=o.step(4,dict(i,rx=False),s);self.assertEqual(n[7],1);self.assertEqual(n[11],2)

    def test_busy_completion_fault_and_next_idle_acceptance(self):
        s=[0]*14;s[2:4]=[1,0x25];s[8:11]=[1,39,0x25]
        i=o.row(request_valid=True,device=2,word=1,write=True,data=0x93)
        self.assertEqual(o.output(4,i,s)[2:4],[4,0]);n=o.step(4,i,s)
        self.assertEqual((n[2],n[8]),(0,0));self.assertEqual(o.output(4,i,n)[2],1)
        self.assertEqual(o.step(4,i,n)[8:11],[1,0,0x93])

    def test_reset_dominates_every_effect(self):
        for d in (4,6,10,32):
            s=[(1<<w)-1 for w in o.widths(d)];s[9]=10*d-1;s[11]=1;s[12]=d//2+9*d-1
            i=o.row(reset=True,request_valid=True,device=2,word=1,write=True,data=0xff,rx=False)
            self.assertEqual(o.step(d,i,s),[0]*14)
            self.assertEqual(o.output(d,i,s),[0]*7+[1,0,0,0,0,0])

    def test_invalid_selector_fault_retains_cpu_state_but_ticks(self):
        s=[0]*14;s[0]=0xa5;s[1]=0xffffffff
        for reg in range(64):
            for wr in (False,True):
                i=o.row(request_valid=True,device=3,word=reg,write=wr,data=0xffffffff)
                self.assertEqual(o.output(4,i,s)[2:4],[2,0]);n=o.step(4,i,s)
                self.assertEqual(n[0],0xa5);self.assertEqual(n[1],0);self.assertEqual(n[2:],[0]*12)

    def test_false_start_and_malformed_recovery_suppress_pulses(self):
        s=[0]*14;s[11:14]=[1,1,0x9a]
        self.assertEqual(o.step(4,o.row(),s)[11:14],[0,1,0x9a])
        for phase in range(4):
            s=[0]*14;s[8:11]=[1,63,0x55];s[11:14]=[phase,63,0x33]
            self.assertEqual(o.output(4,o.row(),s)[9:],[0,0,0,0])
            self.assertEqual(o.step(4,o.row(),s)[8],0)
            self.assertEqual(o.step(4,o.row(),s)[11],0)

    def test_complete_occurrence_ledgers(self):
        for d in (4,6,10,32):
            s,rows=o.stimulus(d);frames,events,ledger=o.oracle(d,s,rows,owned=True)
            self.assertEqual(ledger['responses'],sum(i['request_valid'] and not i['reset'] for i in rows))
            self.assertEqual(ledger['tx_starts'],ledger['tx_completions']+ledger['tx_cancelled'])
            self.assertEqual(ledger['rx_arrivals'],ledger['rx_consumed']+ledger['rx_dropped']+ledger['rx_cancelled'])
            self.assertGreater(ledger['rx_refills'],0)
            self.assertEqual(len(frames),len(events));self.assertEqual(frames[-1]['registers'],[0]*14)
            for segment in o.raw_segments(d): o.oracle(d,segment['startup'],segment['rows'])

if __name__=='__main__':unittest.main()
