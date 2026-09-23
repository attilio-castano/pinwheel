from copy import deepcopy
import sys
from pathlib import Path
import unittest

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
from physical_connections import Connectivity,connection_terminals,parse_measurements
from physical_connection_probe import connection_tcl


def fixture():
    instances={
        's':dict(cell='sg13cmos5l_dfrbpq_1',macro=False,bbox_dbu=[0,0,4,4]),
        'd':dict(cell='sg13cmos5l_buf_1',macro=False,bbox_dbu=[10,0,12,4]),
        'q':dict(cell='sg13cmos5l_dfrbpq_1',macro=False,bbox_dbu=[20,0,24,4]),
        'clockbuf':dict(cell='sg13cmos5l_buf_8',macro=False,bbox_dbu=[30,0,36,4]),
        'hold':dict(cell='sg13cmos5l_dlygate4sd3_1',macro=False,bbox_dbu=[40,0,43,4]),
        'memory':dict(cell='RM_IHP',macro=True,bbox_dbu=[60,10,90,40])}
    for i in instances.values():i['bbox']=i['bbox_dbu'][:]
    def net(terms,ports=[]):
        return dict(type='SIGNAL',ports=ports,terminals=[dict(instance=i,pin=p,direction=d) for i,p,d in terms])
    context=dict(database_sha256='frozen',dbu_per_micron=1,die=[0,0,100,50],instances=instances,
        rows=[dict(bbox_dbu=[0,0,100,4]),dict(bbox_dbu=[0,4,100,8])],placement_blockages=[],
        nets={'src':net([('s','Q','OUTPUT'),('d','A','INPUT'),('hold','A','INPUT')]),
              'n':net([('d','X','OUTPUT'),('q','D','INPUT')],['output']),
              'u':net([('hold','X','OUTPUT'),('memory','A_DIN[0]','INPUT')])})
    ownership=dict(registers={'serial':[dict(cell='s',bit=0)],'state':[dict(cell='q',bit=3)]})
    return context,ownership


REPORT='''PINWHEEL_CONNECTION n
Net n
 Pin capacitance: 0.02-0.03
 Wire capacitance: 0.3
 Total capacitance: 0.32-0.33
 Number of drivers: 1
 Number of loads: 1
max slew
d/X 0.5 0.6 -0.1 (VIOLATED)
max fanout
d/X 8 1 7 (MET)
max capacitance
d/X 0.4 0.33 0.07 (MET)
Startpoint: s (register)
Endpoint: q (register)
Path Type: min
 0.08 slack (MET)
Startpoint: s (register)
Endpoint: q (register)
Path Type: max
 0.4 slack (MET)
'''


class Connections(unittest.TestCase):
    def test_state_and_package_boundaries_remain_shared(self):
        c,o=fixture();g=Connectivity(c,o)
        r=g.record('n',{})
        self.assertEqual(r['source_owners'],['serial'])
        self.assertEqual(r['sink_owners'],['state'])
        self.assertTrue(r['shared'])
        self.assertEqual({p['pin'] for p in r['sink_boundary']},{'q/D','output'})

    def test_macro_boundary_and_delay_cell_do_not_erase_owner(self):
        c,o=fixture();g=Connectivity(c,o)
        r=g.record('u',{'upload':dict(sources=['s/Q'],sinks=['memory/A_DIN[0]'])})
        self.assertEqual(r['semantic_roles'],['upload'])
        self.assertEqual(r['source_owners'],['serial'])
        self.assertEqual(r['sink_boundary'],[dict(kind='macro',pin='memory/A_DIN[0]')])

    def test_missing_or_duplicate_state_owner_rejected(self):
        c,o=fixture()
        for bad in [{'registers':{}},{'registers':dict(o['registers'],extra=o['registers']['serial'])}]:
            with self.assertRaises(ValueError):Connectivity(c,bad)

    def test_clock_multiple_driver_and_inout_targets_rejected(self):
        for change in [lambda n:n.update(type='CLOCK'),
                       lambda n:n['terminals'].append(dict(instance='s',pin='Q',direction='OUTPUT')),
                       lambda n:n['terminals'][1].update(direction='INOUT')]:
            c,_=fixture();change(c['nets']['n'])
            with self.assertRaises(ValueError):connection_terminals(c,'n')

    def test_measured_limits_keep_slack_and_both_timing_sides(self):
        r=parse_measurements(REPORT,{'n'})['n']
        self.assertEqual(r['wire_cap_pf'],[.3,.3])
        self.assertEqual(r['slew']['slack'],-.1)
        self.assertEqual(r['paths']['min']['slack_ns'],.08)

    def test_incomplete_duplicate_or_nonfinite_measurement_rejected(self):
        for text in [REPORT+REPORT,REPORT.replace('Net n','Net other'),
                     REPORT.replace('0.3\n','NaN\n'),REPORT.replace('Path Type: min','Path Type: max'),
                     REPORT.split('Startpoint:')[0]]:
            with self.subTest(text=text),self.assertRaises(ValueError):parse_measurements(text,{'n'})
        with self.assertRaises(ValueError):parse_measurements(REPORT,{'n','missing'})

    def test_tcl_selector_injection_and_duplicates_rejected(self):
        row=dict(net='n',driver='d/X')
        for rows in [[row,row],[dict(row,driver='d/X}; exec bad')]]:
            with self.assertRaises(ValueError):connection_tcl(rows)


if __name__=='__main__':unittest.main()
