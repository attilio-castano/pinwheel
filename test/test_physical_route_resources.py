"""Admission checks against missing, misplaced, and NDR-weighted demand."""
from collections import Counter
from copy import deepcopy
from pathlib import Path
import sys
import unittest
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'tools/openroad-route-import'))
from resource_checks import parse_snapshot,route_demand,verify_demand,verify_release


def fixture():
    edges={(dim,d,layer,x,y):(5,0,0)
           for dim,layers in [(2,[0]),(3,[1,2])]
           for layer in layers for d in ('H','V')
           for x in range(3-(d=='H')) for y in range(2-(d=='V'))}
    return dict(grid=(3,2,2,0,0,10),edges=edges,nets={
        'data':dict(cost=1,soft=False,layers=[1,1]),
        'clock':dict(cost=2,soft=False,layers=[1,3])})


def dump(s):
    lines=['grid\t'+'\t'.join(map(str,s['grid']))]
    lines+=['\t'.join(map(str,(*key,*v))) for key,v in s['edges'].items()]
    lines+=['\t'.join(map(str,('net',n,v['cost'],int(v['soft']),*v['layers']))) for n,v in s['nets'].items()]
    return '\n'.join(lines)+'\n'


class NativeResourceTests(unittest.TestCase):
    def test_complete_snapshot_roundtrip(self):
        s=fixture();self.assertEqual(parse_snapshot(dump(s)),s)

    def test_incomplete_duplicate_and_negative_entries(self):
        s=fixture();text=dump(s);lines=text.splitlines()
        for bad in ['\n'.join(lines[:2]+lines[3:]),text+lines[1]+'\n',text.replace('5\t0\t0','5\t0\t-1',1)]:
            with self.subTest(bad=bad[:50]),self.assertRaises(ValueError):parse_snapshot(bad)

    def test_direction_layers_and_multiplicity(self):
        segment=((5,5,'Metal2'),(25,5,'Metal2'))
        d=route_demand(fixture(),{'clock':[segment,segment,((5,5,'Metal1'),(5,5,'Metal2'))]})
        self.assertEqual(d,Counter({(2,'H',0,0,0):4,(2,'H',0,1,0):4,(3,'H',2,0,0):6,(3,'H',2,1,0):6}))

    def test_reversed_segment(self):
        a,b=(5,5,'Metal2'),(25,5,'Metal2')
        self.assertEqual(route_demand(fixture(),{'data':[(a,b)]}),route_demand(fixture(),{'data':[(b,a)]}))

    def test_unknown_cost_and_outside_grid_rejected(self):
        for routes in [{'missing':[((5,5,'Metal2'),(25,5,'Metal2'))]},
                       {'data':[((5,5,'Metal2'),(35,5,'Metal2'))]},
                       {'data':[((5,5,'Metal2'),(25,15,'Metal2'))]}]:
            with self.subTest(routes=routes),self.assertRaises(ValueError):route_demand(fixture(),routes)

    def test_all_edges_not_just_total(self):
        s=fixture();routes={'data':[((5,5,'Metal2'),(15,5,'Metal2'))]}
        for key in [(2,'H',0,0,0),(3,'H',2,0,0)]:s['edges'][key]=(5,0,1)
        self.assertEqual(verify_demand(s,routes)['demand_3d_by_layer']['2'],1)
        s['edges'][(3,'H',2,0,0)]=(5,0,0);s['edges'][(3,'H',2,1,0)]=(5,0,1)
        with self.assertRaises(ValueError):verify_demand(s,routes)

    def test_native_release_requires_both_weighted_dimensions(self):
        after=fixture();before=deepcopy(after)
        routes={'clock':[((5,5,'Metal2'),(15,5,'Metal2'))]}
        before['edges'][(2,'H',0,0,0)]=(5,0,2);before['edges'][(3,'H',2,0,0)]=(5,0,3)
        self.assertEqual(verify_release(before,after,routes)['released_3d'],3)
        after['edges'][(2,'H',0,0,0)]=(5,0,2)
        with self.assertRaises(ValueError):verify_release(before,after,routes)

    def test_release_cannot_change_capacity_or_costs(self):
        before=fixture();routes={'data':[((5,5,'Metal2'),(15,5,'Metal2'))]}
        for key in [(2,'H',0,0,0),(3,'H',2,0,0)]:before['edges'][key]=(5,0,1)
        after=fixture();after['edges'][(3,'H',2,1,1)]=(6,0,0)
        with self.assertRaises(ValueError):verify_release(before,after,routes)
        after=fixture();after['nets']['data']['soft']=True
        with self.assertRaises(ValueError):verify_release(before,after,routes)


if __name__=='__main__':unittest.main()
