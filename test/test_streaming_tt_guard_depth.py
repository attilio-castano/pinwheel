"""Raw semantic-cut/depth observer controls; no synthesis or Lean."""
from copy import deepcopy
import json
from pathlib import Path
import sys
import tempfile
import unittest

ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'scripts'))
import streaming_tt_guard_depth as G


def fixture(kind,balanced):
    cut=list(range(1,8));state=list(range(100,164));cells={};next_wire=1000
    def gate(kind,a,b=None):
        nonlocal next_wire
        wire=next_wire;next_wire+=1;connections={'A':list(a),'Y':[wire]}
        if b is not None:connections['B']=list(b)
        cells['cell'+str(wire)]={'type':kind,'connections':connections,'port_directions':{p:'output' if p=='Y' else 'input' for p in connections},'parameters':{}}
        return wire
    def bits(n):return [str((n>>i)&1) for i in range(7)]
    leaves=[]
    for index,stored in enumerate(state):
        comparison=gate('$lt',bits(index) if kind=='core' else cut,cut if kind=='core' else bits(64-index))
        operand=gate('$not',[stored]) if kind=='core' else stored
        leaves.append(gate('$not',[gate('$and',[comparison],[operand])]))
    def tree(values):
        if len(values)==1:return values[0]
        half=len(values)//2;return gate('$and',[tree(values[:half])],[tree(values[half:])])
    if balanced:root=tree(leaves)
    else:
        root=leaves[0]
        for leaf in leaves[1:]:root=gate('$and',[root],[leaf])
    gate('$and',[root],[9000])
    names={'r_written':{'bits':state}} if kind=='core' else {'r_request':{'bits':list(range(200,216))+state}}
    return {'modules':{'top':{'cells':cells,'netnames':names,'ports':{'count':{'bits':cut,'direction':'input'}}}}}


class GuardDepthTests(unittest.TestCase):
    def observe(self,data,kind):
        with tempfile.TemporaryDirectory() as name:
            p=Path(name)/'raw.json';p.write_text(json.dumps(data));return G.observe(p,'top',kind)

    def test_both_exact64_predicates_identify_balanced_and_linear_depth(self):
        for kind in ('frontend','core'):
            for balanced,depth in ((False,63),(True,6)):
                with self.subTest(kind=kind,balanced=balanced):
                    report=self.observe(fixture(kind,balanced),kind)
                    self.assertEqual(len(report['predicate_leaves']),64)
                    self.assertEqual(report['assignments_checked_per_leaf'],256)
                    self.assertEqual(len(report['guard_roots']),1)
                    self.assertEqual(report['guard_roots'][0]['predicate_context_and_depth'],depth)
                    self.assertTrue(report['guard_roots'][0]['isolated_guard_wire'])
                    self.assertEqual(report['longest_consecutive_one_bit_and_depth'],depth+1)

    def test_semantic_predicate_mutation_alias_and_duplicate_driver_refused(self):
        for kind in ('frontend','core'):
            for mutation in ('comparison','signed','alias','driver'):
                data=fixture(kind,True);module=data['modules']['top'];cells=module['cells']
                if mutation=='comparison':cells['cell1000']['connections']['A' if kind=='core' else 'B']=(['1']+['0']*6) if kind=='core' else ['0']*7
                elif mutation=='signed':cells['cell1000']['parameters']['A_SIGNED']='1'
                elif mutation=='alias':
                    bits=module['netnames']['r_written' if kind=='core' else 'r_request']['bits'];bits[-1]=bits[-2]
                else:cells['duplicate']=deepcopy(cells['cell1000'])
                with self.subTest(kind=kind,mutation=mutation),self.assertRaises(ValueError):self.observe(data,kind)

    def test_unequal_width_signed_equality_and_bitwise_extension_refused(self):
        for kind,width in (('$eq',1),('$and',2)):
            for signed in ('A_SIGNED','B_SIGNED'):
                cell={'type':kind,'connections':{'A':['1'],'B':['1','1'],'Y':list(range(10,10+width))},
                    'port_directions':{'A':'input','B':'input','Y':'output'},'parameters':{signed:'1'}}
                drv=G.drivers({'cells':{'signed':cell}})
                with self.subTest(kind=kind,signed=signed),self.assertRaisesRegex(ValueError,'Signed operator'):
                    G.evaluate(10+width-1,{},drv)


if __name__=='__main__':unittest.main()
