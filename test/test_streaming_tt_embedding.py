"""A nonidentity state/input embedding is checked by actual kernel rules."""
import copy
from pathlib import Path
import os
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
from streaming_tt_embedding import component_plan,generate
from streaming_tt_graph import network_sources


class PhysicalEmbedding(unittest.TestCase):
    def fixture(self):
        parent=dict(labels=(('input','unused',0),('input','used',0),('state','r_q:0')),
            nodes=(dict(name='["component","gate"]',cell='actual_and',sources=(1,2),
                expression=('*',('variable','p0'),('variable','p1'))),),next={},outputs={})
        child=dict(labels=(('input','A',0),('state','r_q:0')),
            nodes=(dict(name='["gate"]',cell='actual_and',sources=(0,1),
                expression=('*',('variable','p0'),('variable','p1'))),),next={},outputs={})
        hierarchy={('component',):dict(ports={'A':(11,),'Y':(30,),'clk':(99,)},local={5:20})}
        body={'netnames':{'r_q':{'bits':[5]}}}
        return parent,child,hierarchy,body

    def test_connected_function_and_primary_pairing_are_not_names(self):
        parent,child,hierarchy,body=self.fixture()
        plan=component_plan(parent,child,{11:1,20:2,30:3},hierarchy,body,('component',))
        self.assertEqual(plan['image'],(('wire',1,False),('wire',2,False),('wire',3,False)))
        self.assertEqual(plan['clock_port'],(99,))
        changed=copy.deepcopy(child);changed['nodes'][0]['expression']=('+',('variable','p0'),('variable','p1'))
        with self.assertRaisesRegex(ValueError,'Boolean cell differs'):
            component_plan(parent,changed,{11:1,20:2,30:3},hierarchy,body,('component',))
        with self.assertRaisesRegex(ValueError,'Boolean cell differs'):
            component_plan(parent,child,{11:0,20:2,30:3},hierarchy,body,('component',))

    def test_kernel_rejects_forged_primary_image(self):
        if shutil.which('lake') is None:
            self.skipTest('Native Lean unavailable')
        dependency=ROOT/'.lake/build/lib/lean/Pinwheel/Hardware/StreamingPhysical/Embedding.olean'
        if not dependency.is_file():
            self.skipTest('Native Lean physical Embedding library is not built in this environment')
        (ROOT/'build').mkdir(exist_ok=True)
        parent,child,hierarchy,body=self.fixture()
        plan=component_plan(parent,child,{11:1,20:2,30:3},hierarchy,body,('component',))
        with tempfile.TemporaryDirectory(prefix='physical-embedding-',dir=ROOT/'build') as temporary:
            out=Path(temporary);modules,p=network_sources(parent,prefix='TestParent',namespace='TestParent')
            new,c=network_sources(child,prefix='TestChild',namespace='TestChild');modules.update(new)
            new,_=generate(child,plan,p,c,prefix='TestEmbedding',namespace='TestEmbedding');modules.update(new)
            env=dict(os.environ,LEAN_PATH=str(out))
            for name,text in modules.items():
                (out/(name+'.lean')).write_text(text)
                result=subprocess.run(['lake','env','lean','--root='+str(out),'-DwarningAsError=true','-o',str(out/(name+'.olean')),str(out/(name+'.lean'))],cwd=ROOT,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=60)
                self.assertEqual(result.returncode,0,(name,result.stdout.decode()))
            forged=copy.deepcopy(plan);forged['image']=(('wire',0,False),*forged['image'][1:])
            mutated,_=generate(child,forged,p,c,prefix='BadEmbedding',namespace='BadEmbedding')
            for name,text in mutated.items():
                (out/(name+'.lean')).write_text(text)
                result=subprocess.run(['lake','env','lean','--root='+str(out),'-DwarningAsError=true','-DmaxErrors=1','-o',str(out/(name+'.olean')),str(out/(name+'.lean'))],cwd=ROOT,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=60)
                if result.returncode:
                    self.assertIn('connected',text)
                    self.assertIn('decide',result.stdout.decode())
                    break
            else:self.fail('Kernel accepted a forged component primary connection')


if __name__=='__main__':unittest.main()
