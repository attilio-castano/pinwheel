#!/usr/bin/env python3
import copy
from dataclasses import replace
from pathlib import Path
import sys
from types import SimpleNamespace
import unittest

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
import streaming_tt_wire_binding as W
from streaming_tt_certificate import PhysicalFF
from streaming_mapped_liberty import Cell,Library


class BindingTests(unittest.TestCase):
    def setUp(self):
        self.ff=PhysicalFF('["engine.core.ff"]','sg13cmos5l_dfrbpq_1',1,2,3,4)
        self.graph=SimpleNamespace(flipflops=(self.ff,))
        self.row=dict(component='core-d2',register='r_stage1',index=0,ff=self.ff.name,q=2,d=1,clock=3,cell=self.ff.cell)
        self.cell=Cell(self.ff.cell,dict(Q='output',D='input',CLK='input',RESET_B='input'),'Q','IQ',
            ('variable','IQ'),True,('IQ','IQN'),('variable','CLK'),('variable','D'),('not',('variable','RESET_B')))
        self.lib=Library('pin',{self.cell.name:self.cell},True)

    def test_exact_mapping(self):
        flat=W.labels(self.graph,[self.row],count=1);rows,resized=W.actual_rows(self.graph,flat,self.lib,count=1)
        self.assertEqual(rows[0]['actual_ff'],self.ff.name);self.assertEqual(resized,[])

    def test_unknown_missing_and_alias_refused(self):
        for rows in ([],[dict(self.row,ff='unknown')],[self.row,self.row]):
            with self.assertRaises(ValueError):W.labels(self.graph,rows,count=1)
        aliased=dict(self.row,ff='["engine/core/ff"]',index=1)
        with self.assertRaises(ValueError):W.labels(self.graph,[self.row,aliased],count=2)

    def test_wrong_pin_and_semantic_refused(self):
        for row in (dict(self.row,q=9),dict(self.row,q=True),dict(self.row,index=True),dict(self.row,component='unknown')):
            with self.assertRaises(ValueError):W.labels(self.graph,[row],count=1)

    def test_resize_requires_actual_sequential_correspondence(self):
        flat=W.labels(self.graph,[self.row],count=1);resized=replace(self.ff,cell='sg13cmos5l_dfrbpq_2')
        self.lib.cells[resized.cell]=replace(self.cell,name=resized.cell)
        rows,changes=W.actual_rows(SimpleNamespace(flipflops=(resized,)),flat,self.lib,count=1)
        self.assertEqual(len(changes),1)
        self.lib.cells[resized.cell]=replace(self.cell,name=resized.cell,clear=('variable','RESET_B'))
        with self.assertRaises(ValueError):W.actual_rows(SimpleNamespace(flipflops=(resized,)),flat,self.lib,count=1)

    def test_actual_alias_unknown_and_missing_refused(self):
        flat=W.labels(self.graph,[self.row],count=1)
        for ffs in ((),(replace(self.ff,name='["unknown"]'),),(self.ff,self.ff)):
            with self.assertRaises(ValueError):W.actual_rows(SimpleNamespace(flipflops=ffs),flat,self.lib,count=1)

    def test_both_actual_sampler_stages_required(self):
        row=dict(semantic='core-d2:r_stage1:0',actual_ff=self.ff.name,actual_q=2,actual_d=1,actual_clock=3,actual_reset_b=4)
        with self.assertRaises(ValueError):W.make_binding([row],{},'pin')
        second=dict(row,semantic='core-d2:r_stage2:0',actual_ff='["stage2"]')
        self.assertEqual(set(W.make_binding([row,second],{},'pin')['bindings']),{'stage1','stage2'})
        with self.assertRaises(ValueError):W.make_binding([row,dict(second,actual_ff=self.ff.name)],{},'pin')

    def test_dynamic_imports_in_dependency_closure(self):
        closure=W.dependency_closure(W.P.ROOT,['scripts/streaming_tt_wire_binding.py','scripts/streaming_tt_export_odb.py'])
        self.assertIn('scripts/run-streaming-tt-wire.py',closure['files'])
        self.assertIn('scripts/run-streaming-tt-sta.py',closure['files'])
        self.assertIn('scripts/streaming_tt_export_odb.py',closure['files'])


if __name__=='__main__':unittest.main()
