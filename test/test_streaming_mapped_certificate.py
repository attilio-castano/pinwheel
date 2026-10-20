"""Actual leaf expression reconstruction and generated-kernel refusal seams."""
from dataclasses import replace
import itertools
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
from streaming_mapped_certificate import expressions, full_adder_source, lean_expression, graph_source,bitwise_source
from streaming_mapped_liberty import eval_boolean, parse_library
from streaming_mapped_netlist import parse_mapped
from test_streaming_mapped_liberty import LIBRARY, TYPES
from test_streaming_mapped_netlist import fixture


class CertificateTests(unittest.TestCase):
    def setUp(self):
        self.library = replace(parse_library(LIBRARY, TYPES), pinned=True)

    def leaf(self):
        data = fixture(); module = data['modules']['top']
        module['ports'] = dict(a=dict(direction='input', bits=[2]), y=dict(direction='output', bits=[5]))
        module['cells'] = dict(inv=module['cells']['invert'])
        module['cells']['inv']['connections']['A'] = [2]
        return parse_mapped(data, 'top', self.library, combinational=True)

    def test_connected_expression_follows_actual_pins(self):
        graph = self.leaf(); variables, outputs = expressions(graph, ('a',))
        self.assertEqual(variables, ('a:0',))
        for a in (False, True):
            self.assertEqual(eval_boolean(outputs['y'][0], {'a:0': a}), not a)
        text = lean_expression(outputs['y'][0], variables)
        self.assertEqual(text, '.inv (.var ⟨0, by decide⟩)')

    def test_missing_duplicate_unknown_order_or_clocked_graph_refuses(self):
        for order in ((), ('a', 'a'), ('missing',)):
            with self.subTest(order=order), self.assertRaises(ValueError): expressions(self.leaf(), order)
        with self.assertRaises(ValueError): expressions(parse_mapped(fixture(), 'top', self.library), ('a', 'clk'))
        with self.assertRaises(ValueError): lean_expression(('variable', 'unknown'), ('a',))

    def test_full_adder_interface_and_provenance_are_mandatory(self):
        for namespace, digest in [('Bad; arbitrary', '0'*64), ('Valid', 'nohash')]:
            with self.assertRaises(ValueError): full_adder_source(self.leaf(), namespace=namespace, netlist_sha256=digest)
        with self.assertRaises(ValueError): full_adder_source(self.leaf(), netlist_sha256='0'*64)

    def test_graph_export_retains_explicit_pre_edge_q_and_actual_d(self):
        graph = parse_mapped(fixture(), 'top', self.library)
        text = graph_source(graph, netlist_sha256='0'*64)
        self.assertIn('abbrev Inputs := Fin 1 → Bool', text)
        self.assertIn('abbrev State := Fin 1 → Bool', text)
        self.assertIn('q ⟨0, by decide⟩', text)
        self.assertIn('def next ', text)
        self.assertNotIn('axiom', text)
        self.assertNotIn('native_decide', text)
        self.assertNotIn('sorry', text)

    def test_bitwise_wiring_and_local_truth_are_separate_kernel_obligations(self):
        cell=lambda a,y:dict(type='sg13cmos5l_inv_1',parameters={},port_directions=dict(A='input',Y='output'),connections=dict(A=[a],Y=[y]))
        data=dict(modules=dict(word=dict(ports=dict(A=dict(direction='input',bits=[2,3]),Y=dict(direction='output',bits=[4,5])),cells=dict(first=cell(2,4),second=cell(3,5)))))
        graph=parse_mapped(data,'word',self.library,combinational=True)
        text=bitwise_source(graph,'$not',namespace='Actual.Word',netlist_sha256='0'*64)
        self.assertIn('theorem wiring_correct',text)
        self.assertIn('theorem scalar_correct',text)
        self.assertIn('theorem raw_correct',text)
        self.assertIn('Expr.eval_map',text)
        for forbidden in ('bv_decide','native_decide','sorry','axiom '):self.assertNotIn(forbidden,text)
        # Mutate a real functional pin. The generated global expression keeps
        # A[1] in output0 while its local desired wire remains A[0]; it must be
        # proved equal by the static certificate, rather than being erased.
        data['modules']['word']['cells']['first']['connections']['A']=[3]
        mutated=bitwise_source(parse_mapped(data,'word',self.library,combinational=True),'$not',namespace='Actual.BadWord',netlist_sha256='1'*64)
        self.assertNotEqual(text,mutated)
        self.assertIn('.inv (.var ⟨1, by decide⟩)',mutated)

    def test_bitwise_type_and_namespace_reject_before_export(self):
        for operation,namespace in [('$add','Valid'),('$not','Bad;code')]:
            with self.assertRaises(ValueError):bitwise_source(self.leaf(),operation,namespace=namespace,netlist_sha256='0'*64)


if __name__ == '__main__': unittest.main()
