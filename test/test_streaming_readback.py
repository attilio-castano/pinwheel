"""Refusal and extraction tests for the complete streaming artifact adapters."""
import copy
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
import streaming_readback as r
import streaming_wrapper as emitter
import streaming_wrapper_readback as w


def assembly(rb):
    result = dict(schema=1,module=rb.TOP)
    if rb.KIND == 'core':
        result['addr_bits'] = rb.ADDR_BITS
    for key,ports in [('inputs',rb.INPUTS),('registers',rb.REGISTERS),('outputs',rb.OUTPUTS)]:
        result[key] = [dict(name=n,width=bits,**({'reference':n} if key=='registers' else {}))
            for n,(bits,_) in ports.items()]
    return result


class Readback(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)

    def test_complete_state_and_private_backend(self):
        for kind,a,count,bits in [('core',1,105,4636),('core',2,113,4792),('frontend',1,28,1403)]:
            rb = r.backend(kind,a)
            self.assertEqual((len(rb.REGISTERS),sum(w for w,_ in rb.REGISTERS.values())),(count,bits))
            path = self.root/'assembly.json'
            path.write_text(json.dumps(assembly(rb)))
            r.check_interface(rb,path)
        import backend_readback
        self.assertNotEqual(backend_readback.TOP,rb.TOP)

    def test_missing_duplicate_alias_width_and_depth_refuse(self):
        rb = r.backend('core',1)
        original = assembly(rb)
        changed = []
        for key in ('inputs','registers','outputs'):
            for op in ('missing','duplicate','width'):
                item = copy.deepcopy(original)
                if op=='missing': item[key].pop()
                elif op=='duplicate': item[key].append(item[key][0])
                else: item[key][0]['width'] += 1
                changed.append(item)
        item = copy.deepcopy(original)
        item['registers'][0]['reference'] = 'r_word1'
        changed.append(item)
        item = copy.deepcopy(original)
        item['addr_bits'] = 2
        changed.append(item)
        for item in changed:
            path = self.root/'assembly.json'
            path.write_text(json.dumps(item))
            with self.subTest(item=item),self.assertRaises(ValueError):
                r.check_interface(rb,path)
        for kind,a in [('unknown',1),('core',True),('core',3)]:
            with self.assertRaises(ValueError): r.backend(kind,a)

    def wrappers(self,a=1,mutation=None):
        package = emitter.package_source(assembly(r.backend('core',a)),assembly(r.backend('frontend',a)))
        tiny = emitter.tt_source(2**a)
        texts = dict(package=package,tiny=tiny)
        if mutation:
            name,old,new = mutation
            self.assertIn(old,texts[name])
            texts[name] = texts[name].replace(old,new,1)
        paths = {}
        for name,text in texts.items():
            paths[name] = self.root/(name+'.sv')
            paths[name].write_text(text)
        return w.read_bundle(paths['package'],paths['tiny'],a)

    def test_actual_wrapper_extraction_both_depths(self):
        for a in (1,2):
            bundle = self.wrappers(a)
            self.assertEqual(len(bundle['frontend']),33)
            self.assertEqual(len(bundle['controller']),15)
            self.assertEqual(bundle['clocks'],['clk','clk'])
            text = w.lean_source(bundle)
            self.assertIn('theorem package_correct',text)
            self.assertIn('theorem tiny_correct',text)
            self.assertIn('tt_um_pinwheel_streaming_d'+str(2**a),text)

    def test_real_mutations_are_extracted_without_canonical_substitution(self):
        for label,name,old,new in w.mutation_specs()[1:]:
            with self.subTest(label=label):
                bundle = self.wrappers(mutation=(name,old,new))
                if label=='package-wire':
                    self.assertEqual(bundle['frontend']['status_generation'],('status','transfer'))
                elif label=='package-clock':
                    self.assertEqual(bundle['clocks'][0],'sck')
                else:
                    line = next(line for line in w.lean_source(bundle).splitlines() if line.startswith('  | .oe =>'))
                    self.assertIn('TinyWiring.Input.engine .levels',line)
                    self.assertNotIn('TinyWiring.Input.engine .enabled',line)

    def test_hidden_state_unsupported_logic_missing_or_multiple_driver_refuse(self):
        cases = [('package','wire core_initialize','reg core_initialize'),
            ('package','endmodule','always @(posedge clk) begin end\nendmodule'),
            ('package','.core_command(core_command)', '.core_command(missing)'),
            ('package','assign busy = status_busy;','assign busy = status_busy;\nassign busy = status_busy;'),
            ('tiny','wire active = ena && rst_n;', 'wire active = ena || rst_n;'),
            ('tiny','wire _unused =','wire _unused = missing &&')]
        for mutation in cases:
            with self.subTest(mutation=mutation),self.assertRaises(ValueError):
                self.wrappers(mutation=mutation)

    def test_model_array_getelem_and_prefixes(self):
        rb = r.backend('core',1)
        class Graph:
            next = {n:n for n in rb.REGISTERS}
            outputs = {n:n for n in rb.OUTPUTS}
        original = rb.graph_value
        rb.graph_value = lambda graph,node,namespace: '0'
        try:
            text = r.model_source(rb,Graph())
        finally:
            rb.graph_value = original
        self.assertNotIn("]) [",text)
        self.assertIn("])[k.toNat]'",text)
        self.assertEqual(r.prefix_imports('import Proof\nimport Model\n','CoreD2'),
            'import CoreD2Proof\nimport CoreD2Model\n')
        with self.assertRaises(ValueError): r.prefix_imports('import Proof','../evil')


if __name__=='__main__': unittest.main()
