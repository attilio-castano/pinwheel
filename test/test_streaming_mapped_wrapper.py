"""Actual boundary preservation: clock, complete ABI, pin order and renames."""
from copy import deepcopy
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
from streaming_mapped_wrapper import PADS,ENGINE,CUT_PREFIX,cut_engine,restore_engine,renamed_modules,merge_modules,read_document


def fixture():
    ports,at = {},2
    for name,(direction,width) in PADS.items():
        ports[name]=dict(direction=direction,bits=list(range(at,at+width))); at+=width
    connections={}
    for name,(_,width) in ENGINE.items():
        connections[name]=ports['clk']['bits'] if name=='clk' else list(range(at,at+width)); at+=width
    return dict(modules={'top':dict(ports=ports,netnames={},cells={
        'engine':dict(type='package',parameters={},port_directions={k:v[0] for k,v in ENGINE.items()},
            connections=connections),
        'gate':dict(type='$not',parameters={},port_directions=dict(A='input',Y='output'),
            connections=dict(A=ports['ena']['bits'],Y=connections['initialize']))})})


class WrapperTests(unittest.TestCase):
    def test_actual_wrapper_json_duplicate_keys_are_refused(self):
        with tempfile.TemporaryDirectory() as temporary:
            path=Path(temporary)/'actual.json'
            path.write_text('{"modules":{"top":{},"top":{}}}')
            with self.assertRaisesRegex(ValueError,'Duplicate'):read_document(path)
            path.write_text('{"modules":{"top":{"ports":{}}}}')
            self.assertEqual(read_document(path),{'modules':{'top':{'ports':{}}}})

    def test_cut_retains_actual_pin_order_and_restore_uses_mapped_ids(self):
        original=fixture(); cut,boundary=cut_engine(original,'top','package')
        self.assertEqual(original,fixture())
        self.assertNotIn('clk',cut['modules']['top']['ports'])
        for name,port in cut['modules']['top']['ports'].items():
            if name.startswith(CUT_PREFIX): port['bits']=[i+1000 for i in port['bits']]
        restored=restore_engine(cut,boundary)['modules']['top']
        self.assertEqual(set(restored['ports']),set(PADS))
        cell=restored['cells']['engine']
        for pin in ENGINE:
            if pin!='clk': self.assertEqual(cell['connections'][pin],
                [i+1000 for i in original['modules']['top']['cells']['engine']['connections'][pin]])
        self.assertEqual(cell['connections']['clk'],restored['ports']['clk']['bits'])
        self.assertGreater(restored['ports']['clk']['bits'][0],1000)

    def test_clock_changed_abi_extra_engine_or_child_refused(self):
        variants=[]
        changed=fixture(); changed['modules']['top']['cells']['engine']['connections']['clk']=[999]; variants.append(changed)
        changed=fixture(); changed['modules']['top']['ports']['ena']['bits']=[998,999]; variants.append(changed)
        changed=fixture(); changed['modules']['top']['cells']['second']=deepcopy(changed['modules']['top']['cells']['engine']); variants.append(changed)
        changed=fixture(); changed['modules']['top']['cells']['gate']['type']='hidden'; variants.append(changed)
        for changed in variants:
            with self.subTest(changed=changed),self.assertRaises(ValueError): cut_engine(changed,'top','package')

    def test_missing_reversed_or_extra_virtual_ports_refused(self):
        cut,boundary=cut_engine(fixture(),'top','package')
        for mode in ('missing','reversed','extra'):
            changed=deepcopy(cut); ports=changed['modules']['top']['ports']
            if mode=='missing': del ports[CUT_PREFIX+'mosi']
            elif mode=='reversed': ports[CUT_PREFIX+'mosi']['direction']='input'
            else: ports['extra']=dict(direction='input',bits=[999])
            with self.subTest(mode=mode),self.assertRaises(ValueError): restore_engine(changed,boundary)

    def test_rename_changes_definitions_and_actual_uses_together(self):
        data=dict(modules={'top':dict(cells={'child':dict(type='word')}),'word':dict(cells={'gate':dict(type='lib')})})
        result=renamed_modules(data,'top','front_',{'lib'})
        self.assertEqual(set(result),{'top','front_word'})
        self.assertEqual(result['top']['cells']['child']['type'],'front_word')
        self.assertEqual(result['front_word']['cells']['gate']['type'],'lib')
        self.assertEqual(data['modules']['top']['cells']['child']['type'],'word')
        with self.assertRaises(ValueError): merge_modules(result,result)
        with self.assertRaises(ValueError): renamed_modules(data,'top','bad prefix',{'lib'})
        with self.assertRaises(ValueError): renamed_modules(data,'top','ok_',set())


if __name__=='__main__': unittest.main()
