"""Balancing must preserve logic and reject unbound physical guidance."""
from copy import deepcopy
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
from mapped_buffer_balance import contract, inventory, morton, rebalance
from physical_buffer_repair import _bufferless


def fixture(count=74):
    def port(direction, bits):
        return dict(direction=direction, bits=bits)

    def cell(kind, a, y, output):
        return dict(type=kind, hide_name=0, parameters={}, attributes={},
            connections={'A': [a], output: [y]}, port_directions={'A': 'input', output: 'output'})

    buffers, gates = {}, {}
    for k in range((count+6)//7):
        buffers[f'b{k}'] = cell('sg13cmos5l_buf_1', 3 if k == 0 else 10+k-1, 10+k, 'X')
    for k in range(count):
        gates[f'g{k:03d}'] = cell('inv', 10+k//7, 1000+k, 'Y')
    module = dict(attributes={}, ports={'clk': port('input',[2]), 'data':port('input',[3]),
        'out':port('output',list(range(1000,1000+count)))}, cells={**buffers, **gates},
        netnames={'data_alias':dict(bits=[3],attributes={}),
                  'unused_reserved':dict(bits=['x','x'],attributes={})})
    lib = lambda out, area: dict(attributes={'blackbox':'1','area':str(area)}, cells={},
        ports={'A':port('input',[2]),out:port('output',[3])})
    data = dict(modules={'top':module,'sg13cmos5l_buf_1':lib('X',7.2576),'inv':lib('Y',4)})
    context = dict(database_sha256='f'*64, instances={n:dict(cell=c['type'],
        bbox_dbu=[(k%10)*100,(k//10)*100,(k%10)*100+20,(k//10)*100+20])
        for k,(n,c) in enumerate(module['cells'].items())})
    return data, context


class BufferBalancing(unittest.TestCase):
    def test_shallow_trees_preserve_every_nonbuffer_connection_and_alias(self):
        data, context = fixture()
        saved = deepcopy(data)
        after, report = rebalance(data,'top',context)
        self.assertEqual(data,saved)
        self.assertEqual(_bufferless(saved['modules']['top']),_bufferless(after['modules']['top']))
        self.assertEqual(report['original_forests'][0]['maximum_levels'],11)
        self.assertEqual(report['balanced_forests'][0]['maximum_levels'],2)
        self.assertEqual(report['balanced_forests'][0]['sink_pins'],74)
        self.assertEqual(after['modules']['top']['netnames']['unused_reserved']['bits'],['x','x'])
        self.assertEqual(after['modules']['top']['ports']['clk'],saved['modules']['top']['ports']['clk'])

    def test_geometry_is_required_and_cell_types_must_match(self):
        for mutate in [lambda c:c['instances'].pop('g000'),
                       lambda c:c['instances']['g000'].__setitem__('cell','different'),
                       lambda c:c['instances']['g000'].__setitem__('bbox_dbu',[0,0,0,2])]:
            data, context = fixture()
            mutate(context)
            with self.assertRaises(ValueError):
                rebalance(data,'top',context)

    def test_clock_buffers_cannot_be_rebalanced(self):
        data,_=fixture()
        data['modules']['top']['cells']['b0']['connections']['A']=[2]
        with self.assertRaisesRegex(ValueError,'Clock trees'):
            contract(data['modules']['top'])

    def test_cycle_floating_input_and_multiple_driver_rejected(self):
        for value in [10,99999,'x',1000]:
            data,_=fixture()
            cell=data['modules']['top']['cells']['b0']
            if value==1000:
                cell['connections']['X']=[value]
            else:
                cell['connections']['A']=[value]
            with self.subTest(value=value), self.assertRaises(ValueError):
                contract(data['modules']['top'])

    def test_order_is_deterministic_and_guidance_changes_only_transport(self):
        data,context=fixture()
        left,_=rebalance(data,'top',context)
        again,_=rebalance(data,'top',context)
        self.assertEqual(left,again)
        for n,c in context['instances'].items():
            x,y,xx,yy=c['bbox_dbu'];c['bbox_dbu']=[y,x,yy,xx]
        right,_=rebalance(data,'top',context)
        self.assertEqual(_bufferless(left['modules']['top']),_bufferless(right['modules']['top']))
        self.assertEqual(inventory(right['modules']['top'])[0]['sink_pins'],74)
        with self.assertRaises(ValueError):
            morton(-1,0)


if __name__=='__main__':
    unittest.main()
