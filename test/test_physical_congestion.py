from pathlib import Path
import sys
import unittest
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
from physical_congestion import reconcile_markers


def fixture():
    box=[0,0,7200,7200]
    marker=dict(comment='capacity:0 usage:1 overflow:1',waived='false',
        shape=[dict(type='box',points=[dict(x='0',y='0'),dict(x='7.2',y='7.2')])],
        sources=[dict(type='net',name='crossing')])
    native={'Global route':dict(source='GRT',category={'Horizontal congestion':dict(source='GRT',violations=[marker])})}
    grid=dict(database_sha256='frozen',dbu_per_micron=1000,grid_x=[0,7200],grid_y=[0,7200],
        layers={'Metal3':dict(capacity=[[17,17],[17,17]],usage=[[18,17],[17,17]],
            hotspots=[dict(index=[0,0],capacity=17,usage=18,overflow=1)])})
    context=dict(database_sha256='frozen',dbu_per_micron=1000,layers={'Metal3':dict(direction='HORIZONTAL')},
        nets={'crossing':dict(type='SIGNAL'),'touching':dict(type='CLOCK')},
        macro_obstructions=[dict(layer='Metal3',bbox_dbu=box)])
    guides=[dict(net=n,layer='Metal3',bbox_dbu=box) for n in context['nets']]
    return [native,grid,context,1,guides]


class Congestion(unittest.TestCase):
    def test_zero_available_capacity_is_not_seventeen_signal_tracks(self):
        result=reconcile_markers(*fixture());h=result['hotspots'][0]
        self.assertEqual((h['available_capacity'],h['routed_demand'],h['capacity_reduction']),(0,1,17))
        self.assertEqual(h['crossing_nets'],['crossing'])
        self.assertEqual(h['guide_only_nets'],['touching'])
        self.assertEqual(result['zero_capacity_edges'],1)

    def test_stale_markers_are_rejected_even_when_retained_in_a_new_database(self):
        args=fixture();args[1]['layers']['Metal3']['hotspots']=[];args[3]=0
        with self.assertRaisesRegex(ValueError,'stale'):reconcile_markers(*args)

    def test_incomplete_duplicate_or_wrong_source_is_rejected(self):
        for mutate in [lambda a:a[0]['Global route']['category']['Horizontal congestion']['violations'].clear(),
                       lambda a:a[0]['Global route']['category']['Horizontal congestion']['violations'].__imul__(2),
                       lambda a:a[0]['Global route'].update(source='other'),
                       lambda a:a[2].update(database_sha256='wrong')]:
            a=fixture();mutate(a)
            with self.subTest(mutate=mutate),self.assertRaises(ValueError):reconcile_markers(*a)

    def test_native_budget_must_reconcile_with_heatmap(self):
        a=fixture();a[0]['Global route']['category']['Horizontal congestion']['violations'][0]['comment']='capacity:0 usage:2 overflow:2'
        with self.assertRaisesRegex(ValueError,'reconcile'):reconcile_markers(*a)

    def test_flow_total_must_match(self):
        a=fixture();a[3]=2
        with self.assertRaisesRegex(ValueError,'coverage'):reconcile_markers(*a)

    def test_unknown_source_net_or_missing_guide_is_rejected(self):
        for mutate in [lambda a:a[0]['Global route']['category']['Horizontal congestion']['violations'][0]['sources'][0].update(name='unknown'),
                       lambda a:a[4].pop(0)]:
            a=fixture();mutate(a)
            with self.assertRaises(ValueError):reconcile_markers(*a)


if __name__=='__main__':unittest.main()
