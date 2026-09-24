from copy import deepcopy
import json
from pathlib import Path
import sys
import unittest

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
from physical_connections import connection_terminals
from physical_organization import Library, Planner, BufferGeometry, reconstruct, validate_exchanges, portfolios, screen_exchange_identity, validate_refinement, mechanism_screen
from tiled_chip import FF


def fixture():
    kinds={f'sg13cmos5l_buf_{n}':(w,cap) for n,w,cap in [(1,2,.004),(2,3,.007),(4,4,.011),(8,6,.02)]}
    text='capacitive_load_unit (1,pf);\n'
    for cell,(width,cap) in kinds.items():
        text+=f'''cell ({cell}) {{ area : {width*2};
          pin (A) {{ direction : input; capacitance : {cap}; }}
          pin (X) {{ direction : output; function : "A"; max_capacitance : {int(cell[-1])*.3}; }} }}\n'''
    text+='''cell (leaf) { area : 4; pin (A) { direction : input; capacitance : .01;
        rise_capacitance_range (.009,.011); fall_capacitance_range (.009,.011); } }
        cell (memory) { bus (A_DIN) { direction : input; capacitance : .004;
        pin (A_DIN[3:0]) { related_power_pin : VDD; } } }'''
    lib=Library({'fast':[text],'slow':[text]})
    inst={}
    def put(name,cell,box,macro=False):inst[name]=dict(cell=cell,bbox=box[:],bbox_dbu=box[:],macro=macro)
    put('s',FF,[40,0,42,2]);put('a','sg13cmos5l_buf_1',[0,4,2,6]);put('b','sg13cmos5l_buf_1',[90,4,92,6])
    for name,x in [('x',80),('y',85),('u',5),('v',10)]:put(name,'leaf',[x,8,x+2,10])
    for i,(cell,(w,_)) in enumerate(kinds.items()):put('size'+str(i),cell,[i*10,20,i*10+w,22])
    def net(driver,consumers):
        ds,dp=driver.split('/')
        return dict(type='SIGNAL',ports=[],terminals=[dict(instance=ds,pin=dp,direction='OUTPUT')]+
            [dict(instance=p.split('/')[0],pin=p.split('/')[1],direction='INPUT') for p in consumers])
    nets={'root':net('s/Q',['a/A','b/A']),'left':net('a/X',['x/A','y/A']),'right':net('b/X',['u/A','v/A'])}
    context=dict(database_sha256='frozen',dbu_per_micron=1,instances=inst,nets=nets,die=[0,0,100,30],
        rows=[dict(bbox_dbu=[0,y,100,y+2]) for y in range(0,30,2)],placement_blockages=[])
    records=[dict(net=n,**connection_terminals(context,n),driver_cell=inst[connection_terminals(context,n)['driver'].split('/')[0]]['cell']) for n in sorted(nets)]
    coverage=dict(source_database_sha256='frozen',connections=records,
        components=[dict(root='root',nets=sorted(nets),families=['first','overlapping'])])
    geometry=dict(database_sha256='frozen',pins={t['instance']+'/'+t['pin']:[dict(layer='Metal1',bbox_dbu=inst[t['instance']]['bbox_dbu'])]
        for v in nets.values() for t in v['terminals']})
    measurements={c:{} for c in ['fast','slow']}
    for c in measurements:
        for r in records:
            caps=[sum(lib.capacitance(c,inst[p.split('/')[0]]['cell'],p.split('/')[1])[i] for p in r['consumers']) for i in (0,1)]
            measurements[c][r['net']]=dict(pin_cap_pf=caps,wire_cap_pf=[.05,.05],loads=len(r['consumers']),drivers=1,
                capacitance=dict(actual=caps[1]+.05,limit=.3))
    policy=dict(schema=1,source_database_sha256='frozen',contract_sha256='contract',
        transforms=['resize_buffer','exchange_leaf_consumers','add_macro_receiver'],
        resize_cells=['sg13cmos5l_buf_2','sg13cmos5l_buf_4','sg13cmos5l_buf_8'],
        grouping='same_transport_tree_fixed_drivers_equal_count_exchanges',
        placement=dict(resize='same_origin_free_growth',receiver='free_row_near_macro_pin'),
        protected_instances=[],max_exchange_passes=8,boundary='test')
    total=sum((i['bbox'][2]-i['bbox'][0])*(i['bbox'][3]-i['bbox'][1]) for i in inst.values())
    contract=dict(reserve_fraction=.2,area_reference=dict(area_um2=total),max_added_area_fraction=.3,
        timing_floors_ns={'fast':dict(setup=.4,hold=.1),'slow':dict(setup=.2,hold=.2)})
    return context,coverage,geometry,measurements,lib,policy,contract


class Organization(unittest.TestCase):
    def test_reconstruction_counts_shared_tree_once_and_preserves_all_leaves(self):
        c,v,g,*_=fixture();m=reconstruct(c,v,g)
        self.assertEqual(m['branch_count'],3);self.assertEqual(m['buffer_count'],2)
        self.assertEqual(m['transport_area_um2'],8)
        self.assertEqual(m['transport_count'],2);self.assertEqual(m['delay_count'],0)
        self.assertEqual(m['trees'][0]['leaves'],['u/A','v/A','x/A','y/A'])
        self.assertEqual(m['trees'][0]['families'],['first','overlapping'])

    def test_missing_branch_duplicate_tree_or_changed_endpoint_is_rejected(self):
        for change in [lambda v:v['components'][0]['nets'].remove('left'),
                       lambda v:v['components'].append(deepcopy(v['components'][0])),
                       lambda v:v['connections'][0]['consumers'].pop()]:
            c,v,g,*_=fixture();change(v)
            with self.assertRaises(ValueError):reconstruct(c,v,g)

    def test_wrong_checkpoint_and_buffer_cycle_are_rejected(self):
        c,v,g,*_=fixture();g['database_sha256']='other'
        with self.assertRaises(ValueError):reconstruct(c,v,g)
        c,v,g,*_=fixture();v['components'][0]['root']='left'
        with self.assertRaises(ValueError):reconstruct(c,v,g)

    def test_library_ranges_bus_bounds_units_and_identity(self):
        lib=fixture()[4]
        self.assertEqual(lib.capacitance('fast','leaf','A'),[.009,.011])
        self.assertEqual(lib.capacitance('fast','memory','A_DIN[3]'),[.004,.004])
        with self.assertRaises(ValueError):lib.capacitance('fast','memory','A_DIN[4]')
        with self.assertRaises(ValueError):Library({'fast':['capacitive_load_unit (1,ff);']})
        text=lib.texts['fast'][0].replace('function : "A"','function : "!A"')
        with self.assertRaises(ValueError):Library({'fast':[text]}).buffer('fast','sg13cmos5l_buf_1')

    def test_independent_pin_reconciliation_detects_changed_load(self):
        args=fixture();p=Planner(*args)
        self.assertEqual(p.reconcile_pins({'root','left','right'}),6)
        args[3]['slow']['left']['pin_cap_pf'][1]=.05
        with self.assertRaisesRegex(ValueError,'saved STA'):p.reconcile_pins({'left'})

    def test_pin_loads_sum_with_common_rise_or_fall_before_taking_the_maximum(self):
        args=fixture();p=Planner(*args)
        p.library.caps['fast','leaf','A']=dict(rise=[.009,.02],fall=[.008,.01])
        p.context['instances']['y']['cell']='opposite'
        p.library.caps['fast','opposite','A']=dict(rise=[.008,.01],fall=[.009,.02])
        self.assertEqual(p.pin_caps('fast',['x/A','y/A']),[.017,.03])
        self.assertNotEqual(p.pin_caps('fast',['x/A','y/A'])[1],.04)

    def test_resize_counts_added_load_on_shared_parent_once(self):
        p=Planner(*fixture());r=p.resize('root',['left','right'],'sg13cmos5l_buf_2')
        self.assertEqual(r['added_area_um2'],4)
        self.assertAlmostEqual(r['upstream']['fast']['root']['added_pin_cap_pf'],.006)
        self.assertEqual(len(r['upstream']['fast']),1)
        self.assertFalse(r['execution_admitted']);self.assertFalse(r['timing_qualified'])

    def test_resize_rejects_protected_driver_and_reports_occupied_growth(self):
        args=fixture();args[5]['protected_instances']=['a'];p=Planner(*args)
        with self.assertRaisesRegex(ValueError,'protected'):p.resize('root',['left'],'sg13cmos5l_buf_2')
        args=fixture();args[0]['instances']['obstacle']=dict(cell='leaf',macro=False,bbox=[2,4,4,6],bbox_dbu=[2,4,4,6])
        r=Planner(*args).resize('root',['left'],'sg13cmos5l_buf_2')
        self.assertFalse(r['footprint_screen_pass'])

    def test_exchange_improves_geometry_without_dropping_or_relabeling_loads(self):
        p=Planner(*fixture());r=p.exchange('root',['left','right'])
        self.assertEqual(r['improved_targets'],['left','right']);self.assertEqual(r['added_area_um2'],0)
        self.assertTrue(all(v['after_span_um']<v['before_span_um'] for v in r['geometry'].values()))
        self.assertEqual(sum(len(e['after']) for e in r['edits']),4)
        self.assertFalse(r['electrical_qualified'])

    def test_exchange_cannot_drop_duplicate_cross_tree_or_touch_state(self):
        for mutate in [lambda e:e[0]['after'].__setitem__(0,e[0]['after'][1]),
                       lambda e:e[0].update(net='outside'),lambda e:e[0]['after'].pop()]:
            p=Planner(*fixture());r=p.exchange('root',['left','right']);mutate(r['edits'])
            with self.assertRaises(ValueError):validate_exchanges(p.context,p.rows,p.model['trees'][0],r['edits'],[])
        p=Planner(*fixture());r=p.exchange('root',['left','right'])
        p.context['instances']['x']['cell']=FF
        with self.assertRaisesRegex(ValueError,'state'):validate_exchanges(p.context,p.rows,p.model['trees'][0],r['edits'],[])

    def test_forged_tree_membership_cannot_authorize_a_different_source(self):
        p=Planner(*fixture());r=p.exchange('root',['left','right'])
        p.context['nets']['root']['terminals']=[t for t in p.context['nets']['root']['terminals'] if t['instance']!='b']
        p.context['nets']['other_root']=dict(type='SIGNAL',ports=[],terminals=[
            dict(instance='other',pin='Q',direction='OUTPUT'),dict(instance='b',pin='A',direction='INPUT')])
        p.context['instances']['other']=dict(cell=FF,macro=False)
        with self.assertRaisesRegex(ValueError,'electrical root'):
            validate_exchanges(p.context,p.rows,p.model['trees'][0],r['edits'],[])

    def test_internal_branch_can_regroup_leaves_while_fixed_state_load_stays_put(self):
        args=fixture();c,v,g,m,lib,policy,contract=args
        c['instances']['fixed']=dict(cell=FF,macro=False,bbox=[20,8,22,10],bbox_dbu=[20,8,22,10])
        c['nets']['left']['terminals'].append(dict(instance='fixed',pin='D',direction='INPUT'))
        g['pins']['fixed/D']=[dict(layer='Metal1',bbox_dbu=[20,8,22,10])]
        next(r for r in v['connections'] if r['net']=='left')['consumers'].append('fixed/D')
        next(r for r in v['connections'] if r['net']=='left')['consumers'].sort()
        for corner in m:lib.caps[corner,FF,'D']=dict(rise=[.01,.01],fall=[.01,.01])
        p=Planner(*args);result=p.exchange('root',['left','right'])
        changed=next(e for e in result['edits'] if e['net']=='left')
        self.assertIn('fixed/D',changed['after']);self.assertTrue(result['swaps'])

    def test_missing_corner_bad_policy_or_inconsistent_area_fails(self):
        for change in [lambda a:a[3].pop('slow'),lambda a:a[5].update(grouping='arbitrary'),
                       lambda a:a[5].update(max_exchange_passes=100),
                       lambda a:a[0]['instances']['size1']['bbox_dbu'].__setitem__(2,19)]:
            args=fixture();change(args)
            with self.assertRaises(ValueError):Planner(*args)

    def test_portfolio_does_not_reset_area_or_claim_physical_qualification(self):
        p=Planner(*fixture());r=p.resize('root',['left','right'],'sg13cmos5l_buf_2');r['id']='resize'
        result=portfolios([r],['left','right'],p.current_area,p.current_area+1)
        self.assertEqual(len(result),1);self.assertFalse(result[0]['area_screen_pass'])
        self.assertFalse(result[0]['execution_admitted'])
        with self.assertRaisesRegex(ValueError,'coverage'):portfolios([r],['left'],p.current_area,p.area_limit)

    def test_independent_readback_checks_identity_and_does_not_edit_its_source(self):
        p=Planner(*fixture());r=p.exchange('root',['left','right']);module=dict(ports={},cells={})
        for wire,net in enumerate(p.context['nets'].values(),10):
            for terminal in net['terminals']:
                name=terminal['instance'];pin=terminal['pin']
                cell=module['cells'].setdefault(name,dict(type=p.context['instances'][name]['cell'],
                    connections={},port_directions={}))
                cell['connections'][pin]=[wire];cell['port_directions'][pin]=terminal['direction'].lower()
        original=deepcopy(module)
        result=screen_exchange_identity(module,r['edits'])
        self.assertTrue(result['whole_circuit_buffer_contracted_identity'])
        self.assertEqual(result['rewired_scalar_inputs'],4);self.assertEqual(module,original)
        self.assertFalse(result['independent_new_physical_readback'])
        module['ports']['other']=dict(direction='input',bits=[99])
        module['cells']['b']['connections']['A']=[99]
        with self.assertRaisesRegex(ValueError,'functional source'):screen_exchange_identity(module,r['edits'])
        bad=deepcopy(original);bad['cells']['x']['connections']['A']=[10]
        with self.assertRaisesRegex(ValueError,'saved readback'):screen_exchange_identity(bad,r['edits'])

    def test_receiver_costs_both_its_source_load_and_its_new_branch(self):
        args=fixture();c,v,g,m,lib,policy,contract=args
        c['instances']['memory']=dict(cell='memory',macro=True,bbox=[50,12,52,14],bbox_dbu=[50,12,52,14])
        c['nets']['left']['terminals'].append(dict(instance='memory',pin='A_DIN[0]',direction='INPUT'))
        g['pins']['memory/A_DIN[0]']=[dict(layer='Metal4',bbox_dbu=[50,12,52,14])]
        next(r for r in v['connections'] if r['net']=='left')['consumers'].append('memory/A_DIN[0]')
        next(r for r in v['connections'] if r['net']=='left')['consumers'].sort()
        p=Planner(*args);before=deepcopy(c)
        result=p.receiver('root','left','sg13cmos5l_buf_2')
        self.assertEqual(result['added_area_um2'],6);self.assertEqual(c,before)
        self.assertAlmostEqual(result['receiver_budgets']['fast']['source_total_with_saved_wire_pf'],.079)
        self.assertAlmostEqual(result['receiver_budgets']['fast']['new_branch_wire_budget_pf'],.476)
        self.assertFalse(result['placement_screen'][0]['legal_placement_qualified'])

    def test_individually_free_candidate_footprints_can_collide_as_a_portfolio(self):
        p=Planner(*fixture());first=p.resize('root',['left'],'sg13cmos5l_buf_2');first['id']='first'
        second=deepcopy(first);second.update(root='other',targets=['other_leaf'],id='second')
        result=portfolios([first,second],['left','other_leaf'],p.current_area,p.area_limit)
        self.assertTrue(result[0]['area_screen_pass']);self.assertFalse(result[0]['combined_footprints_disjoint'])

    def test_wire_pressure_screen_rejects_an_insufficient_geometric_gain(self):
        args=fixture();args[3]['fast']['left']['wire_cap_pf']=[.6,.6]
        p=Planner(*args)
        first=p.exchange('root',['left'],objective='worst_wire_pressure',max_passes=1)
        self.assertTrue(first['improved_targets'])
        self.assertFalse(mechanism_screen(first,p.measurements,.2)['pass_conditional_screen'])
        second=p.exchange('root',['left'],objective='worst_wire_pressure',max_passes=4)
        self.assertTrue(mechanism_screen(second,p.measurements,.2)['pass_conditional_screen'])
        self.assertFalse(second['wire_span_scenario']['left']['physical_prediction'])
        with self.assertRaises(ValueError):p.exchange('root',['left'],objective='unknown')
        with self.assertRaises(ValueError):p.exchange('root',['left'],max_passes=33)

    def test_bounded_refinement_rejects_protected_or_expanded_authority(self):
        c,_,_,_,_,policy,_=fixture()
        r=dict(schema=1,source_database_sha256='frozen',base_policy_sha256='base',boundary='screen',
            relocation=dict(instance='a',cell='sg13cmos5l_buf_2',max_displacement_sites=5,row='same',orientation='same'),
            exchange=dict(objective='worst_wire_pressure',max_passes=16))
        validate_refinement(r,policy,c)
        for change in [lambda x:x['relocation'].update(row='any'),lambda x:x['relocation'].update(max_displacement_sites=21),
                       lambda x:x['exchange'].update(max_passes=0),lambda x:x.update(source_database_sha256='wrong')]:
            bad=deepcopy(r);change(bad)
            with self.assertRaises(ValueError):validate_refinement(bad,policy,c)
        policy['protected_instances']=['a']
        with self.assertRaises(ValueError):validate_refinement(r,policy,c)

    def test_same_row_move_checks_both_incident_nets_and_saved_pin_geometry(self):
        args=fixture();c,v,g,_,_,_,_=args
        c['instances']['a']['orientation']='R0'
        c['instances']['obstacle']=dict(cell='leaf',macro=False,bbox=[2,4,4,6],bbox_dbu=[2,4,4,6])
        for row in v['connections']:row['distribution_root']='root'
        lef='SITE CoreSite\n SIZE 1 BY 2 ;\nEND CoreSite\n'
        for size,width in [(1,2),(2,3)]:
            name='sg13cmos5l_buf_'+str(size)
            lef+=f'MACRO {name}\n ORIGIN 0 0 ;\n SIZE {width} BY 2 ;\n SITE CoreSite ;\n'
            for pin in ['A','X']:lef+=f' PIN {pin}\n PORT\n LAYER Metal1 ;\n RECT 0 0 {width} 2 ;\n END\n END {pin}\n'
            lef+=f'END {name}\n'
        masters=BufferGeometry(lef,['sg13cmos5l_buf_1','sg13cmos5l_buf_2'],1)
        p=Planner(*args);original=deepcopy(c)
        rule=dict(instance='a',cell='sg13cmos5l_buf_2',max_displacement_sites=5,row='same',orientation='same')
        result=p.relocate(rule,masters)
        self.assertTrue(result);self.assertEqual(c,original)
        for candidate in result:
            self.assertEqual(set(candidate['incident_geometry']),{'root','left'})
            self.assertEqual(candidate['edits'][0]['footprint_dbu'][1],4)
            self.assertLessEqual(candidate['displacement_um'],5)
            self.assertFalse(candidate['execution_admitted'])
        p.model['points_um']['a/A'][0]+=.1
        with self.assertRaisesRegex(ValueError,'saved geometry'):p.relocate(rule,masters)
        with self.assertRaises(ValueError):BufferGeometry(lef.replace('RECT 0 0','RECT -1 0'),['sg13cmos5l_buf_1'],1)
        with self.assertRaises(ValueError):masters.points('sg13cmos5l_buf_1',[0,0,2,2],'R90')


if __name__=='__main__':unittest.main()
