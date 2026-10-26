"""Small geometric PG controls; no Docker, OpenROAD or electrical solve."""
import copy
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
from types import SimpleNamespace as Obj
import unittest
from unittest.mock import patch

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
import streaming_8x4_power_grid as G


def box(via=False,level=1,bounds=(0,0,10,10)):
    layer=Obj(getName=lambda:'Metal'+str(level),getRoutingLevel=lambda:level)
    return Obj(isVia=lambda:via,getTechLayer=lambda:layer,
        xMin=lambda:bounds[0],yMin=lambda:bounds[1],xMax=lambda:bounds[2],yMax=lambda:bounds[3])


def fixture():
    """Two independently named rails, one cell, and two BPins per rail.

    The second BPin deliberately lets a control expose PSM's existential placed
    BPin check: requiring one placed BPin must not waive another unplaced BPin.
    """
    inventory=dict(schema='pinwheel.streaming-tt-odb-inventory.v1',top='example',power_connectivity_signed_off=False,
        masters={'cell_master':{}},physical_only_instances={},
        nets={'SUPPLY_X':dict(signal_type='POWER'),'RETURN_Y':dict(signal_type='GROUND')},
        instances={'cell':dict(master='cell_master',terminals={
            'VDD':dict(signal_type='POWER',net='SUPPLY_X'),'VSS':dict(signal_type='GROUND',net='RETURN_Y')})},
        power_bterms={'PAD_P':dict(signal_type='POWER',net='SUPPLY_X'),
            'PAD_N':dict(signal_type='GROUND',net='RETURN_Y')})
    state=dict(placed=True,pin_status='PLACED',empty_mpin=False,via_present=True)
    inst=Obj(getName=lambda:'cell',getMaster=lambda:Obj(getName=lambda:'cell_master'),isPlaced=lambda:state['placed'])
    nets=[]
    for name,kind,pin,pad in [('SUPPLY_X','POWER','VDD','PAD_P'),('RETURN_Y','GROUND','VSS','PAD_N')]:
        net=Obj(getName=lambda name=name:name,getSigType=lambda kind=kind:kind)
        term=Obj(getInst=lambda:inst,getMTerm=lambda pin=pin,kind=kind:Obj(getName=lambda:pin,getSigType=lambda:kind,
            getMPins=lambda:[Obj(getGeometry=lambda:[] if state['empty_mpin'] else [box()])]),
            getNet=lambda net=net:net,getBBox=lambda:box())
        bterm=Obj(getName=lambda pad=pad:pad,getSigType=lambda kind=kind:kind,getBPins=lambda:[
            Obj(getPlacementStatus=lambda:'PLACED',getBoxes=lambda:[box()]),
            Obj(getPlacementStatus=lambda:state['pin_status'],getBoxes=lambda:[box()])])
        net.getITerms=lambda term=term:[term];net.getBTerms=lambda bterm=bterm:[bterm]
        net.getSWires=lambda:[Obj(getWires=lambda:[box()]+([box(via=True)] if state['via_present'] else []))]
        nets.append(net)
    return inventory,Obj(getNets=lambda:nets),state


def log(rails):
    return ''.join('PINWHEEL_PG_BEGIN '+name+'\nShapes on Metal1: 3\nTotal shapes: 3\n'
        'Nodes on Metal1: 7\nTotal nodes: 7\nTotal connections: 8\n'
        '[INFO PSM-0040] All shapes on net '+name+' are connected.\nPINWHEEL_PG_END '+name+'\n' for name in rails)


class PowerGrid(unittest.TestCase):
    def test_actual_names_and_complete_geometric_census(self):
        inventory,block,_=fixture();expected=G.expected_rails(inventory)
        self.assertEqual(set(expected),{'SUPPLY_X','RETURN_Y'})
        census=G.census(block,inventory);G.validate_census(census,inventory)
        self.assertEqual(census['SUPPLY_X']['bpin_count'],2)
        self.assertEqual(census['SUPPLY_X']['swire_vias'],1)
        for field in ('skipped_iterms','skipped_bpins'):self.assertEqual(census['RETURN_Y'][field],0)

    def test_all_terminal_skip_modes_fail_instead_of_existence_waiver(self):
        for key,bad in [('placed',False),('pin_status','UNPLACED'),('empty_mpin',True),('via_present',False)]:
            with self.subTest(key=key):
                inventory,block,state=fixture();state[key]=bad
                with self.assertRaises(ValueError):G.census(block,inventory)
        for shape in [box(via=True),box(level=0),box(bounds=(0,0,0,5))]:
            with self.assertRaises(ValueError):G.pin_shapes([shape])

    def test_missing_disconnected_and_skipped_census_reject(self):
        inventory,block,_=fixture();census=G.census(block,inventory)
        for change in ('missing','skipped','empty','unplaced'):
            value=copy.deepcopy(census)
            if change=='missing':value['SUPPLY_X']['iterms']=[]
            elif change=='skipped':value['SUPPLY_X']['skipped_iterms']=1
            elif change=='empty':value['SUPPLY_X']['iterms'][0]['mpins']=[[]]
            else:value['SUPPLY_X']['bterms'][0]['bpins'][1]['placement_status']='NONE'
            with self.assertRaises(ValueError):G.validate_census(value,inventory)
        inventory['instances']['cell']['terminals']['VDD']['net']=None
        with self.assertRaises(ValueError):G.expected_rails(inventory)

    def test_exact_success_error_and_nonvacuous_graph_messages(self):
        inventory,_,_=fixture();rails=G.expected_rails(inventory);text=log(rails)
        self.assertEqual(G.parse_log(text,rails)['SUPPLY_X'],dict(shapes=3,nodes=7,connections=8))
        for bad in [text.replace('Total nodes: 7','Total nodes: 0',1),
            text.replace('[INFO PSM-0040] All shapes on net SUPPLY_X are connected.',''),
            text.replace('Total connections: 8','',1),text+'[WARNING PSM-0001] skipped terminal\n',
            text+'[ERROR PSM-0069] disconnected\n',text+log({'SUPPLY_X':{}})]:
            with self.assertRaises(ValueError):G.parse_log(bad,rails)

    def test_every_error_file_and_exact_command_are_required(self):
        inventory,block,_=fixture();rails=G.expected_rails(inventory)
        with tempfile.TemporaryDirectory() as temporary:
            output=Path(temporary);inputs=output/'inputs';inputs.mkdir()
            G.P.write(inputs/'inventory.json',inventory);G.P.write(inputs/'reference.json',{})
            G.P.write(inputs/'request.json',dict(rails=rails))
            checks=[]
            for index,name in enumerate(rails):
                filename='rail-'+str(index)+'-errors.rpt';(output/filename).write_bytes(b'')
                checks.append(dict(net=name,argv=['check_power_grid','-net',name,'-error_file','/work/pg/'+filename],
                    catch_status=0,result='1',error_file=filename,error_sha256=G.sha(output/filename),error_bytes=0,
                    floorplanning=False,dont_require_terminals=False))
            value=dict(schema='pinwheel.streaming-8x4-power-grid-native.v1',completed=True,source_odb_unchanged=True,
                canonical_inventory_rederived=True,geometric_open_path_connectivity=True,shorts_checked=False,
                ir_drop_qualified=False,physical_acceptance=False,qualified=False,openroad_source_commit=G.COMMIT,
                openroad_version=G.COMMIT,openroad_git_describe='',rails=G.census(block,inventory),checks=checks,
                inventory_totals=G.inventory_totals(inventory),
                input_sha256={'/work/target.odb':'a'*64,'/work/pg/inputs/inventory.json':G.sha(inputs/'inventory.json'),
                    '/work/pg/inputs/reference.json':G.sha(inputs/'reference.json')})
            (output/'openroad.log').write_text(log(rails));(output/'launch.py').write_text(G.LAUNCHER)
            G.P.write(output/'leaf.json',dict(schema='pinwheel.streaming-8x4-power-grid-leaf.v1',completed=True,
                exit_code=0,timeout_seconds=180,openroad_executable='/native/openroad',
                argv=['/native/openroad','-no_init','-exit','-python','/work/pg/launch.py'],log_sha256=G.sha(output/'openroad.log')))
            G.P.write(output/'native.json',value);packet=dict(source_odb=dict(sha256='a'*64))
            G.native_result(output,packet)
            for field,bad in [('dont_require_terminals',True),('floorplanning',True),('result','0')]:
                changed=copy.deepcopy(value);changed['checks'][0][field]=bad;G.P.write(output/'native.json',changed)
                with self.assertRaises(ValueError):G.native_result(output,packet)
            leaf=G.P.read(output/'leaf.json');leaf['timeout_seconds']=181;G.P.write(output/'leaf.json',leaf)
            G.P.write(output/'native.json',value)
            with self.assertRaises(ValueError):G.native_result(output,packet)
            leaf['timeout_seconds']=180;G.P.write(output/'leaf.json',leaf)
            G.P.write(output/'native.json',value);(output/'rail-0-errors.rpt').write_text('violation')
            with self.assertRaises(ValueError):G.native_result(output,packet)

    def test_leaf_timeout_preserves_failure_and_enforces_180_seconds(self):
        with tempfile.TemporaryDirectory() as temporary:
            root=Path(temporary);(root/'launch.py').write_text(G.LAUNCHER)
            def timed_out(command,**kwargs):
                self.assertEqual(kwargs['timeout'],180)
                kwargs['log_path'].write_text('retained timeout observation')
                error=subprocess.TimeoutExpired(command,180);error.process_group_stopped=True
                raise error
            with patch.object(G.shutil,'which',return_value=sys.executable),\
                 patch.object(G.process_group,'run_captured',side_effect=timed_out):
                self.assertEqual(G.native_supervise(root),2)
            value=G.P.read(root/'leaf.json')
            self.assertIs(value['completed'],False);self.assertEqual(value['exit_code'],124)
            self.assertTrue(value['process_group_stopped']);self.assertEqual(value['timeout_seconds'],180)
            self.assertEqual(value['log_sha256'],G.sha(root/'openroad.log'))

    def test_real_pinned_source_intake_reopens_and_rejects_mutation(self):
        source=G.P.ROOT/'build/campaigns/8x4-20261022-01/intake/psm-source-01'
        expected=G.source_evidence(source)
        self.assertEqual(len(expected),10)
        # These controls exercise real audited C++/Tcl bytes rather than a
        # synthetic success receipt mirroring the expected schema.
        with tempfile.TemporaryDirectory() as temporary:
            copied=Path(temporary)/'psm';shutil.copytree(source,copied)
            self.assertEqual(G.source_evidence(copied),expected)
            (copied/'foreign').write_text('not in source intake')
            with self.assertRaises(ValueError):G.source_evidence(copied)
            (copied/'foreign').unlink();path=copied/'src/psm/src/ir_solver.cpp';path.write_bytes(path.read_bytes()+b'\n')
            with self.assertRaises(ValueError):G.source_evidence(copied)

    def test_resource_policy_is_fixed_and_receipt_membership_complete(self):
        lock=G.P.read(G.P.ROOT/'tools/physical-toolchain.json')
        runtime=dict(image_id='sha256:5825633bea1f9cbc705ece2de2bc31de6e4ec83d233739205a0f265ef9d92f92',architecture='arm64',os='linux',
            rootfs_diff_ids=lock['container_rootfs_diff_ids'],runtime_config_sha256=lock['container_runtime_config_sha256'])
        packet=dict(source_odb=dict(path='/actual.odb'),runtime=copy.deepcopy(runtime))
        command=G.container_command(Path('/fresh'),packet,runtime,
            '00000000-0000-4000-8000-000000000001','pinwheel-pg-test')
        self.assertIn('--network',command);self.assertIn('none',command)
        self.assertEqual(command[command.index('--memory')+1],'2g')
        self.assertIn('source=/actual.odb,target=/work/target.odb,readonly',' '.join(command))
        self.assertEqual((G.LEAF_SECONDS,G.OUTER_SECONDS),(180,240))
        runtime['image_id']=lock['container_config_digest']
        with self.assertRaises(ValueError):G.container_command(Path('/fresh'),packet,runtime,
            '00000000-0000-4000-8000-000000000001','pinwheel-pg-test')
        runtime['image_id']='sha256:wrong'
        with self.assertRaises(ValueError):G.container_command(Path('/fresh'),packet,runtime,
            '00000000-0000-4000-8000-000000000001','pinwheel-pg-test')
        runtime=copy.deepcopy(packet['runtime']);runtime['rootfs_diff_ids']=[]
        with self.assertRaises(ValueError):G.container_command(Path('/fresh'),packet,runtime,
            '00000000-0000-4000-8000-000000000001','pinwheel-pg-test')
        with tempfile.TemporaryDirectory() as temporary:
            root=Path(temporary);(root/'report.json').write_text('{}');(root/'nested').mkdir()
            (root/'nested/report.json').write_text('must be bound')
            self.assertEqual(set(G.artifacts(root)),{'nested/report.json'})

    def test_unclosed_views_fail_before_runtime_or_native(self):
        with tempfile.TemporaryDirectory() as temporary:
            path=Path(temporary)/'report.json';G.P.write(path,dict(schema='pinwheel.streaming-8x4-final-views-run.v1',completed=False))
            with patch.object(G.V,'inspect_runtime',side_effect=AssertionError('no Native runtime launch')):
                with self.assertRaises(ValueError):G.closed_views(path)

    def test_required_version_and_optional_empty_description_match_actual_capture(self):
        # Exact observed return values, retained under campaign8x4-20261022-01/
        # route-replay-preparation-01/step/{version,describe}-return.txt.
        # Literals keep this control independent of ignored build captures.
        version='dcf36133a369abc8f3c5e5738cd4d82e4903c0e0'
        describe=''
        self.assertEqual(version,G.COMMIT);self.assertEqual(describe,'')
        self.assertEqual(G.revision_identity(version,describe),G.COMMIT)
        self.assertEqual(G.revision_identity('v2.0-g'+G.COMMIT,'g'+G.COMMIT),G.COMMIT)
        for bad_version,bad_describe in [('',G.COMMIT),(G.COMMIT[:8],''),
            ('a'*40,''),(G.COMMIT,'a'*40),(G.COMMIT,'g'+G.COMMIT[:8]),
            (G.COMMIT+'0',''),(G.COMMIT,'0'+G.COMMIT),
            (G.COMMIT+' '+'a'*40,''),(None,'')]:
            with self.subTest(version=bad_version,describe=bad_describe):
                with self.assertRaises(ValueError):G.revision_identity(bad_version,bad_describe)

    def test_both_raw_queries_are_preserved_and_query_failure_is_fatal(self):
        answers={'ord::openroad_version':G.COMMIT,'ord::openroad_git_describe':''}
        calls=[]
        def query(design,command):calls.append(command);return answers[command]
        with patch.object(G,'caught',side_effect=query):
            self.assertEqual(G.observe_revision(object()),dict(openroad_version=G.COMMIT,openroad_git_describe=''))
        self.assertEqual(calls,list(answers))
        with patch.object(G,'caught',side_effect=ValueError('query failed')):
            with self.assertRaises(ValueError):G.observe_revision(object())


if __name__=='__main__':unittest.main()
