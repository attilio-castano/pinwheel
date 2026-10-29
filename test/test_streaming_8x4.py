"""Scoped8x4 admission regressions: oldgeometry and weakenedcontracts must reject."""
import copy
import json
from pathlib import Path
import sys
import shutil
import subprocess
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
import streaming_8x4_geometry as G
import streaming_8x4_prepare as P
import streaming_8x4_run as R

OFFICIAL = G.ROOT/'build/campaigns/8x4-20261022-01/intake/tt_block_8x4_pgvdd.def'


def synthetic_template():
    centers = {'clk':187200,'ena':191040,'rst_n':183360}
    for prefix,first in [('ui_in',179520),('uio_in',148800),('uio_oe',56640),('uio_out',87360),('uo_out',118080)]:
        centers.update({f'{prefix}[{index}]':first-3840*index for index in range(8)})
    lines = ['UNITS DISTANCE MICRONS 1000 ;','DIEAREA ( 0 0 ) ( 1724160 710640 ) ;']
    lines += [f'ROW ROW_{index} CoreSite 2880 {3780+index*3780} {"N" if index%2==0 else "FS"} DO 3580 BY 1 STEP 480 0 ;' for index in range(186)]
    lines += ['PINS 43 ;']
    for name,center in sorted(centers.items()):
        direction = 'INPUT' if name in {'clk','ena','rst_n'} or name.startswith(('ui_in[','uio_in[')) else 'OUTPUT'
        lines.append(f'- {name} + NET {name} + DIRECTION {direction} + USE SIGNAL\n  + PORT\n    + LAYER Metal4 ( -150 -1000 ) ( 150 0 )\n    + PLACED ( {center} 710640 ) N ;')
    return '\n'.join(lines)+'\nEND PINS\n'


class Geometry(unittest.TestCase):
    def test_official_shape_fixture_and_power_grid(self):
        pins = G.template_pins(synthetic_template())
        self.assertEqual(set(pins),G.public_names())
        rows = G.Grid().rectangles()
        self.assertEqual(len(rows),70)
        self.assertEqual(min(G.clearance(row['bounds_dbu'],pin) for row in rows for pin in pins.values()),680)
        self.assertEqual(G.validate_power_ports(rows)['full_height_power_stripes'],70)
        grid=G.Grid()
        self.assertGreaterEqual(grid.first_center+len(rows)//2*grid.pitch-grid.width//2,G.DIE[2])
        self.assertLessEqual(rows[-1]['bounds_dbu'][2],G.CORE[2])

    @unittest.skipUnless(OFFICIAL.is_file(),'Campaign officialDEF intake absent; sourcefixture controls remain separate')
    def test_actual_hash_bound_official_allocation(self):
        admitted=G.admit(OFFICIAL)
        self.assertEqual(admitted['template_sha256'],'64b52f2150f699edc7fb500c2f486a51eca66fd91d3efb7347200bd2cf83a2ee')
        self.assertEqual(len(admitted['public_pins_dbu']),43)
        self.assertEqual(len(admitted['expected_power_ports']),70)
        self.assertEqual(admitted['minimum_public_clearance_dbu'],680)

    def test_old_die_and_changed_pin_contract_reject(self):
        original = synthetic_template()
        for changed in (original.replace('1724160','1289280'),original.replace('MICRONS 1000','MICRONS 2000'),
                        original.replace('PINS 43','PINS 42'),original.replace('DO 3580','DO 3579',1),
                        original.replace('clk + NET clk','oops + NET oops'),
                        original.replace('DIRECTION INPUT','DIRECTION OUTPUT',1),
                        original.replace('( -150 -1000 )','( -149 -1000 )',1),
                        original.replace('Metal4','Metal3',1),original.replace('710640 ) N','710639 ) N',1)):
            with self.subTest(changed=changed[:80]),self.assertRaises(ValueError): G.template_pins(changed)

    def test_missing_full_stripe_and_wrong_layer_reject(self):
        rows = G.Grid().rectangles()
        for changed in (rows[:-1],[dict(row,layer='Metal3') for row in rows],
                        [dict(row,bounds_dbu=[row['bounds_dbu'][0],0,row['bounds_dbu'][2],10000]) for row in rows]):
            with self.assertRaises(ValueError): G.validate_power_ports(changed)

    def test_overlapping_grid_reject(self):
        for grid in (G.Grid(width=2099),G.Grid(pair_delta=2200),G.Grid(first_center=1000),G.Grid(public_clearance=200),
                     G.Grid(pitch=50000,first_center=16160)):
            with self.assertRaises(ValueError): grid.rectangles()

    def test_hash_and_manifest_binding_reject(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp);template = root/'official.def';template.write_text(synthetic_template())
            allocation = root/'allocation.json'
            manifest = json.loads(G.ALLOCATION.read_text());manifest['template_sha256']=G.sha(template)
            allocation.write_text(json.dumps(manifest))
            admitted = G.admit(template,allocation)
            self.assertFalse(admitted['physical_acceptance'])
            self.assertFalse(admitted['native_geometry_validated'])
            self.assertIn('set streaming8_die {0 0 1724160 710640}',G.allocation_tcl(admitted))
            template.write_text(template.read_text()+'\n')
            with self.assertRaises(ValueError): G.admit(template,allocation)
            template.write_text(synthetic_template())
            for key,value in [('tiles','6x4'),('die_dbu',[0,0,1289280,710640]),('support_commit','latest')]:
                changed = dict(manifest);changed[key]=value;allocation.write_text(json.dumps(changed))
                with self.subTest(key=key),self.assertRaises(ValueError): G.admit(template,allocation)

    def test_colliding_official_pin_grid_rejects(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp);template=root/'official.def';template.write_text(synthetic_template())
            allocation=root/'allocation.json';manifest=json.loads(G.ALLOCATION.read_text());manifest['template_sha256']=G.sha(template)
            allocation.write_text(json.dumps(manifest))
            with self.assertRaises(ValueError): G.admit(template,allocation,G.Grid(first_center=187200))

    @unittest.skipUnless(shutil.which('tclsh'),'HOST Tcl interpreter unavailable')
    def test_actual_tcl_guard_validates_die_core_and_pin_contract(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp)
            template=root/'official.def';template.write_text(synthetic_template())
            allocation=root/'allocation.json';manifest=json.loads(G.ALLOCATION.read_text());manifest['template_sha256']=G.sha(template)
            allocation.write_text(json.dumps(manifest));admission=G.admit(template,allocation)
            (root/'allocation.tcl').write_text(G.allocation_tcl(admission))
            shutil.copyfile(G.ROOT/'physical/streaming_8x4/pdn.tcl',root/'pdn.tcl')
            common=root/'openroad/common';common.mkdir(parents=True)
            (common/'set_global_connections.tcl').write_text('proc set_global_connections {} {}\n')
            lines=['namespace eval ord {}','proc ord::get_db_block {} {return block}',
                'proc die {method} {dict get {xMin 0 yMin 0 xMax 1724160 yMax 710640} $method}',
                'proc core {method} {dict get {xMin 2880 yMin 3780 xMax 1721280 yMax 706860} $method}']
            names=[]
            for index,name in enumerate(sorted(G.public_names())):
                term='term'+str(index);names.append(term)
                direction='INPUT' if name in {'clk','ena','rst_n'} or name.startswith(('ui_in[','uio_in[')) else 'OUTPUT'
                lines.append('proc '+term+' {method} {switch -- $method {getSigType {return SIGNAL} getName {return {'+name+
                    '}} getIoType {return '+direction+'} getBPins {return {}} default {error "Unknown term API"}}}')
            lines.append('proc block {method} {switch -- $method {getDbUnitsPerMicron {return 1000} getDieArea {return die} '+
                'getCoreArea {return core} getBTerms {return {'+' '.join(names)+'}} default {error "Unknown block API"}}}')
            for command in ('set_voltage_domain','define_pdn_grid','add_pdn_stripe','add_pdn_connect'):
                lines.append('proc '+command+' {args} {}')
            lines += ['set ::env(PDN_VWIDTH) 2.1','set ::env(PDN_VPITCH) 50','set ::env(PDN_VOFFSET) 10',
                'set ::env(PDN_VSPACING) 3.52','set ::env(PDN_HWIDTH) 2.1','set ::env(PDN_HPITCH) 50',
                'set ::env(PDN_HOFFSET) 10','set ::env(PDN_HSPACING) 3.52','set ::env(PDN_RAIL_WIDTH) 0.48',
                'set ::env(VDD_NET) VPWR','set ::env(GND_NET) VGND','set ::env(SCRIPTS_DIR) {'+str(root)+'}',
                'source {'+str(root/'pdn.tcl')+'}','puts GUARD_COMPLETED']
            original='\n'.join(lines)+'\n'
            for expected,text in [(True,original),(False,original.replace('xMax 1724160','xMax 1289280')),
                                  (False,original.replace('xMax 1721280','xMax 1721281')),
                                  (False,original.replace('set ::env(PDN_VWIDTH) 2.1','set ::env(PDN_VWIDTH) 2.0')),
                                  (False,original.replace('getIoType {return INPUT}','getIoType {return OUTPUT}',1))]:
                script=root/'control.tcl';script.write_text(text)
                result=subprocess.run([shutil.which('tclsh'),str(script)],capture_output=True,text=True,timeout=5)
                self.assertEqual(result.returncode==0,expected,result.stderr)
                self.assertEqual('GUARD_COMPLETED' in result.stdout,expected)


class Recipe(unittest.TestCase):
    def test_only_footprint_template_flow_change(self):
        config = json.loads((G.ROOT/'physical/streaming-tt-candidate.json').read_text())
        geometry=dict(allocation_sha256='a'*64,template_sha256='b'*64)
        after,ledger=P.recipe(config,geometry)
        self.assertEqual(set(ledger['changes']),{'DIE_AREA','FP_DEF_TEMPLATE','meta'})
        self.assertEqual(after['DIE_AREA'],[0,0,1724.16,710.64])
        self.assertEqual(after['CLOCK_PERIOD'],20)
        self.assertEqual(after['PL_TARGET_DENSITY_PCT'],85)
        self.assertEqual(after['RT_MAX_LAYER'],'Metal4')
        self.assertFalse(ledger['physical_acceptance'])
        self.assertEqual(config,json.loads((G.ROOT/'physical/streaming-tt-candidate.json').read_text()))

    def test_wrong_behavior_or_baseline_rejects(self):
        config = json.loads((G.ROOT/'physical/streaming-tt-candidate.json').read_text())
        geometry=dict(allocation_sha256='a'*64,template_sha256='b'*64)
        for key,value in [('CLOCK_PERIOD',30),('PL_TARGET_DENSITY_PCT',65),('DESIGN_NAME','smaller'),('DIE_AREA',[0,0,1724.16,710.64])]:
            changed=copy.deepcopy(config);changed[key]=value
            with self.subTest(key=key),self.assertRaises(ValueError): P.recipe(changed,geometry)

    def test_unrecognized_historical_receipt_rejects_before_any_copy(self):
        with tempfile.TemporaryDirectory() as temp:
            path=Path(temp)/'inputs.json';path.write_text('{}')
            with self.assertRaisesRegex(ValueError,'exact retained balanced'): P.validate_baseline(path)


class Runner(unittest.TestCase):
    def test_nonfinite_native_observations_are_typed_not_coerced(self):
        encoded=R.receipt_value(dict(positive=float('inf'),negative=float('-inf'),nan=float('nan'),finite=1.25,
            nested=[float('inf'),'Infinity',None,False]))
        self.assertEqual(encoded['positive'],dict(type='pinwheel.native-nonfinite-float.v1',value='+Infinity',qualified=False))
        self.assertEqual(encoded['negative']['value'],'-Infinity')
        self.assertEqual(encoded['nan']['value'],'NaN')
        self.assertEqual(encoded['finite'],1.25)
        self.assertEqual(encoded['nested'][1:],['Infinity',None,False])
        json.dumps(encoded,allow_nan=False)

    def test_actual_captured_native_infinity_state_closes_strict_receipt(self):
        fixture=G.ROOT/'test/fixtures/streaming_8x4/probe01-staprepnr-state.json'
        expected='166a2f0e0e3a013fcd57c080f0cf6fd0307554d8c34c8e5143dc3c6acfbed7e9'
        self.assertEqual(G.sha(fixture),expected)
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp);stage=root/'flow/04-openroad-staprepnr';stage.mkdir(parents=True)
            path=stage/'state_out.json';shutil.copyfile(fixture,path)
            rows=R.states(root,root/'prepared',root/'pdk')
            self.assertEqual(len(rows),1)
            self.assertEqual(rows[0]['state_sha256'],expected)
            value=rows[0]['metrics']['timing__setup_r2r__ws']
            self.assertEqual(value['value'],'+Infinity')
            self.assertFalse(value['qualified'])
            R.write(root/'receipt.json',dict(states=rows,qualified=False,physical_acceptance=False))
            self.assertEqual(G.sha(path),expected)
            self.assertIsInstance(json.loads((root/'receipt.json').read_text())['states'][0]['metrics']['timing__setup_r2r__ws'],dict)

    def test_full_tail_cannot_skip_or_reorder_checks(self):
        prefix=['OpenROAD.GeneratePDN','Odb.RemovePDNObstructions','Odb.ApplyDEFTemplate',
                'OpenROAD.GlobalPlacement','OpenROAD.STAMidPNR-3']
        ids=prefix+list(R.TAIL)
        classic=['Yosys.Synthesis']+ids
        self.assertTrue(R.validate_order(classic,ids,R.STOPS['full'])['ordinary_full_tail_preserved'])
        for broken in (ids[:-1],ids[:len(prefix)]+list(R.TAIL[1:]),ids[:len(prefix)]+list(reversed(R.TAIL))):
            with self.assertRaises(ValueError):R.validate_order(classic,broken,R.STOPS['full'])
        with self.assertRaises(ValueError):R.validate_order(classic,ids,'OpenROAD.DetailedRouting')

    def test_container_is_bounded_offline_and_input_pdk_readonly(self):
        command=R.container_command(Path('/prepared'),Path('/output'),Path('/pdk'),'sha256:'+'a'*64,
            'pinwheel-test-8x4','12345678-1234-1234-1234-123456789abc','full')
        self.assertIn('type=bind,source=/prepared/inputs,target=/work/inputs,readonly',command)
        self.assertIn('type=bind,source=/pdk,target=/work/pdk,readonly',command)
        for key,value in [('--network','none'),('--cpus','4'),('--memory','6g'),('--memory-swap','6g'),('--pull','never')]:
            self.assertEqual(command[command.index(key)+1],value)
        with self.assertRaises(ValueError):R.container_command(Path('/p'),Path('/o'),Path('/pdk'),'sha256:'+'a'*64,
            'unowned-container','12345678-1234-1234-1234-123456789abc','full')


if __name__ == '__main__': unittest.main()
