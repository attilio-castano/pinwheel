"""Real former-short regression and exact host admission before native CAD."""
from copy import deepcopy
from dataclasses import replace
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import streaming_tt_pdn_geometry as P


def template():
    lines = ['UNITS DISTANCE MICRONS 1000 ;', 'DIEAREA ( 0 0 ) ( 1289280 710640 ) ;', 'PINS 43 ;']
    for name, center in P.official_pin_centers().items():
        direction = 'INPUT' if name in ('clk', 'ena', 'rst_n') or name.startswith(('ui_in[', 'uio_in[')) else 'OUTPUT'
        lines += [f'- {name} + NET {name} + DIRECTION {direction} + USE SIGNAL', '+ PORT',
                  '+ LAYER Metal4 ( -150 -500 ) ( 150 500 )', f'+ PLACED ( {center} 710140 ) N ;']
    return '\n'.join(lines + ['END PINS', ''])


class GeometryTests(unittest.TestCase):
    def setUp(self):
        self.source = (ROOT / 'physical/streaming_tt/pdn.tcl').read_text()
        self.grid = P.Grid.from_tcl(self.source)
        self.pins = P.template_pins(template())

    def test_admitted_pattern_measures_all43_pins_and52_stripes(self):
        result = P.admit_geometry(self.pins, self.grid)
        self.assertEqual(result['minimum_public_clearance_dbu'], 640)
        self.assertEqual(result['expected_power_stripe_count'], 52)
        self.assertFalse(result['native_geometry_validated'])
        self.assertFalse(result['qualified'])

    def test_old_pattern_reproduces_three_actual_ground_shorts(self):
        old = P.Grid(2100, 50000, 12880, 5620, 600)
        shorts = {(name, stripe['net']) for stripe in old.rectangles() for name, rectangle in self.pins.items()
                  if P.clearance(stripe['bounds_dbu'], rectangle) <= 0}
        self.assertEqual(shorts, {('ui_in[3]', 'VGND'), ('uio_out[5]', 'VGND'), ('uo_out[0]', 'VGND')})
        with self.assertRaisesRegex(ValueError, 'clearance'):
            P.admit_geometry(self.pins, old)

    def test_bad_scale_die_direction_name_duplicate_and_geometry_refuse(self):
        original = template()
        mutations = [original.replace('MICRONS 1000', 'MICRONS 2000'),
                     original.replace('1289280 710640', '1289281 710640'),
                     original.replace('NET ena + DIRECTION INPUT', 'NET ena + DIRECTION OUTPUT'),
                     original.replace('- ena + NET ena', '- other + NET other'),
                     original.replace('- ena + NET ena', '- clk + NET clk'),
                     original.replace('( 191040 710140 )', '( 191041 710140 )'),
                     original.replace('+ PORT\n+ LAYER', '+ PORT\n+ LAYER Metal3 ( 0 0 ) ( 1 1 )\n+ LAYER', 1)]
        for text in mutations:
            with self.subTest(text=text[:40]), self.assertRaises(ValueError):
                P.template_pins(text)

    def test_geometry_parameters_cannot_waive_width_spacing_or_boundaries(self):
        for field, value in [('width', 2000), ('width', 2101), ('pitch', 7000), ('pair_delta', 2200),
                             ('first_center', 100), ('public_clearance', 0), ('public_clearance', 239), ('pitch', True)]:
            with self.subTest(field=field, value=value), self.assertRaises(ValueError):
                P.admit_geometry(self.pins, replace(self.grid, **{field: value}))

    def test_abutment_and_subthreshold_gap_fail(self):
        pin = self.pins['ui_in[3]']
        for x in (pin[0] - 2100, pin[0] - 2100 - 239):
            changed = replace(self.grid, first_center=x + 1050)
            with self.subTest(x=x), self.assertRaises(ValueError):
                P.admit_geometry(self.pins, changed)

    def test_actual_ports_require_all_full_height_m4_stripes(self):
        rows = self.grid.rectangles()
        caps = [dict(net=row['net'], layer='Metal4', bounds_dbu=[row['bounds_dbu'][0], 0, row['bounds_dbu'][2], 200])
                for row in rows]
        result = P.validate_power_ports(rows + caps, self.grid)
        self.assertEqual(result['full_height_power_stripes'], 52)
        for change in ('layer', 'width', 'net', 'missing', 'caps_only', 'extension'):
            changed = deepcopy(rows)
            if change == 'layer': changed[0]['layer'] = 'Metal3'
            if change == 'width': changed[0]['bounds_dbu'][2] -= 1
            if change == 'net': changed[0]['net'] = 'VGND'
            if change == 'missing': changed.pop()
            if change == 'caps_only': changed = caps
            if change == 'extension': changed[0]['bounds_dbu'][0] -= 1
            with self.subTest(change=change), self.assertRaises(ValueError):
                P.validate_power_ports(changed, self.grid)

    def test_tcl_metadata_requires_single_literal_parameters(self):
        with self.assertRaises(ValueError): P.Grid.from_tcl(self.source + '\nset streaming_pdn_m4_width_dbu 2100\n')
        with self.assertRaises(ValueError): P.Grid.from_tcl(self.source.replace('set streaming_pdn_m4_width_dbu 2100',
                                                                              'set streaming_pdn_m4_width_dbu $other'))

    @unittest.skipUnless(shutil.which('tclsh'), 'host Tcl unavailable')
    def test_actual_tcl_guard_and_emitted_native_commands_without_cad(self):
        # Exercise the production Tcl against exact object-like host stubs. No
        # OpenROAD process or PDN implementation runs in this test.
        with tempfile.TemporaryDirectory() as temporary:
            base = Path(temporary)
            common = base / 'openroad/common'; common.mkdir(parents=True)
            (common / 'set_global_connections.tcl').write_text('proc set_global_connections {} {}\n')
            script = base / 'check.tcl'
            names = list(P.official_pin_centers())
            prelude = [f'set ::env(SCRIPTS_DIR) {{{base}}}',
                       'foreach {key value} {VDD_NET VPWR GND_NET VGND PDN_RAIL_WIDTH .44 PDN_VPITCH 50 PDN_VOFFSET 10 PDN_VSPACING 3.52 PDN_HWIDTH 2.1 PDN_HPITCH 50 PDN_HOFFSET 10 PDN_HSPACING 3.52 PDN_VWIDTH 2.1} {set ::env($key) $value}',
                       'namespace eval ord {proc get_db_block {} {return block}}',
                       f'set terms {{{" ".join("term" + str(k) for k in range(43))}}}',
                       'proc block {method} {switch $method {getDbUnitsPerMicron {return 1000} getDieArea {return die} getCoreArea {return core} getBTerms {return $::terms} default {error "unsupported block $method"}}}',
                       'proc die {method} {dict get {xMin 0 yMin 0 xMax 1289280 yMax 710640} $method}',
                       'proc core {method} {if {$method ne "xMin"} {error "unsupported core"};return 2880}',
                       'proc layer {method} {if {$method ne "getName"} {error "unsupported layer"};return Metal4}',
                       'proc set_voltage_domain {args} {}',
                       'proc define_pdn_grid {args} {puts [list GRID {*}$args]}',
                       'proc add_pdn_stripe {args} {puts [list STRIPE {*}$args]}',
                       'proc add_pdn_connect {args} {puts [list CONNECT {*}$args]}']
            for k, name in enumerate(names):
                lx, by, rx, ty = self.pins[name]
                direction = 'INPUT' if name in ('clk', 'ena', 'rst_n') or name.startswith(('ui_in[', 'uio_in[')) else 'OUTPUT'
                prelude += [f'proc term{k} {{method}} {{switch $method {{getSigType {{return SIGNAL}} getIoType {{return {direction}}} getName {{return {{{name}}}}} getBPins {{if {{[info exists ::unplaced]}} {{return {{}}}};return pin{k}}} default {{error "unsupported term"}}}}}}',
                            f'proc pin{k} {{method}} {{if {{$method ne "getBoxes"}} {{error "unsupported pin"}};return box{k}}}',
                            f'proc box{k} {{method}} {{if {{$method eq "getTechLayer"}} {{return layer}};dict get {{xMin {lx} yMin {by} xMax {rx} yMax {ty}}} $method}}']
            def execute(source, mutation=''):
                script.write_text('\n'.join(prelude) + '\n' + mutation + '\n' + source)
                return subprocess.run(['tclsh', str(script)], text=True, capture_output=True, timeout=5)
            result = execute(self.source)
            self.assertEqual(result.returncode, 0, result.stderr)
            grid_line = next(line for line in result.stdout.splitlines() if line.startswith('GRID '))
            self.assertIn('-pins Metal4', grid_line)
            stripes = [line for line in result.stdout.splitlines() if line.startswith('STRIPE ')]
            self.assertEqual(len(stripes), 4)
            for layer in ('Metal2', 'Metal3'):
                line = next(line for line in stripes if '-layer ' + layer in line)
                self.assertNotIn('-extend_to_boundary', line)
            m4 = next(line for line in stripes if '-layer Metal4' in line)
            self.assertIn('-offset 13.28', m4); self.assertIn('-spacing 5.58', m4)
            self.assertIn('-pitch 50.0', m4); self.assertIn('-extend_to_boundary', m4)
            unplaced = execute(self.source, 'set ::unplaced 1')
            self.assertEqual(unplaced.returncode, 0, unplaced.stderr)
            for mutation in ('set ::env(PDN_VWIDTH) 2.0', 'set terms [lrange $terms 0 end-1]',
                             'rename term0 originalTerm0;proc term0 {method} {if {$method eq "getIoType"} {return OUTPUT};originalTerm0 $method}',
                             'rename term0 originalTerm0;proc term0 {method} {if {$method eq "getBPins"} {return {}};originalTerm0 $method}',
                             'lappend terms powerTerm;proc powerTerm {method} {dict get {getSigType POWER getBPins pin0} $method}',
                             'proc box0 {method} {if {$method eq "getTechLayer"} {return layer};dict get {xMin 187051 yMin 709640 xMax 187350 yMax 710640} $method}'):
                failed = execute(self.source, mutation)
                self.assertNotEqual(failed.returncode, 0, failed.stdout)
                self.assertNotIn('GRID ', failed.stdout)
            old = self.source.replace('streaming_pdn_m4_first_center_dbu 16160', 'streaming_pdn_m4_first_center_dbu 12880').replace(
                'streaming_pdn_m4_pair_delta_dbu 7680', 'streaming_pdn_m4_pair_delta_dbu 5620')
            failed = execute(old)
            self.assertNotEqual(failed.returncode, 0)
            self.assertIn('clearance', failed.stderr)


if __name__ == '__main__': unittest.main()
