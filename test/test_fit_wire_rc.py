"""The wire-RC fit must recover known per-layer values and reject thin data."""
import importlib.util
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("fit_wire_rc", ROOT / "scripts/fit-wire-rc.py")
rc = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(rc)

CAP = {"Metal2": 0.00016, "Metal3": 0.00019}
RES = {"Metal2": 0.7, "Metal3": 0.58}
VIA = 16.0


def design(count):
    """Two-segment nets with one via and varied layer proportions."""
    nets, names, records = [], [], []
    for k in range(count):
        vertical, horizontal = 30 + 7 * k, 40 + 11 * ((k * 5) % 13)
        nets.append(f"- n{k} ( a{k} Y ) ( b{k} A ) + USE SIGNAL\n"
                    f"  + ROUTED Metal2 ( 1000 1000 ) ( * {1000 + vertical * 1000} ) Via2_XY\n"
                    f"  NEW Metal3 ( 1000 {1000 + vertical * 1000} ) ( {1000 + horizontal * 1000} * ) ;")
        names.append(f"*{k + 1} n{k}")
        cap = vertical * CAP["Metal2"] + horizontal * CAP["Metal3"]
        records.append(f"*D_NET *{k + 1} {cap}\n*CONN\n*I a{k}:Y O\n*I b{k}:A I\n"
                       f"*CAP\n1 a{k}:Y {cap}\n*RES\n1 a{k}:Y x:1 {vertical * RES['Metal2']}\n"
                       f"2 x:1 x:2 {VIA}\n3 x:2 b{k}:A {horizontal * RES['Metal3']}\n*END")
    text = ("UNITS DISTANCE MICRONS 1000 ;\nNETS %d ;\n" % count) + "\n".join(nets) + "\nEND NETS\n"
    spef = "*C_UNIT 1 PF\n*R_UNIT 1 OHM\n*NAME_MAP\n" + "\n".join(names) + "\n" + "\n".join(records)
    return text, spef.split("\n")


class FitWireRC(unittest.TestCase):
    def test_route_formatting_does_not_change_lengths_or_fit(self):
        text, spef = design(60)
        expected = rc.routed_lengths(text)
        cap, res, _ = rc.extracted(spef)
        expected_fit = rc.fit(expected, cap, res, 20.0)
        formats = {
            "continued points and vias": text.replace(" ) ( ", " )\n\t( ").replace(
                " ) Via", " )\n\tVia"),
            "several segments on one line": text.replace("\n  NEW", "\tNEW"),
            "split layer and point tokens": text.replace("ROUTED Metal2", "ROUTED\n\tMetal2")
                .replace("NEW Metal3", "NEW\n\tMetal3").replace("( ", "(\n\t")
                .replace(" )", "\n\t)"),
        }
        for label, formatted in formats.items():
            with self.subTest(label=label):
                lengths = rc.routed_lengths(formatted)
                self.assertEqual(lengths["n0"], ({"Metal2": 30.0, "Metal3": 40.0}, 1))
                self.assertEqual(lengths, expected)
                self.assertEqual(rc.fit(lengths, cap, res, 20.0), expected_fit)

    def test_segments_restart_point_chains_and_patch_rectangles_are_not_vias(self):
        text = """UNITS DISTANCE MICRONS 1000 ;
NETS 1 ;
- n0 ( a Y ) ( b A )
  + ROUTED Metal2 ( -1000 -1000 50 )
      ( * 29000 75 ) Via2_XY NEW Metal3 ( -1000 29000 ) ( 39000 * )
  NEW Metal2 ( 100000 100000 ) ( 101000 * )
  NEW Metal2 ( 101000 100000 ) RECT ( -100 -150 100 0 ) ;
END NETS
"""
        self.assertEqual(rc.routed_lengths(text), {"n0": ({"Metal2": 31.0, "Metal3": 40.0}, 1)})

    def test_a_new_segment_cannot_reuse_another_segments_coordinates(self):
        text, _ = design(1)
        text = text.replace("NEW Metal3 ( 1000 31000 )", "NEW Metal3 ( * 31000 )")
        with self.assertRaisesRegex(ValueError, "segment starts with a wildcard coordinate"):
            rc.routed_lengths(text)

    def test_recovers_layer_and_via_values(self):
        text, spef = design(60)
        lengths = rc.routed_lengths(text)
        self.assertEqual(lengths["n0"], ({"Metal2": 30.0, "Metal3": 40.0}, 1))
        cap, res, units = rc.extracted(spef)
        self.assertEqual(units, {"C_UNIT": "1 PF", "R_UNIT": "1 OHM"})
        report = rc.fit(lengths, cap, res, 20.0)
        for layer in CAP:
            self.assertAlmostEqual(report["cap_per_um"][layer], CAP[layer], places=9)
            self.assertAlmostEqual(report["res_per_um"][layer], RES[layer], places=6)
        self.assertAlmostEqual(report["res_per_via"], VIA, places=5)
        self.assertGreater(report["cap_r_squared"], 0.999999)

    def test_rejects_too_few_nets_and_unrouted_designs(self):
        text, spef = design(5)
        cap, res, _ = rc.extracted(spef)
        with self.assertRaises(ValueError):
            rc.fit(rc.routed_lengths(text), cap, res, 20.0)
        with self.assertRaises(ValueError):
            rc.routed_lengths("UNITS DISTANCE MICRONS 1000 ;\n")


if __name__ == "__main__":
    unittest.main()
