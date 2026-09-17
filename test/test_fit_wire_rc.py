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
