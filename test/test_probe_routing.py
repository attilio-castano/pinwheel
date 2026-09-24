"""Static probes must use resolved routing limits, including null clock defaults."""
import importlib.util
from pathlib import Path
import sys
import unittest

SCRIPTS = Path(__file__).resolve().parents[1] / "scripts"
sys.path.insert(0, str(SCRIPTS))
spec = importlib.util.spec_from_file_location("probe_routing", SCRIPTS / "probe-routing.py")
probe = importlib.util.module_from_spec(spec)
spec.loader.exec_module(probe)


class RoutingLimitsTests(unittest.TestCase):
    def test_unresolved_defaults_are_rejected(self):
        with self.assertRaisesRegex(ValueError, "both routing layer limits"):
            probe.routing_layers({"RT_MAX_LAYER": "Metal4"})

    def test_null_clock_limits_follow_resolved_signal_limits(self):
        config = dict(RT_MIN_LAYER="Metal2", RT_MAX_LAYER="Metal4", RT_CLOCK_MIN_LAYER=None, RT_CLOCK_MAX_LAYER=None)
        self.assertEqual(probe.routing_layers(config), ("Metal2-Metal4", "Metal2-Metal4"))
        config.update(RT_CLOCK_MIN_LAYER="Metal3")
        self.assertEqual(probe.routing_layers(config), ("Metal2-Metal4", "Metal3-Metal4"))


if __name__ == "__main__":
    unittest.main()
