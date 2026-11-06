"""Portable controls for the zero-delay graph and sampler transport seam."""

import json
from pathlib import Path
import sys
from types import SimpleNamespace as Row
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
import streaming_8x4_e982_g4_transport as transport


def fixture(offset=0, *, reset="reset", output="q", passive_count=0):
    names = ("clk", "input", "d", "q", "reset")
    wire = {name: offset + index for index, name in enumerate(names, 2)}
    inventory = {"nets": {name: {"wire": value, "signal_type": "CLOCK" if name == "clk" else "SIGNAL"}
                          for name, value in wire.items()}, "unconnected_signal_outputs": {}}
    graph = Row(inputs={"clk": [wire["clk"]], "input": [wire["input"]]}, outputs={"out": [wire[output]]},
                clock=wire["clk"], gates=[Row(name="gate", cell="buffer", connections={"A": wire["input"], "X": wire["d"]},
                                            output=wire["d"])],
                flipflops=[Row(name="ff", cell="state", q=wire["q"], d=wire["d"], clock=wire["clk"], reset_b=wire[reset])],
                passive_loads=[("diode", "antennanp", {"A": wire["q"]})] * passive_count)
    return graph, inventory


class GraphTransportTests(unittest.TestCase):
    def test_renumbering_and_passive_load_changes_preserve_signature(self):
        old = transport.graph_signature(*fixture(passive_count=1))
        self.assertEqual(old, transport.graph_signature(*fixture(102, passive_count=2)))

    def test_reset_and_public_output_remain_observable(self):
        old = transport.graph_signature(*fixture())
        self.assertNotEqual(old, transport.graph_signature(*fixture(reset="input")))
        self.assertNotEqual(old, transport.graph_signature(*fixture(output="d")))

    def test_same_net_spelling_cannot_hide_signal_clock_change(self):
        graph, inventory = fixture()
        old = transport.graph_signature(graph, inventory)
        inventory["nets"]["clk"]["signal_type"] = "SIGNAL"
        self.assertNotEqual(old, transport.graph_signature(graph, inventory))

    def test_sampler_rebinds_both_real_state_rows_and_checks_old_pins(self):
        rows, cells, changed, flops = [], {}, {}, []
        for index in range(6039):
            name = f"ff{index}"
            path = json.dumps([name], separators=(",", ":"))
            flops.append(Row(name=path))
            pins = {pin: 4 * index + bit for bit, pin in enumerate(transport.STATE_PINS, 2)}
            semantic = f"core-d2:r_stage{index + 1}:0" if index < 2 else f"other:{index}"
            rows.append(dict(semantic=semantic, actual_ff=path, actual_cell="state",
                             **{key: pins[pin] for pin, key in transport.STATE_PINS.items()}))
            cells[name] = dict(type="state", connections={pin: [bit] for pin, bit in pins.items()})
            changed[name] = dict(type="state", connections={pin: [bit + 30000] for pin, bit in pins.items()})
        bindings = {f"stage{i + 1}": dict(component="core-d2", register=f"r_stage{i + 1}", index=0,
                                          cell=rows[i]["actual_ff"], q=rows[i]["actual_q"], d=rows[i]["actual_d"],
                                          clock=rows[i]["actual_clock"], reset_b=rows[i]["actual_reset_b"])
                    for i in range(2)}
        arguments = ({"rows": rows}, {"bindings": bindings}, {"modules": {transport.TOP: {"cells": cells}}},
                     {"modules": {transport.TOP: {"cells": changed}}}, Row(flipflops=flops), Row(flipflops=flops))
        result, sampler = transport.state_transport(*arguments)
        self.assertEqual(len(result), 6039)
        self.assertEqual((sampler["stage2"]["cell"], sampler["stage2"]["d"]), ("ff1", 30007))
        bindings["stage2"]["d"] = bindings["stage1"]["d"]
        with self.assertRaisesRegex(ValueError, "sampler witness"):
            transport.state_transport(*arguments)


if __name__ == "__main__":
    unittest.main()
