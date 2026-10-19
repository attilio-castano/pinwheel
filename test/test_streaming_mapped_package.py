"""Actual package vector interpretation, without a name-based wire shortcut.

These are parser/generator tests. Same-width source substitutions remain in
the generated proposition; the separate native kernel controls must reject
that proposition. Unsupported bit-vector shapes are refused before Lean.
"""
from copy import deepcopy
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
import streaming_ready_readback as interface
from streaming_mapped_wrapper import ENGINE, package_source


def fixture(addr_bits=1):
    front = interface.backend('frontend', addr_bits)
    core = interface.backend('core', addr_bits)
    next_bit = 2

    def allocate(width):
        nonlocal next_bit
        values = list(range(next_bit, next_bit + width))
        next_bit += width
        return values

    ports = {pin: dict(direction=direction, bits=allocate(width))
        for pin, (direction, width) in ENGINE.items()}
    frontend_outputs = {pin: ports[pin]['bits'] if pin in ('miso', 'ready') else allocate(width)
        for pin, (width, _) in front.OUTPUTS.items()}
    core_outputs = {pin: ports[pin]['bits'] if pin in ('busy', 'levels', 'enabled') else allocate(width)
        for pin, (width, _) in core.OUTPUTS.items()}
    frontend_inputs = {pin: core_outputs[pin.removeprefix('status_')]
        if pin.startswith('status_') else ports[pin]['bits'] for pin in front.INPUTS}
    core_inputs = {pin: frontend_outputs['core_' + pin] for pin in core.INPUTS}

    def child(model, inputs, outputs):
        return dict(type=model.TOP, parameters={},
            port_directions={'clk': 'input', **{pin: 'input' for pin in inputs},
                **{pin: 'output' for pin in outputs}},
            connections=deepcopy({'clk': ports['clk']['bits'], **inputs, **outputs}))

    top = 'pinwheel_streaming_ready_quad_d' + str(2 ** addr_bits)
    return dict(modules={top: dict(ports=ports, netnames={}, cells={
        'frontend': child(front, frontend_inputs, frontend_outputs),
        'core': child(core, core_inputs, core_outputs)})}), top


def generate(data, top, addr_bits=1):
    return package_source(data, top, addr_bits, namespace='Fixture.ActualPackage', netlist_sha256='a' * 64)


class PackageTests(unittest.TestCase):
    def test_complete_actual_vectors_generate_every_typed_connection(self):
        for addr_bits in (1, 2):
            data, top = fixture(addr_bits)
            original = deepcopy(data)
            source = generate(data, top, addr_bits)
            self.assertEqual(data, original)
            self.assertIn('theorem package_correct : Wiring.Certificate ' + str(addr_bits), source)
            self.assertIn('| _, .status .generation => .status .generation', source)
            self.assertIn('| _, .status .transfer => .status .transfer', source)
            self.assertIn('| _, .busy => .status .busy', source)
            self.assertIn('| _, .initialize => .core .initialize', source)
            self.assertIn('| _, .miso => .frontend (.miso)', source)

    def test_same_width_status_swap_is_preserved_for_kernel_rejection(self):
        data, top = fixture()
        connections = data['modules'][top]['cells']['frontend']['connections']
        connections['status_generation'] = connections['status_transfer'][:]
        source = generate(data, top)
        self.assertIn('| _, .status .generation => .status .transfer', source)
        self.assertNotIn('| _, .status .generation => .status .generation', source)
        self.assertIn('case status o => cases o <;> rfl', source)

    def test_reversed_resized_constant_and_undriven_vectors_refused(self):
        for change in ('reverse', 'resize', 'constant', 'undriven'):
            data, top = fixture()
            connections = data['modules'][top]['cells']['frontend']['connections']
            if change == 'reverse': connections['status_generation'].reverse()
            elif change == 'resize': connections['status_generation'].pop()
            elif change == 'constant': connections['status_generation'] = ['0'] * 16
            else: connections['status_generation'] = list(range(90000, 90016))
            with self.subTest(change=change), self.assertRaises(ValueError):
                generate(data, top)

    def test_child_clock_type_parameters_missing_and_extra_logic_refused(self):
        for change in ('clock', 'type', 'parameters', 'missing', 'logic'):
            data, top = fixture()
            module = data['modules'][top]
            if change == 'clock': module['cells']['core']['connections']['clk'] = module['ports']['sck']['bits']
            elif change == 'type': module['cells']['core']['type'] = 'other_core'
            elif change == 'parameters': module['cells']['core']['parameters'] = {'MODE': '1'}
            elif change == 'missing': del module['cells']['frontend']['connections']['status_phase']
            else: module['cells']['extra'] = dict(type='$not')
            with self.subTest(change=change), self.assertRaises(ValueError):
                generate(data, top)

    def test_whole_source_alias_and_reordered_public_vector_refused(self):
        for change in ('source-alias', 'public-reversal'):
            data, top = fixture()
            module = data['modules'][top]
            if change == 'source-alias':
                outputs = module['cells']['core']['connections']
                outputs['transfer'] = outputs['generation'][:]
            else: module['ports']['levels']['bits'] = list(reversed(module['ports']['levels']['bits']))
            with self.subTest(change=change), self.assertRaises(ValueError):
                generate(data, top)


if __name__ == '__main__':
    unittest.main()
