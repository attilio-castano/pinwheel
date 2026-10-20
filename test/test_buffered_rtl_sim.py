"""Focused simulator provenance/refusal controls; no qualified campaign run."""
from copy import deepcopy
import hashlib
import importlib.util
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('buffered_rtl_sim_driver',
    ROOT / 'scripts/check-buffered-rtl-sim.py')
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)


def blob(data):
    return hashlib.sha1(f'blob {len(data)}\0'.encode() + data).hexdigest()


class SimulatorControls(unittest.TestCase):
    def test_exact_selected_bytes_and_separate_producer_membership(self):
        with tempfile.TemporaryDirectory(prefix='unqualified-sim-membership-') as directory:
            source, producer = Path(directory) / 'selected', Path(directory) / 'producer'
            source.mkdir()
            producer.mkdir()
            (source / 'source.lean').write_bytes(b'import Init\n')
            (producer / 'driver.py').write_bytes(b'# committed producer\n')
            source_tree = {'source.lean': blob((source / 'source.lean').read_bytes())}
            producer_tree = {'driver.py': blob((producer / 'driver.py').read_bytes())}
            source_hashes = gate.membership(source, source_tree, 'sha1')
            self.assertNotEqual(source_hashes, gate.membership(producer, producer_tree, 'sha1'))
            (source / 'source.lean').write_bytes(b'import Init\n-- later change\n')
            with self.assertRaisesRegex(RuntimeError, 'differs from selected committed source'):
                gate.membership(source, source_tree, 'sha1')
            (producer / 'driver.py').write_bytes(b'# changed driver\n')
            with self.assertRaisesRegex(RuntimeError, 'differs from selected committed source'):
                gate.membership(producer, producer_tree, 'sha1')

    def test_tree_refuses_duplicate_nonregular_and_escaping_paths(self):
        valid = '100644 blob ' + 'a' * 40 + '\tsource.py\0'
        self.assertEqual(gate.parse_tree(valid), {'source.py': 'a' * 40})
        for text in (valid + valid, valid.replace('100644', '120000'),
                     valid.replace('source.py', '../source.py'),
                     valid.replace('source.py', '/source.py'),
                     valid.replace('source.py', 'source\n.py')):
            with self.subTest(tree=text), self.assertRaises(RuntimeError):
                gate.parse_tree(text)

    def test_no_borrowed_cache_or_symlinked_input(self):
        with tempfile.TemporaryDirectory(prefix='unqualified-sim-cache-') as directory:
            root = Path(directory)
            gate.fresh_snapshot(root)
            for name in ('.lake', 'build', '.git'):
                (root / name).mkdir()
                with self.assertRaisesRegex(RuntimeError, 'prior repository/build/cache'):
                    gate.fresh_snapshot(root)
                (root / name).rmdir()
            for name in ('Old.olean', 'old.pyc'):
                (root / name).write_bytes(b'old')
                with self.assertRaises(RuntimeError):
                    gate.fresh_snapshot(root)
                (root / name).unlink()
            (root / 'actual').write_bytes(b'fixture')
            (root / 'redirected').symlink_to(root / 'actual')
            with self.assertRaisesRegex(RuntimeError, 'redirected committed input'):
                gate.membership(root, {'redirected': blob(b'fixture')}, 'sha1')

    def test_preuse_artifact_hash_cannot_be_replaced_or_changed(self):
        with tempfile.TemporaryDirectory(prefix='unqualified-sim-freeze-') as directory:
            root = Path(directory)
            artifact = root / 'emitted.sv'
            artifact.write_text('module emitted; endmodule\n')
            report = {}
            gate.freeze(report, root, [artifact])
            original = deepcopy(report)
            gate.freeze(report, root, [artifact])
            gate.check_frozen(report, root)
            artifact.write_text('module changed; endmodule\n')
            with self.assertRaisesRegex(RuntimeError, 'Already frozen simulator input changed'):
                gate.freeze(report, root, [artifact])
            self.assertEqual(report, original)
            with self.assertRaisesRegex(RuntimeError, 'Frozen simulator input changed'):
                gate.check_frozen(report, root)

    def test_environment_refuses_interpreter_and_simulator_overrides(self):
        gate.check_environment({})
        for key in ('PYTHONPATH', 'LEAN_PATH', 'LAKE_CACHE_DIR', 'LD_PRELOAD',
                    'DYLD_INSERT_LIBRARIES', 'IVERILOG_ROOT', 'VPI_MODULE_PATH'):
            with self.subTest(key=key), self.assertRaisesRegex(RuntimeError, 'overrides'):
                gate.check_environment({key: '/unselected'})

    def test_native_versions_use_lakes_embedded_lean_and_pinned_simulator_build(self):
        versions = dict(lean='Lean (version 4.33.1, native)',
            lake='Lake version 5.0.0-src+819816b (Lean version 4.33.1)',
            circt='LLVM version 24\nCIRCT firtool-1.159.0',
            iverilog='Icarus Verilog version 14.0 (devel) (s20260301-436-gd254ea49e-dirty)',
            vvp='Icarus Verilog runtime version 14.0 (devel) (s20260301-436-gd254ea49e-dirty)')
        manifest = dict(packages=dict(circt=dict(release='firtool-1.159.0')))
        gate.check_versions(versions, '4.33.1', manifest)
        for key in versions:
            with self.subTest(tool=key), self.assertRaisesRegex(RuntimeError, 'version mismatch'):
                gate.check_versions(dict(versions, **{key: 'wrong tool version'}), '4.33.1', manifest)
        with self.assertRaisesRegex(RuntimeError, 'version mismatch'):
            gate.check_versions(versions, '4.32.0', manifest)

    def test_exact_three_peer_and_nonempty_frontend_contract(self):
        frontend = dict(cases=1, edges=2, pre_output_checks=3, post_output_checks=4, register_checks=5)
        peers = dict(cases=3, spi_cases=1, jtag_cases=1, i2c_cases=1, physical_edges=9,
            requests=3, responses=3, results_retained_twice=True,
            peer_results=[dict(outcome='complete') for _ in range(3)])
        gate.check_results(frontend, peers)
        for key in frontend:
            with self.subTest(field=key), self.assertRaisesRegex(RuntimeError, 'nonempty'):
                gate.check_results(dict(frontend, **{key: 0}), peers)
        for key, value in [('cases', 0), ('i2c_cases', 0), ('physical_edges', 0),
                           ('responses', 2), ('results_retained_twice', False),
                           ('peer_results', [dict(outcome='fault')] * 3)]:
            with self.subTest(field=key), self.assertRaisesRegex(RuntimeError, 'three-peer'):
                gate.check_results(frontend, dict(peers, **{key: value}))

    def test_completion_marker_is_exact_unique_and_allows_icarus_finish_metadata(self):
        marker = 'Frontend finite replay 123 edges'
        gate.completion_marker(marker + '\nfixture.sv:20: $finish called at 30 (1s)\n', marker)
        for output in ('', marker + '0\n', marker + '\n' + marker + '\n'):
            with self.subTest(output=output), self.assertRaisesRegex(RuntimeError, 'completion marker'):
                gate.completion_marker(output, marker)

    def test_poison_is_independent_for_both_banks_and_q(self):
        anchor = '  pinwheel_buffered_shared_branches_sram_serial dut (.*);'
        fixture = gate.poison_bridge(anchor)
        self.assertNotEqual(*gate.POISON_SEEDS)
        for bank, seed in enumerate(gate.POISON_SEEDS):
            self.assertIn(f"storage{bank}.A_DOUT = 64'h{seed:016x}", fixture)
            self.assertIn(f"storage{bank}.memory[poison] = 64'h{seed:016x} ^ poison", fixture)
        for changed in ('wrong anchor', anchor + anchor):
            with self.assertRaisesRegex(RuntimeError, 'anchor changed'):
                gate.poison_bridge(changed)

    def test_tools_include_icarus_payload_backend_config_vpi_and_runtime(self):
        with tempfile.TemporaryDirectory(prefix='unqualified-sim-tools-') as directory:
            root = Path(directory)
            circt, oss, lean = root / 'firtool-fixture', root / 'oss-fixture', root / 'lean'
            paths = {name: str(path) for name, path in [
                ('circt', circt / 'bin/circt-opt'), ('iverilog', oss / 'bin/iverilog'),
                ('vvp', oss / 'bin/vvp'), ('lean', lean / 'bin/lean'),
                ('lake', lean / 'bin/lake'), ('python', root / 'python')]}
            files = [Path(path) for path in paths.values()]
            files += [oss / 'libexec' / name for name in ('iverilog', 'vvp', 'ivl', 'ivlpp', 'realpath')]
            files += [oss / 'lib/ivl' / name for name in ('vvp.conf', 'vvp.tgt', 'system.vpi')]
            files += [oss / 'lib/runtime.dylib', lean / 'lib/lean/runtime.dylib']
            for path in files:
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(b'\xcf\xfa\xed\xfe native' if path == Path(paths['lean']) else str(path).encode())
            packages = {}
            for name, package, archive_name in [('circt', circt, 'circt.tgz'),
                                                ('oss-cad-suite', oss, 'oss.tgz')]:
                archive = root / archive_name
                archive.write_bytes(name.encode())
                packages[name] = dict(directory=package.name, archive=archive_name, sha256=gate.digest(archive))
            manifest = dict(packages=packages)
            before = gate.tool_identity(paths, manifest)
            for relative in ('libexec/iverilog', 'libexec/vvp', 'libexec/ivl', 'libexec/ivlpp',
                             'lib/ivl/vvp.conf', 'lib/ivl/vvp.tgt', 'lib/ivl/system.vpi', 'lib/runtime.dylib'):
                path = oss / relative
                self.assertIn(str(path), before['files'])
                original = path.read_bytes()
                path.write_bytes(original + b'changed')
                self.assertNotEqual(before, gate.tool_identity(paths, manifest))
                path.write_bytes(original)
            (oss / 'lib/ivl/extra.conf').write_bytes(b'added configuration')
            self.assertNotEqual(before, gate.tool_identity(paths, manifest))
            (oss / 'lib/ivl/extra.conf').unlink()
            (root / 'oss.tgz').write_bytes(b'changed official archive')
            with self.assertRaisesRegex(RuntimeError, 'pinned official archive'):
                gate.tool_identity(paths, manifest)


IVERILOG = ROOT / 'build/tools/oss-cad-suite/bin/iverilog'
VVP = ROOT / 'build/tools/oss-cad-suite/bin/vvp'


@unittest.skipUnless(IVERILOG.is_file() and VVP.is_file(), 'local pinned Icarus installation unavailable')
class DigitalMemoryLaw(unittest.TestCase):
    def test_write_priority_preedge_read_mask_and_held_q(self):
        # Exercise the declared external memory assumption independently of the
        # controller: simultaneous W/R, write-held Q, masked write, read and idle.
        with tempfile.TemporaryDirectory(prefix='unqualified-digital-memory-law-') as directory:
            root = Path(directory)
            (root / 'model.sv').write_text(gate.DIGITAL_MEMORY)
            (root / 'test.sv').write_text('''module tb;
reg clk=0,men=1,wen=0,ren=0; reg[5:0] addr=3;
reg[63:0] data=64'hfedcba9876543210,mask=64'hffffffffffffffff; wire[63:0] q;
RM_IHPSG13_1P_64x64_c2_bm_bist dut(.A_CLK(clk),.A_MEN(men),.A_DLY(1'b1),
.A_WEN(wen),.A_REN(ren),.A_ADDR(addr),.A_DIN(data),.A_BM(mask),.A_DOUT(q),
.A_BIST_CLK(1'b0),.A_BIST_EN(1'b0),.A_BIST_MEN(1'b0),.A_BIST_WEN(1'b0),
.A_BIST_REN(1'b0),.A_BIST_ADDR(6'b0),.A_BIST_DIN(64'b0),.A_BIST_BM(64'b0));
task tick; begin #5;clk=1;#5;clk=0;end endtask
initial begin
dut.memory[3]=64'h123456789abcdef0; dut.A_DOUT=64'h55;
wen=1;ren=1; tick;
if(q!==64'h55 || dut.memory[3]!==64'hfedcba9876543210) $fatal(1,"write priority/held Q");
wen=0;ren=1; tick; if(q!==64'hfedcba9876543210) $fatal(1,"synchronous read");
wen=1;data=64'h1;mask=64'hff; tick;
if(q!==64'hfedcba9876543210 || dut.memory[3]!==64'hfedcba9876543201) $fatal(1,"masked write");
wen=0;ren=0;tick;if(q!==64'hfedcba9876543210) $fatal(1,"idle hold");
men=0;ren=1;tick;if(q!==64'hfedcba9876543210) $fatal(1,"MEN hold");
men=1;tick;if(q!==64'hfedcba9876543201) $fatal(1,"read updated cell");
$display("digital memory law passed"); $finish;
end
endmodule
''')
            subprocess.run([str(IVERILOG), '-g2012', '-s', 'tb', '-o', str(root / 'test.vvp'),
                            str(root / 'model.sv'), str(root / 'test.sv')], check=True,
                           stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=30)
            result = subprocess.run([str(VVP), str(root / 'test.vvp')], check=True,
                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, timeout=30)
            gate.completion_marker(result.stdout, 'digital memory law passed')


if __name__ == '__main__':
    unittest.main()
