"""Refuse stale mapped/PDK/clock/layer inputs before any physical tool starts."""
from copy import deepcopy
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import streaming_tt_physical as P
spec = importlib.util.spec_from_file_location('streaming_tt_runner_test', ROOT / 'scripts/run-streaming-tt-physical.py')
R = importlib.util.module_from_spec(spec); spec.loader.exec_module(R)


class PhysicalTests(unittest.TestCase):
    def test_exact_standardcell_clock_pins_layers_and_no_sram_config(self):
        config = P.read(ROOT / 'physical/streaming-tt.json'); P.validate_config(config, 2)
        for key, value in [('CLOCK_PERIOD', 40), ('RT_MAX_LAYER', 'TopMetal1'), ('PDN_HORIZONTAL_LAYER', 'TopMetal1'),
                ('MACROS', {}), ('RUN_CTS', False), ('TIMING_VIOLATION_CORNERS', ['typical']), ('PL_TARGET_DENSITY_PCT', 50)]:
            changed = deepcopy(config); changed[key] = value
            with self.subTest(key=key), self.assertRaises(ValueError): P.validate_config(changed, 2)
        sdc = (ROOT / 'physical/streaming-tt.sdc').read_text()
        self.assertNotIn('set_false_path', sdc)
        self.assertIn('-max 4.0', sdc); self.assertIn('-min 0.2', sdc)
        pdn = (ROOT / 'physical/streaming_tt/pdn.tcl').read_text()
        self.assertNotIn('-layer TopMetal', pdn)
        for layer in ['Metal1', 'Metal2', 'Metal3', 'Metal4']: self.assertIn('-layer ' + layer, pdn)

    def test_every_horizontal_rail_has_a_crossing_vertical_power_connection(self):
        pdn = (ROOT / 'physical/streaming_tt/pdn.tcl').read_text()
        # Pinned technology directions: M1/M3 horizontal, M2/M4 vertical.
        # Require adjacent-layer connections. A direct M1-to-M4 stack leaves
        # periodic channel bands around the M3 straps in the pinned runtime.
        self.assertIn('-layers {Metal1 Metal2}', pdn)
        self.assertIn('-layers {Metal2 Metal3}', pdn)
        self.assertIn('-layers {Metal3 Metal4}', pdn)
        self.assertNotIn('-layers {Metal1 Metal3}', pdn)
        self.assertNotIn('-layers {Metal1 Metal4}', pdn)
        self.assertIn('-layer Metal2 -width 1.0', pdn)
        self.assertNotIn('-skip', pdn)

    def test_physical_flow_keeps_header_but_removes_state_optimization(self):
        source = (ROOT / 'physical/streaming_tt/librelane_plugin_streaming_tt.py').read_text()
        self.assertIn("'Yosys.Synthesis'", source)
        self.assertNotIn("'Yosys.JsonHeader'", source)
        seed = dict(nl='/work/inputs/design.v', metrics={})
        self.assertEqual(set(seed), {'nl', 'metrics'})

    def test_safe_names_paths_and_duplicate_json_refuse(self):
        for value in ['../outside', '/absolute', '', 'space name']:
            with self.assertRaises(ValueError): P.safe_name(value)
        for value in ['../outside', '/absolute']:
            with self.assertRaises(ValueError): P.relative_path(value)
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / 'input.json'; path.write_text('{"passed":true,"passed":false}')
            with self.assertRaises(ValueError): P.read(path)

    def test_pdk_hash_receipt_does_not_override_pinned_git_blob(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary); pdk = root / 'pdk'; pdk.mkdir(); (pdk / 'view').write_bytes(b'pinned view')
            data = (pdk / 'view').read_bytes()
            tree = root / 'tree.json'; P.write(tree, dict(truncated=False, tree=[dict(path='view', mode='100644',
                sha=hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest())]))
            lock = dict(pdk_revision='revision', pdk_tree_sha256=P.sha(tree))
            receipt = dict(revision='revision', tree_sha256=P.sha(tree), files_sha256={'view': P.sha(pdk / 'view')}, symlinks={})
            P.write(pdk / 'installed.json', receipt); P.verify_pdk(pdk, lock, tree)
            (pdk / 'view').write_bytes(b'changed view'); receipt['files_sha256']['view'] = P.sha(pdk / 'view')
            P.write(pdk / 'installed.json', receipt)
            with self.assertRaisesRegex(ValueError, 'pinned Git blob'): P.verify_pdk(pdk, lock, tree)

    def test_runtime_rootfs_and_config_are_both_checked(self):
        image = dict(Id='image', Architecture='arm64', Os='linux', RootFS={'Layers': ['layer']}, Config={'A': 1})
        lock = dict(container_tag='pinned', container_rootfs_diff_ids=['layer'],
            container_runtime_config_sha256=hashlib.sha256(json.dumps({'A': 1}, sort_keys=True).encode()).hexdigest())
        response = type('Response', (), dict(returncode=0, stdout=json.dumps([image]), stderr=''))()
        with patch.object(P.subprocess, 'run', return_value=response): self.assertEqual(P.inspect_runtime(lock)['image_id'], 'image')
        for mode in ['rootfs', 'config', 'architecture']:
            changed = deepcopy(image)
            if mode == 'rootfs': changed['RootFS']['Layers'] = ['other']
            elif mode == 'config': changed['Config'] = {'A': 2}
            else: changed['Architecture'] = 'amd64'
            response.stdout = json.dumps([changed])
            with patch.object(P.subprocess, 'run', return_value=response), self.assertRaises(ValueError): P.inspect_runtime(lock)

    def test_native_command_is_offline_readonly_inputs_and_exact_postmap_seed(self):
        command = R.container_command(Path('/stage'), Path('/output'), {'image_id': 'immutable-image'}, 'fresh', 'owner', R.STOPS[-1])
        self.assertEqual(command[command.index('--network') + 1], 'none')
        self.assertEqual(command[command.index('--cpus') + 1], '4')
        self.assertEqual(command[command.index('--memory') + 1], '6g')
        self.assertEqual(command[command.index('--memory-swap') + 1], '6g')
        self.assertIn('type=bind,source=/stage/inputs,target=/work/inputs,readonly', command)
        self.assertIn('type=bind,source=/stage/pdk,target=/work/pdk,readonly', command)
        self.assertEqual(command[command.index('--with-initial-state') + 1], '/work/inputs/seed.json')
        self.assertNotIn('pull', command[:2])

    def test_carried_netlist_is_not_claimed_current_after_odb_only_repairs(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary); out = root / 'flow'; step = out / 'stage'; step.mkdir(parents=True)
            (step / 'state.odb').write_bytes(b'actual ODB'); (step / 'before.nl.v').write_bytes(b'earlier NL')
            P.write(step / 'state_out.json', dict(odb='/work/run/stage/state.odb', nl='/work/run/stage/before.nl.v', metrics={}))
            result = R.collect_states(out, root)
            self.assertTrue(result[0]['carried_netlist_requires_ODB_reexport'])
            self.assertEqual(result[0]['authoritative_physical_view'], 'odb')
            self.assertEqual(result[0]['views']['odb']['sha256'], P.sha(step / 'state.odb'))

    def test_tool_generated_view_cannot_escape_its_mounted_root(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary); out = root / 'flow'; step = out / 'stage'; step.mkdir(parents=True)
            (root / 'outside.odb').write_bytes(b'outside artifact')
            P.write(step / 'state_out.json', dict(odb='/work/run/../outside.odb', metrics={}))
            with self.assertRaisesRegex(ValueError, 'escapes its mounted root'): R.collect_states(out, root)

    def test_optimized_run_reexecutes_exact_frozen_worker_before_native_tools(self):
        with tempfile.TemporaryDirectory() as temporary:
            base=Path(temporary);design=base/'candidate';worker=design/'inputs/producer/scripts/run-streaming-tt-physical.py'
            worker.parent.mkdir(parents=True);worker.write_text('# exact staged worker\n')
            value=dict(schema='pinwheel.streaming-tt-physical-input.v2',
                producer_sha256={'scripts/run-streaming-tt-physical.py':P.sha(worker)})
            class Reexec(Exception): pass
            with patch.object(R,'BASE',base),patch.object(R,'verify_prepared',return_value=value),\
                    patch.object(sys,'argv',['runner','--design','candidate','--tag','fresh']),\
                    patch.object(R.os,'execv',side_effect=Reexec) as execute:
                with self.assertRaises(Reexec):R.main()
            command=execute.call_args.args[1]
            self.assertEqual(command[:3],[sys.executable,'-B',str(worker)])
            self.assertEqual(command[-2:],['--frozen-input',str(design/'inputs.json')])


if __name__ == '__main__': unittest.main()
