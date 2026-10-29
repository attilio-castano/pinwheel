"""Portable real producer-kernel schema controls; no Native or campaign files."""
from pathlib import Path
import sys
import unittest
from unittest.mock import patch
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
import streaming_8x4_model24_process_patterns_kernel_readback as W

class KernelReaderControls(unittest.TestCase):
    def test_actual_frozen_producer_returns_dotted_kernel_keys(self):
        kernel={'cpu.max':'100000 100000','memory.max':'2147483648','memory.swap.max':'0','pids.max':'128'}
        with patch('pathlib.Path.read_text',lambda p:kernel[p.name]):self.assertEqual(W.W.S.N.C.cgroups(),kernel)
        self.assertTrue(W.cgroup_contract(kernel))
    def test_renamed_missing_extra_or_resource_keys_are_not_aliases(self):
        kernel={'cpu.max':'100000 100000','memory.max':'2147483648','memory.swap.max':'0','pids.max':'128'}
        for bad in ({k.replace('.','_'):v for k,v in kernel.items()},dict(kernel,extra='0'),dict(kernel,**{'memory.max':'6442450944'}),dict(kernel,**{'cpu.max':'200000 100000'}),dict(kernel,**{'memory.swap.max':'1'})):
            with self.assertRaises(ValueError):W.cgroup_contract(bad)
    def test_only_exact_old_reader_failure_is_preserved(self):
        with patch.object(W.OLD,'readback',side_effect=KeyError('cpu_max')):
            self.assertEqual(W.preserve_old_failure(None,None,None,None,None,None),dict(type='KeyError',args=['cpu_max']))
        with patch.object(W.OLD,'readback',side_effect=KeyError('different')):
            with self.assertRaises(ValueError):W.preserve_old_failure(None,None,None,None,None,None)
        with patch.object(W.OLD,'readback',return_value={}):
            with self.assertRaises(ValueError):W.preserve_old_failure(None,None,None,None,None,None)
    def test_original_work_gate_is_preserved(self):
        self.assertTrue(W.work(dict(actual_work_seconds=90,work_budget_passed=True)))
        self.assertFalse(W.work(dict(actual_work_seconds=90.01,work_budget_passed=False)))
        with self.assertRaises(ValueError):W.work(dict(actual_work_seconds=90.01,work_budget_passed=True))

if __name__=='__main__':unittest.main()
