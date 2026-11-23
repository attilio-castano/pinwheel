#!/usr/bin/env python3
"""Portable strict-comparison/encoding tests; these do not run the external model."""
import copy
import importlib.util
import json
from pathlib import Path
import struct
import sys
import unittest

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/"scripts"))
import isa_reference_check as gate
from isa_reference_cases import campaign,KINDS


class ISAReferenceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.cases=campaign()

    def test_complete_kinds_and_determinism(self):
        self.assertEqual(self.cases,campaign())
        self.assertEqual(len(KINDS),40)
        self.assertEqual(set(KINDS),{c["kind"] for c in self.cases if c["kind"]!="illegal"})
        self.assertEqual([c["id"] for c in self.cases],list(range(len(self.cases))))

    def test_raw_elf_exact_payload_and_entry(self):
        for case in self.cases:
            blob=gate.elf(case)
            self.assertEqual(blob[:7],b"\x7fELF\x01\x01\x01")
            self.assertEqual(struct.unpack_from("<I",blob,24)[0],case["pc"])
            self.assertEqual(blob[116:4212],gate.rom_bytes(case))
            self.assertEqual(blob[4212:],bytes(case["ram"]))
            self.assertEqual(struct.unpack_from("<I",blob,116+case["pc"])[0],case["word"])

    def fixture(self):
        return dict(id=0,word=0x13,pc=4,registers=[0]*32,ram=[0]*4096,trap=None)

    def test_all_architectural_fields_compared(self):
        before=self.fixture()
        for key in ("pc","word","id","registers","ram","trap"):
            after=copy.deepcopy(before)
            if key in ("registers","ram"): after[key][-1]=1
            elif key=="trap": after[key]=dict(cause=5,target=0)
            else: after[key]+=1
            with self.assertRaises(AssertionError):gate.compare(before,after)

    def test_truncated_unknown_and_bool_state_fail_as_malformed(self):
        before=self.fixture()
        for value in ([],[0]*31,[0]*31+[True],[0]*31+["x"],[0]*31+[2**32]):
            after=copy.deepcopy(before);after["registers"]=value
            with self.assertRaises(RuntimeError):gate.compare(before,after)
        after=copy.deepcopy(before);del after["trap"]
        with self.assertRaises(RuntimeError):gate.compare(before,after)

    def test_trace_requires_exact_executed_instruction(self):
        case=dict(pc=0,word=0x13)
        text="[0] [M]: 0x00000000 (0x00000013) addi x0, x0, 0\n"
        self.assertIsNone(gate.parse_trace(text,case)["trap"])
        for changed in ("",text+text,text.replace("00000013","00000093"),text.replace("00000000","00000004")):
            with self.assertRaises(RuntimeError):gate.parse_trace(changed,case)

    def test_scalar_types_and_trap_shape_are_strict(self):
        for key in ("id","word","pc"):
            invalid = [False,"0",-1] + ([] if key == "id" else [2**32])
            for value in invalid:
                frame=self.fixture();frame[key]=value
                with self.subTest(key=key,value=value):
                    with self.assertRaises(RuntimeError):gate.compare(frame,copy.deepcopy(frame))
        for trap in (False,{},dict(cause=True,target=None),dict(cause=1,target=None),
                     dict(cause=2,target=0),dict(cause=5,target=False),dict(cause=5,target=None),
                     dict(cause=5,target=2**32),dict(cause=5,target=0,extra=0)):
            frame=self.fixture();frame["trap"]=trap
            with self.subTest(trap=trap):
                with self.assertRaises(RuntimeError):gate.compare(frame,copy.deepcopy(frame))

    def test_complete_trap_evidence_and_address_consistency(self):
        case=dict(pc=0x100,word=0x2083)
        text=("[0] [M]: 0x00000100 (0x00002083) lw x1, 0(x0)\n"
              "handling exc#load-access-fault at priv M | tval=0x00010000 | tval2=0x0\n"
              "CSR mcause (0x342) <- 0x00000005\nCSR mepc (0x341) <- 0x00000100\nCSR mtval (0x343) <- 0x00010000\n")
        self.assertEqual(gate.parse_trace(text,case)["trap"],dict(cause=5,target=0x10000))
        for changed in (text.replace("CSR mcause","MISSING mcause"),text.replace("<- 0x00010000","<- 0x00010004"),text+"Error: fail\n"):
            with self.assertRaises(RuntimeError):gate.parse_trace(changed,case)

    def test_no_accidental_mmio_cases(self):
        # Memory-specific generators use ROM/RAM/unmapped boundaries, never
        # pretend the upstream platform has Pinwheel GPIO/timer/UART semantics.
        for c in self.cases:
            if c["feature"]=="data_fault_priority_x0":
                self.assertFalse(0x40000000<=c["registers"][1]<0x40000300)


if __name__=="__main__":unittest.main()
