#!/usr/bin/env python3
"""Cold-loader descriptor, topology and fixed-knownness trace regression tests."""
from copy import deepcopy
import importlib.util
from pathlib import Path
import sys
import unittest

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/"scripts"))
def load(name,path):
    spec=importlib.util.spec_from_file_location(name,ROOT/path)
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);return module
cold=load("loadable_boot","scripts/check-processor-loadable-system-boot.py")
fixture=load("previous_boot_tests","test/test_processor_system_boot.py")
boot=cold.boot


def descriptor():
    d=fixture.descriptor();d["module"]="processor_loadable_system"
    d["inputs"]=fixture.rows(cold.INPUT_NAMES,cold.INPUT_WIDTHS)
    d["outputs"]=fixture.rows(cold.OUTPUT_NAMES,cold.OUTPUT_WIDTHS)
    d["roles"]={n:cold.INPUT_NAMES[k] for k,n in enumerate(boot.INPUT_NAMES+["loader_mode","loader_valid","loader_address","loader_data"])}
    d["roles"].update({"core_"+n:cold.OUTPUT_NAMES[k] for k,n in enumerate(boot.CORE_OUTPUT_ROLES)})
    d["roles"].update({"mmio_"+n:cold.OUTPUT_NAMES[k+30] for k,n in enumerate(boot.MMIO_OUTPUT_ROLES)})
    d["roles"].update(loader_ready="state_37",running="state_38")
    d["leaf_interfaces"]=[]
    for name,ins,iw,ow,regs,rw in cold.leaf_shapes():
        d["leaf_interfaces"].append({"module":"processor_loadable_system_"+name,"mlir":name+".mlir","clock":"clk",
            "inputs":fixture.rows(ins,iw),"outputs":fixture.rows([f"out_state_{k}" for k in range(len(ow)+len(rw))],ow+rw),
            "registers":fixture.rows(regs,rw,True),"state_taps":{r:f"out_state_{len(ow)+k}" for k,r in enumerate(regs)}})
    return d


def wiring(d):
    header=["input wire clk"]+[f"input wire [{p['width']-1}:0] {p['name']}" for p in d["inputs"]]
    header += [f"output wire [{p['width']-1}:0] {p['name']}" for p in d["outputs"]]
    wires,instances=cold.topology_expected(d)
    lines=["module processor_loadable_system("+", ".join(header)+");"]
    lines += [f"wire [{w-1}:0] {n};" for n,w in wires.items()]
    for n,ports in instances.items():lines.append(f"processor_loadable_system_{n} {n}("+", ".join(f".{p}({v})" for p,v in ports.items())+");")
    return "\n".join(lines+["endmodule",""])


def frames():
    result=[]
    for k in range(9):
        i=[int(k in (0,7)),0xdecafbad,0,0,0,0,int(k<8),int(k in (0,2,3,4,5,7)),max(0,k-2)%4,0x11223344+max(0,k-2)%4]
        pre=[0]*39;post=[0]*39;registers=[0]*60
        if k==8:pre[4]=1;pre[6]=0x10000;pre[7]=0
        result.append({"cycle":k,"input":i,"pre":pre,"post":post,"registers":registers})
    return result


def trace_fixture():
    d={"inputs":fixture.rows(["input"],[1]),"outputs":fixture.rows(["valid"],[1]),"registers":fixture.rows(["q"],[3],True)}
    want=[("IN",0,1),("PRE",0,0),("POST",0,0),("REG",0,None),
          ("IN",1,0),("PRE",1,0),("POST",1,1),("REG",1,5)]
    lines=["IN,0,1","PRE,0,0","POST,0,0","REG,0,xxx","IN,1,0","PRE,1,0","POST,1,1","REG,1,101",
           "LOADABLE_DONE","tb.sv:8: $finish called at 6000 (1ps)"]
    return d,want,lines


class SchemaTests(unittest.TestCase):
    def test_exact_typed_hierarchy(self):
        d=descriptor();cold.validate_descriptor(d)
        self.assertEqual(cold.validate_topology(d,wiring(d))["registers"],60)

    def test_omission_width_alias_and_path_failures(self):
        changes=[lambda d:d["inputs"].pop(),lambda d:d["outputs"][38].update(width=2),
            lambda d:d["inputs"][0].update(index=False),lambda d:d["inputs"][0].update(width=True),
            lambda d:d["register_map"].pop("r_state_59"),lambda d:d["registers"][37].update(reference="ram.r_state_1"),
            lambda d:d["roles"].update(loader_valid="in_state_6"),
            lambda d:d["leaf_interfaces"][1]["state_taps"].update(r_state_0="out_state_6"),
            lambda d:d["leaf_interfaces"][3].update(mlir="../bus.mlir")]
        for change in changes:
            with self.subTest(change=change):
                d=descriptor();change(d)
                with self.assertRaises(ValueError):cold.validate_descriptor(d)

    def test_same_width_reset_and_loader_control_swaps_rejected(self):
        d=descriptor();text=wiring(d)
        for a,b in ((".state_0(in_state_0)",".state_0(in_state_6)"),
            (".out_state_12(ram_input_state_0)",".out_state_12(ram_input_state_9)"),
            (".out_state_36(state_37)",".out_state_36(state_38)"),
            (".out_state_5(r_state_37)",".out_state_5(r_state_38)")):
            self.assertIn(a,text)
            with self.assertRaises(ValueError):cold.validate_topology(d,text.replace(a,b))

    def test_testbench_never_forces_or_initializes_dut(self):
        text=cold.testbench(descriptor(),frames(),True)
        for forbidden in ("force ","release ","$deposit","$readmem","dut.ram.r_state_0 ="):
            self.assertNotIn(forbidden,text)
        self.assertIn("dut.ram.r_state_0",text)


class InitializationTests(unittest.TestCase):
    def test_dut_initialization_is_rejected(self):
        graph={"modules":{"dut":{"netnames":{"q":{"attributes":{}}},"cells":{}}}}
        cold.check_no_initialization(graph)
        wrong=deepcopy(graph);wrong["modules"]["dut"]["netnames"]["q"]["attributes"]["init"]="0"
        with self.assertRaises(ValueError):cold.check_no_initialization(wrong)
        wrong=deepcopy(graph);wrong["modules"]["dut"]["cells"]["initial"]={"type":"$meminit_v2"}
        with self.assertRaises(ValueError):cold.check_no_initialization(wrong)

    def test_definedness_requires_real_reset_load_and_capture(self):
        masks,coverage=cold.initialization(frames())
        self.assertTrue(masks[0][0]);self.assertTrue(masks[0][48]);self.assertTrue(masks[0][59])
        self.assertEqual(masks[0][37:48],[False]*11)
        self.assertTrue(masks[2][37]);self.assertFalse(masks[2][38])
        self.assertEqual(masks[5][37:41],[True]*4)
        self.assertEqual(masks[7][41:48],[False]*7)
        self.assertTrue(all(masks[8]));self.assertEqual(coverage["first_metadata_capture_cycle"],8)
        self.assertEqual([w["address"] for w in coverage["loader_writes"]],[0,1,2,3])
        self.assertEqual(coverage["startup_forced_registers"],0)

    def test_no_implicit_memory_initialization_or_unproven_q(self):
        for mutate in (lambda f:f[0]["input"].__setitem__(0,0),
                       lambda f:f[4]["input"].__setitem__(7,0),
                       lambda f:f[8]["pre"].__setitem__(4,0),
                       lambda f:f[8]["pre"].__setitem__(7,3)):
            fs=frames();mutate(fs)
            with self.assertRaises(ValueError):cold.initialization(fs)


class TraceTests(unittest.TestCase):
    def test_uninitialized_bits_can_be_unknown_or_arbitrary_binary(self):
        d,want,lines=trace_fixture()
        self.assertEqual(cold.check_trace("\n".join(lines),want,d),8)
        for value in ("000","111","0x1"):
            changed=lines.copy();changed[3]="REG,0,"+value
            self.assertEqual(cold.check_trace("\n".join(changed),want,d),8)

    def test_defined_wrong_value_is_concrete(self):
        d,want,lines=trace_fixture();lines[7]="REG,1,100"
        with self.assertRaises(boot.ConcreteMismatch) as caught:cold.check_trace("\n".join(lines),want,d)
        self.assertEqual(caught.exception.witness["expected"],5);self.assertEqual(caught.exception.witness["actual"],4)

    def test_complete_trace_required_before_semantic_failure(self):
        d,want,valid=trace_fixture()
        changes=[lambda x:x.__setitem__(7,"REG,1,xxx"),lambda x:x.__setitem__(7,"REG,1,10"),
            lambda x:x.__setitem__(3,"REG,0,zzz"),lambda x:x.pop(7),lambda x:x.append("diagnostic"),
            lambda x:x.__setitem__(7,"REG,2,101"),lambda x:x.pop(),lambda x:x.insert(0,x[-1]),
            lambda x:x.__setitem__(1,"PRE,0,x"),lambda x:x.insert(8,"REG,1,101")]
        for mutate in changes:
            changed=valid.copy();changed[2]="POST,0,1";mutate(changed)
            with self.subTest(changed=changed):
                with self.assertRaises(boot.TraceError):cold.check_trace("\n".join(changed),want,d)

    def test_unconstrained_external_outputs_are_forbidden(self):
        d,want,lines=trace_fixture();want[1]=("PRE",0,None)
        with self.assertRaises(boot.TraceError):cold.check_trace("\n".join(lines),want,d)


class MutationTests(unittest.TestCase):
    def test_five_actual_assignment_mutations(self):
        source={"core":"r_state_1 <= next_x2;\nassign out_state_12 = pc;\n","ram":"r_state_0 <= next_word;\n",
                "mmio":"r_gpio <= next_gpio;\n","bus":"unchanged"}
        changes=list(cold.mutations(source,descriptor()))
        self.assertEqual(len(changes),5)
        for _,leaf,text in changes:self.assertNotEqual(text,source[leaf])
        self.assertIn("~state_9",changes[2][2]);self.assertIn("state_10",changes[4][2])

    def test_loader_active_acceptance_is_mandatory(self):
        w={"observation":"REG","cycle":2,"index":37,"expected":0x11223344,"actual":0x11223345}
        i=[0]*10;rows=[("IN",2,*i)]
        with self.assertRaises(AssertionError):cold.semantic_witness("corrupt-loader-word",boot.ConcreteMismatch(w,rows),[0]*60)
        i[6]=1;i[7]=1;rows=[("IN",2,*i)]
        witness=cold.semantic_witness("corrupt-loader-word",boot.ConcreteMismatch(w,rows),[0]*60)
        self.assertTrue(witness["complete_binary_defined_trace"])


if __name__=="__main__":unittest.main()
