#!/usr/bin/env python3
"""Portable, fail-closed tests for the emitted system boot evidence checker."""
from copy import deepcopy
import importlib.util
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/"scripts"))
spec=importlib.util.spec_from_file_location("system_boot",ROOT/"scripts/check-processor-system-boot.py")
boot=importlib.util.module_from_spec(spec)
spec.loader.exec_module(boot)


def rows(names,widths,registers=False):
    return [{"index":k,"name":n,"width":w,**({"reference":n} if registers else {})}
            for k,(n,w) in enumerate(zip(names,widths,strict=True))]


def descriptor():
    d={"schema":1,"module":"processor_system","clock":"clk","rom_word_width":5,"ram_word_width":2,
       "ram_base":0x10000,"gpio_base":0x40000000,"timer_base":0x40000100,"uart_base":0x40000200,
       "top_verilog":"top.sv","latency_added":0,"reset_synchronous":True,"rom_words":boot.PROGRAM+[0]*19,
       "inputs":rows(boot.INPUT_NAMES,boot.INPUT_WIDTHS),
       "outputs":rows([f"state_{k}" for k in range(37)],boot.OUTPUT_WIDTHS),
       "registers":rows([f"r_state_{k}" for k in range(60)],boot.REGISTER_WIDTHS),
       "roles":{n:n for n in boot.INPUT_NAMES},"leaf_interfaces":[]}
    d["roles"].update({"core_"+n:f"state_{k}" for k,n in enumerate(boot.CORE_OUTPUT_ROLES)})
    d["roles"].update({"mmio_"+n:f"state_{k+30}" for k,n in enumerate(boot.MMIO_OUTPUT_ROLES)})
    configs=[("core",boot.CORE_INPUT_NAMES,boot.CORE_INPUT_WIDTHS,boot.CORE_OUTPUT_WIDTHS,
              [f"r_state_{k}" for k in range(37)],boot.CORE_REGISTER_WIDTHS),
             ("ram",boot.RAM_INPUT_NAMES,boot.RAM_INPUT_WIDTHS,boot.RAM_OUTPUT_WIDTHS,
              [f"r_state_{k}" for k in range(12)],boot.RAM_REGISTER_WIDTHS),
             ("mmio",boot.MMIO_INPUT_NAMES,boot.MMIO_INPUT_WIDTHS,boot.MMIO_OUTPUT_WIDTHS,
              boot.MMIO_REGISTER_NAMES,boot.MMIO_REGISTER_WIDTHS),
             ("bus",[f"state_{k}" for k in range(47)],boot.INPUT_WIDTHS+boot.CORE_OUTPUT_WIDTHS+boot.RAM_OUTPUT_WIDTHS+boot.MMIO_OUTPUT_WIDTHS,
              boot.CORE_INPUT_WIDTHS+boot.RAM_INPUT_WIDTHS+boot.MMIO_INPUT_WIDTHS,boot.FETCH_NAMES,boot.FETCH_WIDTHS)]
    refs=[]
    for name,ins,iw,ow,regs,rw in configs:
        d["leaf_interfaces"].append({"module":"processor_system_"+name,"clock":"clk","mlir":name+".mlir",
            "inputs":rows(ins,iw),"outputs":rows([f"out_state_{k}" for k in range(len(ow)+len(rw))],ow+rw),
            "registers":rows(regs,rw,True),"state_taps":{n:f"out_state_{len(ow)+k}" for k,n in enumerate(regs)}})
        refs += [name+"."+r for r in regs]
    for p,ref in zip(d["registers"],refs,strict=True):p.update(reference=ref,flat_reference=p["name"],tap=p["name"])
    d["hierarchical_registers"]=refs
    d["register_map"]={p["name"]:p["reference"] for p in d["registers"]}
    return d


def wiring(d):
    header=["input wire clk"]+[f"input wire [{p['width']-1}:0] {p['name']}" for p in d["inputs"]]
    header += [f"output wire [{p['width']-1}:0] {p['name']}" for p in d["outputs"]]
    lines=["module processor_system("+", ".join(header)+");"]
    nets={p["name"]:p["width"] for p in d["registers"]}
    for prefix,names,widths in (("core_input_",boot.CORE_INPUT_NAMES,boot.CORE_INPUT_WIDTHS),
        ("ram_input_",boot.RAM_INPUT_NAMES,boot.RAM_INPUT_WIDTHS),("mmio_input_",boot.MMIO_INPUT_NAMES,boot.MMIO_INPUT_WIDTHS),
        ("ram_output_",boot.RAM_OUTPUT_NAMES,boot.RAM_OUTPUT_WIDTHS)):
        nets.update(zip([prefix+n for n in names],widths,strict=True))
    lines += [f"wire [{w-1}:0] {n};" for n,w in nets.items()]
    bus_inputs=boot.INPUT_NAMES+[f"state_{k}" for k in range(30)]+["ram_output_"+n for n in boot.RAM_OUTPUT_NAMES]+[f"state_{k}" for k in range(30,37)]
    bus_outputs=["core_input_"+n for n in boot.CORE_INPUT_NAMES]+["ram_input_"+n for n in boot.RAM_INPUT_NAMES]+["mmio_input_"+n for n in boot.MMIO_INPUT_NAMES]
    configs=[("core",["core_input_"+n for n in boot.CORE_INPUT_NAMES],[f"state_{k}" for k in range(30)],0,37),
        ("ram",["ram_input_"+n for n in boot.RAM_INPUT_NAMES],["ram_output_"+n for n in boot.RAM_OUTPUT_NAMES],37,12),
        ("mmio",["mmio_input_"+n for n in boot.MMIO_INPUT_NAMES],[f"state_{k}" for k in range(30,37)],49,8),
        ("bus",bus_inputs,bus_outputs,57,3)]
    for leaf,(name,ins,outs,start,count) in zip(d["leaf_interfaces"],configs,strict=True):
        pairs=[("clk","clk")]+list(zip([p["name"] for p in leaf["inputs"]],ins,strict=True))
        pairs += list(zip([p["name"] for p in leaf["outputs"]],outs+[f"r_state_{k}" for k in range(start,start+count)],strict=True))
        lines.append(f"processor_system_{name} {name}("+", ".join(f".{p}({v})" for p,v in pairs)+");")
    return "\n".join(lines+["endmodule",""])


def trace_fixture():
    d={"inputs":rows(["input"],[1]),"outputs":rows(["valid","data"],[1,3]),"registers":rows(["q"],[3],True)}
    want=[("IN",0,0),("PRE",0,1,5),("POST",0,0,0),("REG",0,5),
          ("IN",1,1),("PRE",1,0,0),("POST",1,1,6),("REG",1,6)]
    lines=[]
    for kind,cycle,*values in want:
        ps=d["inputs" if kind=="IN" else "registers" if kind=="REG" else "outputs"]
        lines.append(",".join([kind,str(cycle)]+[f"{v:0{p['width']}b}" for v,p in zip(values,ps,strict=True)]))
    return d,want,lines+["SYSTEM_DONE","tb.sv:10: $finish called at 9000 (1ps)"]


class DescriptorTests(unittest.TestCase):
    def test_complete_descriptor_and_wiring(self):
        d=descriptor();self.assertEqual(boot.validate_descriptor(d),d)
        self.assertEqual(boot.validate_topology(d,wiring(d))["registers"],60)

    def test_descriptor_rejects_omission_alias_and_permutation(self):
        mutations=[lambda d:d["outputs"].pop(),lambda d:d["registers"].pop(),
            lambda d:d["leaf_interfaces"][3]["inputs"].pop(),lambda d:d["register_map"].pop("r_state_59"),
            lambda d:d["registers"][0].update(reference="core.r_state_1"),
            lambda d:d["leaf_interfaces"][0]["state_taps"].update(r_state_0="out_state_31"),
            lambda d:d["roles"].update(core_retire_pc="state_14"),
            lambda d:d["inputs"][1].update(width=31),lambda d:d["inputs"][0].update(index=False),
            lambda d:d["inputs"][0].update(width=True),lambda d:d.update(schema=True),
            lambda d:d["leaf_interfaces"][0].update(mlir="../core.mlir"),
            lambda d:d["rom_words"].__setitem__(2,0)]
        for mutate in mutations:
            with self.subTest(mutate=mutate):
                d=descriptor();mutate(d)
                with self.assertRaises(ValueError):boot.validate_descriptor(d)

    def test_same_width_wiring_swaps_and_missing_connections(self):
        d=descriptor();text=wiring(d)
        corruptions=[text.replace(".out_state_12(state_12)",".out_state_12(state_14)"),
            text.replace(".out_state_30(r_state_0)",".out_state_30(r_state_1)"),
            text.replace(".state_0(reset), ",""),text.replace(".state_0(reset)",".state_0(reset), .state_0(reset)"),
            text.replace("endmodule","assign state_12 = 0;\nendmodule"),text+"endmodule\n",""]
        for bad in corruptions:
            with self.subTest(bad=bad[:50]):
                with self.assertRaises(ValueError):boot.validate_topology(d,bad)

    def test_numeric_inputs_reject_bools_and_overflow(self):
        self.assertTrue(boot.numbers([0,7],[1,3]))
        for values in ([False,7],[0,8],[0,-1],[0],(0,7)):
            self.assertFalse(boot.numbers(values,[1,3]))


class TraceTests(unittest.TestCase):
    def test_positive_complete_binary_trace(self):
        d,want,lines=trace_fixture();self.assertEqual(boot.check_trace("\n".join(lines),want,d),8)

    def test_concrete_wrong_value_with_full_trace(self):
        d,want,lines=trace_fixture();lines[1]="PRE,0,1,100"
        with self.assertRaises(boot.ConcreteMismatch) as caught:boot.check_trace("\n".join(lines),want,d)
        self.assertEqual(caught.exception.witness["expected"],5)
        self.assertEqual(caught.exception.witness["actual"],4)
        self.assertEqual(len(caught.exception.observations),8)

    def test_later_malformed_trace_overrides_early_semantic_difference(self):
        d,want,valid=trace_fixture()
        corruptions=[lambda x:x.__setitem__(7,"REG,1,0x1"),lambda x:x.__setitem__(7,"REG,1,01"),
            lambda x:x.__setitem__(7,"REG,01,101"),lambda x:x.pop(7),lambda x:x.append("garbage"),
            lambda x:x.__setitem__(7,"REG,1,101,0"),lambda x:x.__setitem__(6,"PRE,1,1,110"),
            lambda x:x.__setitem__(7,"REG,2,101"),lambda x:x.insert(8,"REG,1,110"),
            lambda x:x.pop(),lambda x:x.pop(8),lambda x:x.insert(8,"SYSTEM_DONE"),
            lambda x:x.__setitem__(7,"REG,1,zzz"),lambda x:x.insert(0,x[-1])]
        for mutate in corruptions:
            lines=valid.copy();lines[1]="PRE,0,1,100";mutate(lines)
            with self.subTest(lines=lines):
                with self.assertRaises(boot.TraceError):boot.check_trace("\n".join(lines),want,d)

    def test_edge_order_rejection(self):
        d,want,lines=trace_fixture();lines[1],lines[2]=lines[2],lines[1]
        with self.assertRaises(boot.TraceError):boot.check_trace("\n".join(lines),want,d)


class MutationTests(unittest.TestCase):
    def test_changes_exactly_one_existing_assignment(self):
        d=descriptor();sources={"core":"r_state_1 <= next_x2;\nassign out_state_12 = pc;\n",
            "ram":"r_state_0 <= next_word;\n","mmio":"r_gpio <= next_gpio;\n","bus":"unchanged"}
        results=list(boot.mutations(sources,d))
        self.assertEqual(len(results),4)
        self.assertEqual(len({n for n,_,_ in results}),4)
        for _,leaf,changed in results:
            self.assertNotEqual(changed,sources[leaf])
            self.assertEqual(len(changed.splitlines()),len(sources[leaf].splitlines()))
        self.assertIn("5'd2",results[0][2]);self.assertIn("32'd4",results[1][2])
        self.assertIn("response_ready",results[2][2]);self.assertIn("6'd1",results[3][2])

    def test_missing_or_ambiguous_assignments_fail(self):
        for source in ("r_other <= d;","r_q <= a; r_q <= b;"):
            with self.assertRaises(ValueError):boot.mutate_assignment(source,"r_q",lambda rhs:"0")

    def test_active_control_witness_is_required(self):
        # A mismatch at the intended endpoint alone is insufficient.
        startup=[0]*60
        observation=[("IN",1,*([0]*6)),("PRE",1,*([0]*37)),("POST",1,*([0]*37)),
                     ("REG",0,*startup),("REG",1,*startup)]
        witness={"observation":"REG","cycle":1,"index":1,"expected":128,"actual":129}
        error=boot.ConcreteMismatch(witness,observation)
        with self.assertRaises(AssertionError):boot.semantic_witness("corrupt-active-x2",error,startup)
        pre=list(observation[1]);pre[2+15]=1;pre[2+16]=2;observation[1]=tuple(pre)
        self.assertTrue(boot.semantic_witness("corrupt-active-x2",error,startup)["complete_binary_trace"])


if __name__=="__main__":unittest.main()
