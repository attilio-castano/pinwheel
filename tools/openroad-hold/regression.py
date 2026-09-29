"""Native counterexamples for the pinned hold optimizer (run in its image)."""
import hashlib
import json
import subprocess
import sys
import time
from pathlib import Path

root = Path(sys.argv[1])
out = Path(sys.argv[2])
out.mkdir(exist_ok=False)
started = time.monotonic()
records = []
cases = {"all_protected": None, "mixed_passing": 40,
         "mixed_failing": 1, "unprotected": 1}
for case, length in cases.items():
    design = ["module top(input clk,d,aux,output q0,q1,padout);"]
    protected = []
    if case != "unprotected":
        design += ["wire locked_out; BUF_X1 locked(.A(d),.Z(locked_out));",
                   "DFF_X1 keep0(.D(locked_out),.CK(clk),.Q(q0));"]
        protected += ["locked", "keep0"]
    else:
        design += ["assign q0=1'b0;"]
    if length is not None:
        previous = "d"
        for i in range(length):
            name = f"branch{i}"
            design += [f"wire b{i}; BUF_X1 {name}(.A({previous}),.Z(b{i}));"]
            previous = f"b{i}"
            if i and case != "unprotected":
                protected.append(name)
        design += [f"DFF_X1 keep1(.D({previous}),.CK(clk),.Q(q1));"]
        if case != "unprotected":
            protected.append("keep1")
    else:
        design += ["assign q1=1'b0;"]
    previous = "aux"
    for i in range(40):
        nxt = "padout" if i == 39 else f"p{i}"
        if i != 39:
            design.append(f"wire {nxt};")
        design.append(f"BUF_X1 pad{i}(.A({previous}),.Z({nxt}));")
        protected.append(f"pad{i}")
        previous = nxt
    design.append("endmodule")
    (out / f"{case}.v").write_text("\n".join(design) + "\n")
    for implementation in ["native", "original", "patched"]:
        folder = out / f"{case}-{implementation}"
        folder.mkdir()
        lines = []
        if implementation != "native":
            lines += [f"load {root}/native-02/{implementation}/libpinwheel_hold.so Pinwheelhold",
                      "rename rsz::repair_hold rsz::repair_hold_original",
                      "interp alias {} rsz::repair_hold {} pinwheel_repair_hold"]
        lines += [f"read_liberty {root}/source/test/Nangate45/Nangate45_typ.lib",
                  f"read_lef {root}/source/test/Nangate45/Nangate45.lef",
                  f"read_verilog {out}/{case}.v", "link_design top",
                  "initialize_floorplan -die_area {0 0 100 100} -core_area {1.9 1.4 98.8 98} -site FreePDK45_38x28_10R_NP_162NW_34O",
                  "set block [ord::get_db_block]", "set index 0",
                  "foreach inst [$block getInsts] {",
                  "  $inst setLocation [expr {10000+($index%15)*4000}] [expr {14000+($index/15)*2800}]",
                  "  $inst setOrient R0", "  $inst setPlacementStatus PLACED", "  incr index", "}",
                  "make_tracks", "set port_index 0",
                  "foreach port {clk d aux q0 q1 padout} {",
                  "  place_pin -pin_name $port -layer metal2 -location [list 0 [expr {10+10*$port_index}]] -pin_size {0.1 0.1}",
                  "  incr port_index", "}",
                  "detailed_placement -max_displacement {50 50}",
                  "create_clock -period 20 [get_ports clk]",
                  "set_input_delay -clock clk 0 [get_ports d]",
                  f"source {root}/source/test/Nangate45/Nangate45.rc",
                  "set_wire_rc -layer metal1", "estimate_parasitics -placement",
                  "set_dont_touch [get_cells {" + " ".join(protected) + "}]",
                  "proc snapshot {path} {",
                  "  set f [open $path w]",
                  "  foreach inst [[ord::get_db_block] getInsts] {",
                  "    puts $f [list instance [$inst getName] [[$inst getMaster] getName] [$inst getLocation] [$inst getOrient]]",
                  "    foreach pin [$inst getITerms] {",
                  "      set net [$pin getNet]",
                  "      if {$net ne \"NULL\"} {puts $f [list pin [$inst getName] [[$pin getMTerm] getName] [$net getName]]}",
                  "    }", "  }", "  close $f", "}",
                  f"snapshot {folder}/before.txt",
                  "puts {PINWHEEL_BEFORE}",
                  "report_checks -path_delay min -group_path_count 10 -digits 9",
                  "puts {PINWHEEL_REPAIR}",
                  "repair_timing -hold -hold_margin 0.2 -max_buffer_percent 100 -max_passes 50 -verbose",
                  "estimate_parasitics -placement", "puts {PINWHEEL_AFTER}",
                  "report_checks -path_delay min -group_path_count 10 -digits 9",
                  f"snapshot {folder}/after.txt", f"write_verilog {folder}/after.v", "exit"]
        script = folder / "run.tcl"
        script.write_text("\n".join(lines) + "\n")
        if time.monotonic() - started + 20 > 300:
            raise RuntimeError("Native regression campaign budget exhausted")
        t = time.monotonic()
        with (folder / "run.log").open("x") as log:
            proc = subprocess.run(["openroad", "-exit", "-threads", "1", str(script)],
                                  stdout=log, stderr=subprocess.STDOUT, timeout=20)
        record = dict(case=case, implementation=implementation, protected=protected,
                      returncode=proc.returncode, seconds=round(time.monotonic()-t, 3),
                      script_sha256=hashlib.sha256(script.read_bytes()).hexdigest())
        records.append(record)
        (out / "commands.json").write_text(json.dumps(records, indent=2)+"\n")
        print(case, implementation, proc.returncode, record["seconds"], flush=True)
