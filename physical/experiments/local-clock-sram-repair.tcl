puts "PINWHEEL_ESTIMATION retained_global_routing"
write_verilog /probe/before.v
set original_instances [$::block getInsts]
set_layers_default_rc [lln::get_corner_names]
estimate_parasitics -global_routing
set targets {{memory.mem_q0[42]} {memory.mem_q0[37]} {memory.mem_q1[42]} {memory.mem_q0[44]} {memory.mem_q0[29]} {memory.mem_q0[47]} {memory.mem_q0[33]}}
set keep {}
foreach net [$::block getNets] {
    if {[$net getSigType] eq "SIGNAL" && [$net getName] ni $targets} {lappend keep [$net getName]}
}
set_dont_touch $keep
repair_design -max_wire_length 0 -slew_margin 10 -cap_margin 10 -verbose
unset_dont_touch $keep
write_verilog /probe/sram.v
write_db /probe/sram.odb
estimate_parasitics -placement
puts "PINWHEEL_CLOCK_SPLIT clkbuf_2_0_0_clk_regs"
set original [$::block findInst {clkbuf_2_0_0_clk_regs}]
set input_net [[$original findITerm A] getNet]
insert_buffer -buffer_cell sg13cmos5l_buf_8 -load_pins {{clkbuf_6_12_0_clk_regs/A} {clkbuf_6_13_0_clk_regs/A} {clkbuf_6_8_0_clk_regs/A} {clkbuf_6_9_0_clk_regs/A} {clkbuf_6_14_0_clk_regs/A} {clkbuf_6_15_0_clk_regs/A} {clkbuf_6_11_0_clk_regs/A} {clkbuf_6_10_0_clk_regs/A}} -location {324.0 317.52} -buffer_name local_clock_0 -net_name local_clock_net_0
set copies {}
foreach inst [$::block getInsts] {if {[string match local_clock_0* [$inst getName]]} {lappend copies $inst}}
if {[llength $copies] != 1} {error "Ambiguous inserted clock buffer"}
set copy [lindex $copies 0]
set copy_in [$copy findITerm A]
$copy_in disconnect
$copy_in connect $input_net
[[$copy findITerm X] getNet] setSigType CLOCK
puts "PINWHEEL_CLOCK_SPLIT clkbuf_2_1_0_clk_regs"
set original [$::block findInst {clkbuf_2_1_0_clk_regs}]
set input_net [[$original findITerm A] getNet]
insert_buffer -buffer_cell sg13cmos5l_buf_8 -load_pins {{clkbuf_6_29_0_clk_regs/A} {clkbuf_6_28_0_clk_regs/A} {clkbuf_6_24_0_clk_regs/A} {clkbuf_6_25_0_clk_regs/A} {clkbuf_6_26_0_clk_regs/A} {clkbuf_6_31_0_clk_regs/A} {clkbuf_6_27_0_clk_regs/A} {clkbuf_6_30_0_clk_regs/A}} -location {358.56 555.66} -buffer_name local_clock_1 -net_name local_clock_net_1
set copies {}
foreach inst [$::block getInsts] {if {[string match local_clock_1* [$inst getName]]} {lappend copies $inst}}
if {[llength $copies] != 1} {error "Ambiguous inserted clock buffer"}
set copy [lindex $copies 0]
set copy_in [$copy findITerm A]
$copy_in disconnect
$copy_in connect $input_net
[[$copy findITerm X] getNet] setSigType CLOCK
puts "PINWHEEL_CLOCK_SPLIT clkbuf_2_2_0_clk_regs"
set original [$::block findInst {clkbuf_2_2_0_clk_regs}]
set input_net [[$original findITerm A] getNet]
insert_buffer -buffer_cell sg13cmos5l_buf_8 -load_pins {{clkbuf_6_45_0_clk_regs/A} {clkbuf_6_40_0_clk_regs/A} {clkbuf_6_44_0_clk_regs/A} {clkbuf_6_41_0_clk_regs/A} {clkbuf_6_46_0_clk_regs/A} {clkbuf_6_43_0_clk_regs/A} {clkbuf_6_47_0_clk_regs/A} {clkbuf_6_42_0_clk_regs/A}} -location {1000.8 272.16} -buffer_name local_clock_2 -net_name local_clock_net_2
set copies {}
foreach inst [$::block getInsts] {if {[string match local_clock_2* [$inst getName]]} {lappend copies $inst}}
if {[llength $copies] != 1} {error "Ambiguous inserted clock buffer"}
set copy [lindex $copies 0]
set copy_in [$copy findITerm A]
$copy_in disconnect
$copy_in connect $input_net
[[$copy findITerm X] getNet] setSigType CLOCK
puts "PINWHEEL_CLOCK_SPLIT clkbuf_2_3_0_clk_regs"
set original [$::block findInst {clkbuf_2_3_0_clk_regs}]
set input_net [[$original findITerm A] getNet]
insert_buffer -buffer_cell sg13cmos5l_buf_8 -load_pins {{clkbuf_6_60_0_clk_regs/A} {clkbuf_6_61_0_clk_regs/A} {clkbuf_6_56_0_clk_regs/A} {clkbuf_6_57_0_clk_regs/A} {clkbuf_6_63_0_clk_regs/A} {clkbuf_6_59_0_clk_regs/A} {clkbuf_6_62_0_clk_regs/A} {clkbuf_6_58_0_clk_regs/A}} -location {947.04 544.32} -buffer_name local_clock_3 -net_name local_clock_net_3
set copies {}
foreach inst [$::block getInsts] {if {[string match local_clock_3* [$inst getName]]} {lappend copies $inst}}
if {[llength $copies] != 1} {error "Ambiguous inserted clock buffer"}
set copy [lindex $copies 0]
set copy_in [$copy findITerm A]
$copy_in disconnect
$copy_in connect $input_net
[[$copy findITerm X] getNet] setSigType CLOCK
write_verilog /probe/changed.v
puts "PINWHEEL_LEGALIZE_LOCAL"
set prior_status {}
foreach inst $original_instances {
    lappend prior_status $inst [$inst getPlacementStatus]
    if {[$inst getPlacementStatus] eq "PLACED"} {$inst setPlacementStatus FIRM}
}
detailed_placement -max_displacement {500 100}
check_placement -verbose
foreach {inst status} $prior_status {$inst setPlacementStatus $status}
global_connect
write_verilog /probe/after.v
write_db /probe/repaired.odb
puts "PINWHEEL_ESTIMATION placement"
estimate_parasitics -placement
puts "PINWHEEL_LOCAL_REPAIR_DONE"
