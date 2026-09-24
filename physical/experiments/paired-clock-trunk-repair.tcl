# One controlled change: divide the long eight-load register-clock trunk into
# four spatial pairs. Retain every existing cell, location and logic connection.
# Incremental coarse routing updates the affected wires before any measurement.
write_verilog /probe/before.v
set originals [$::block getInsts]
set_routing_layers -signal Metal2-Metal4 -clock Metal2-Metal4
set_global_routing_layer_adjustment * 0.3
global_route -start_incremental

set pairs {
  {0 {485.0 400.0} {clkbuf_3_0_0_clk_regs/A clkbuf_3_1_0_clk_regs/A}}
  {1 {500.0 490.0} {clkbuf_3_2_0_clk_regs/A clkbuf_3_3_0_clk_regs/A}}
  {2 {815.0 400.0} {clkbuf_3_4_0_clk_regs/A clkbuf_3_5_0_clk_regs/A}}
  {3 {800.0 475.0} {clkbuf_3_6_0_clk_regs/A clkbuf_3_7_0_clk_regs/A}}
}
foreach pair $pairs {
  lassign $pair index location loads
  foreach pin $loads {
    set terminal [$::block findITerm $pin]
    if {$terminal eq "NULL" || [[$terminal getNet] getName] ne "clknet_0_clk_regs"} {
      error "Unexpected clock trunk connection: $pin"
    }
  }
  insert_buffer -buffer_cell sg13cmos5l_buf_8 -load_pins $loads \
    -location $location -buffer_name paired_clock_trunk_$index \
    -net_name paired_clock_branch_$index
  [$::block findNet paired_clock_branch_$index] setSigType CLOCK
}

set statuses {}
foreach inst $originals {
  lappend statuses $inst [$inst getPlacementStatus]
  if {[$inst getPlacementStatus] eq "PLACED"} {$inst setPlacementStatus FIRM}
}
detailed_placement -max_displacement {50 20}
check_placement -verbose
foreach {inst status} $statuses {$inst setPlacementStatus $status}
global_connect
global_route -end_incremental -allow_congestion
estimate_parasitics -global_routing
write_guides /probe/repaired.guide
write_verilog /probe/repaired.v
write_db /probe/repaired.odb
puts {PINWHEEL_LOCAL_CLOCK_TRUNK_REPAIR_DONE}
