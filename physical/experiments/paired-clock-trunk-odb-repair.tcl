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
  # Direct database insertion avoids the pinned resizer's uninitialized DPL
  # post-insertion path. Normal legalization still checks the final geometry.
  set inst [odb::dbInst_create $::block [[ord::get_db] findMaster sg13cmos5l_buf_8] paired_clock_trunk_$index]
  set branch [odb::dbNet_create $::block paired_clock_branch_$index]
  $branch setSigType CLOCK
  [$inst findITerm A] connect [$::block findNet clknet_0_clk_regs]
  [$inst findITerm X] connect $branch
  foreach pin $loads {
    set terminal [$::block findITerm $pin]
    $terminal disconnect
    $terminal connect $branch
  }
  lassign $location x y
  $inst setLocation [expr {int($x * [$::block getDbUnitsPerMicron])}] [expr {int($y * [$::block getDbUnitsPerMicron])}]
  $inst setPlacementStatus PLACED
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
write_guide /probe/repaired.guide
write_verilog /probe/repaired.v
write_db /probe/repaired.odb
puts {PINWHEEL_LOCAL_CLOCK_TRUNK_REPAIR_DONE}
