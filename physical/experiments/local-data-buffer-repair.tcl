write_verilog /probe/before.v
set original_instances [$::block getInsts]
set original_names {}
foreach inst $original_instances {lappend original_names [$inst getName]}
set protected_drivers {_07997_ _07999_ _08080_ _08316_ _08340_ _08361_ _08389_ _08410_ _08522_ _08543_ _08570_ _08588_ _08612_ _08690_ _09048_ _09052_ _09056_ _09060_ _09593_ hold3395 hold3409 hold3419 hold3428 hold3439 hold3440 hold3456 hold3466 hold3470 wire15}
set_dont_touch $protected_drivers
set target_nets {{_00429_} {_01006_} {_01293_} {_01297_} {_01301_} {_01305_} {_01806_} {memory.mem_addr0[0]} {memory.mem_addr0[1]} {memory.mem_addr0[2]} {memory.mem_addr0[3]} {memory.mem_addr0[4]} {memory.mem_addr1[0]} {memory.mem_addr1[1]} {memory.mem_addr1[2]} {memory.mem_addr1[3]} {memory.mem_addr1[4]} {memory.mem_read} {memory.mem_write} {net15} {net3395} {net3409} {net3419} {net3428} {net3439} {net3440} {net3456} {net3466} {net3470}}
set protected_nets {}
foreach net [$::block getNets] {
  if {[$net getSigType] eq "SIGNAL" && [$net getName] ni $target_nets} {lappend protected_nets [$net getName]}
}
set_dont_touch $protected_nets
puts {PINWHEEL_REPAIR_29_DATA_NETS}
repair_design -max_wire_length 0 -slew_margin 10 -cap_margin 10 -verbose
unset_dont_touch $protected_nets
unset_dont_touch $protected_drivers
write_verilog /probe/changed.v
estimate_parasitics -placement
set prior_status {}
foreach inst $original_instances {
  lappend prior_status $inst [$inst getPlacementStatus]
  if {[$inst getPlacementStatus] eq "PLACED"} {$inst setPlacementStatus FIRM}
}
detailed_placement -max_displacement {500 100}
check_placement -verbose
foreach {inst status} $prior_status {$inst setPlacementStatus $status}
global_connect
write_verilog /probe/repaired.v
write_db /probe/repaired.odb
estimate_parasitics -placement
puts {PINWHEEL_ESTIMATION placement}
puts {PINWHEEL_LOCAL_DATA_REPAIR_DONE}
