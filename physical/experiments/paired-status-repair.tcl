puts "PINWHEEL_STATUS_BUFFER_REPAIR"
write_verilog /probe/before.v
set targets {_05626_ _05822_ _05886_}
set original_status {}
foreach inst [$::block getInsts] {
    lappend original_status $inst [$inst getPlacementStatus]
    if {[$inst getName] ni $targets && [$inst getPlacementStatus] eq "PLACED"} {
        $inst setPlacementStatus FIRM
    }
}
foreach name $targets {
    set inst [$::block findInst $name]
    if {$inst eq "NULL" || [[$inst getMaster] getName] ne "sg13cmos5l_buf_1"} {
        error "Unexpected status-path buffer: $name"
    }
    replace_cell $name sg13cmos5l_buf_4
}
detailed_placement -max_displacement {50 20}
check_placement -verbose
foreach {inst status} $original_status {$inst setPlacementStatus $status}
global_connect
write_verilog /probe/after.v
write_db /probe/repaired.odb
estimate_parasitics -placement
puts "PINWHEEL_STATUS_BUFFER_REPAIR_DONE"
