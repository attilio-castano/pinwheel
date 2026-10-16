set block [ord::get_db_block]
foreach name {fanout913 fanout914} {
 set inst [$block findInst $name]
 if {[[$inst getMaster] getName] ne "sg13cmos5l_buf_1" || [$inst getOrient] ne "R180" || [$inst getPlacementStatus] ne "PLACED"} {error {Unexpected pair source cell}}
 set master [[ord::get_db] findMaster {sg13cmos5l_buf_4}]
 if {$master eq "NULL" || ![$inst swapMaster $master]} {error {Pair master swap failed}}
 $inst setOrient R180
 if {$name eq "fanout913"} {$inst setLocation 597120 378000} else {$inst setLocation 600960 378000}
}
check_placement -verbose
