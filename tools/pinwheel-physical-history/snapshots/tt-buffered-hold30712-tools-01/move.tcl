set block [ord::get_db_block]
set inst [$block findInst {timing_eco_hold_30712}]
if {[$inst getOrient] ne "R0" || [[$inst getMaster] getName] ne "sg13cmos5l_dlygate4sd3_1"} {error {Unexpected30712source}}
$inst setOrient MX
$inst setLocation 346080 294840
check_placement -verbose
