# Exact organization experiment; no clock or state edits.
write_verilog /probe/before.v
set_routing_layers -signal Metal2-Metal4 -clock Metal2-Metal4
set_global_routing_layer_adjustment * 0.3
global_route -start_incremental
set wire [$::block findNet {_02967_}]
if {$wire eq "NULL" || [$wire getSigType] ne "SIGNAL"} {error "Missing signal source"}
set actual {}
foreach it [$wire getITerms] {lappend actual "[[$it getInst] getName]/[[$it getMTerm] getName]"}
if {[lsort $actual] ne [lsort [list {_06782_/X} {_06786_/S0} {_06787_/S0} {_06800_/S0} {_07027_/S0} {_07047_/S0} {_07160_/S0} {_07292_/B1} {_07295_/B1}]]} {error "Changed source consumers"}
if {[llength [$wire getBTerms]] != 0} {error "Unexpected package branch"}
set wire [$::block findNet {_02981_}]
if {$wire eq "NULL" || [$wire getSigType] ne "SIGNAL"} {error "Missing signal source"}
set actual {}
foreach it [$wire getITerms] {lappend actual "[[$it getInst] getName]/[[$it getMTerm] getName]"}
if {[lsort $actual] ne [lsort [list {_06796_/X} {_06799_/S0} {_06870_/A} {_06987_/S0} {_07037_/S0} {_07059_/S0} {_07094_/S0} {_07557_/S0} {_07558_/S0}]]} {error "Changed source consumers"}
if {[llength [$wire getBTerms]] != 0} {error "Unexpected package branch"}
set wire [$::block findNet {_03010_}]
if {$wire eq "NULL" || [$wire getSigType] ne "SIGNAL"} {error "Missing signal source"}
set actual {}
foreach it [$wire getITerms] {lappend actual "[[$it getInst] getName]/[[$it getMTerm] getName]"}
if {[lsort $actual] ne [lsort [list {_06825_/X} {_06829_/S0} {_06842_/S0} {_06902_/S0} {_06991_/S0} {_07224_/A1} {_07471_/S0} {_07476_/S0} {_07714_/S0}]]} {error "Changed source consumers"}
if {[llength [$wire getBTerms]] != 0} {error "Unexpected package branch"}
set wire [$::block findNet {_03037_}]
if {$wire eq "NULL" || [$wire getSigType] ne "SIGNAL"} {error "Missing signal source"}
set actual {}
foreach it [$wire getITerms] {lappend actual "[[$it getInst] getName]/[[$it getMTerm] getName]"}
if {[lsort $actual] ne [lsort [list {_06852_/X} {_06855_/S0} {_07247_/B1} {_07251_/A1} {_07260_/A1} {_07482_/S0} {_07546_/S0} {_07555_/S0} {_07974_/B1}]]} {error "Changed source consumers"}
if {[llength [$wire getBTerms]] != 0} {error "Unexpected package branch"}
set wire [$::block findNet {_03121_}]
if {$wire eq "NULL" || [$wire getSigType] ne "SIGNAL"} {error "Missing signal source"}
set actual {}
foreach it [$wire getITerms] {lappend actual "[[$it getInst] getName]/[[$it getMTerm] getName]"}
if {[lsort $actual] ne [lsort [list {_06936_/X} {_06938_/S0} {_07052_/S0} {_07083_/A} {_07170_/S0} {_07668_/S0} {_07684_/S0} {_07685_/S0} {_07780_/S0}]]} {error "Changed source consumers"}
if {[llength [$wire getBTerms]] != 0} {error "Unexpected package branch"}
set wire [$::block findNet {_03168_}]
if {$wire eq "NULL" || [$wire getSigType] ne "SIGNAL"} {error "Missing signal source"}
set actual {}
foreach it [$wire getITerms] {lappend actual "[[$it getInst] getName]/[[$it getMTerm] getName]"}
if {[lsort $actual] ne [lsort [list {_06983_/X} {_06985_/S0} {_07377_/A} {_07505_/S0} {_07562_/S0} {_07712_/S0} {_07734_/S0} {_07736_/S0} {_07744_/S0}]]} {error "Changed source consumers"}
if {[llength [$wire getBTerms]] != 0} {error "Unexpected package branch"}
set wire [$::block findNet {_03183_}]
if {$wire eq "NULL" || [$wire getSigType] ne "SIGNAL"} {error "Missing signal source"}
set actual {}
foreach it [$wire getITerms] {lappend actual "[[$it getInst] getName]/[[$it getMTerm] getName]"}
if {[lsort $actual] ne [lsort [list {_06998_/X} {_06999_/S0} {_07010_/S0} {_07022_/S0} {_07223_/B1} {_07225_/B1} {_07321_/B1} {_07335_/B1} {_07536_/S0}]]} {error "Changed source consumers"}
if {[llength [$wire getBTerms]] != 0} {error "Unexpected package branch"}
set wire [$::block findNet {_03253_}]
if {$wire eq "NULL" || [$wire getSigType] ne "SIGNAL"} {error "Missing signal source"}
set actual {}
foreach it [$wire getITerms] {lappend actual "[[$it getInst] getName]/[[$it getMTerm] getName]"}
if {[lsort $actual] ne [lsort [list {_07068_/X} {_07070_/S0} {_07206_/S0} {_07499_/S0} {_07521_/S0} {_07530_/S0} {_07700_/S0} {_07762_/S0} {_07787_/S0}]]} {error "Changed source consumers"}
if {[llength [$wire getBTerms]] != 0} {error "Unexpected package branch"}
set wire [$::block findNet {_03268_}]
if {$wire eq "NULL" || [$wire getSigType] ne "SIGNAL"} {error "Missing signal source"}
set actual {}
foreach it [$wire getITerms] {lappend actual "[[$it getInst] getName]/[[$it getMTerm] getName]"}
if {[lsort $actual] ne [lsort [list {_07083_/X} {_07084_/A} {_07240_/B1} {_07325_/B1} {_07540_/S0} {_07710_/S0} {_07727_/S0} {_07767_/S0} {_07773_/S0}]]} {error "Changed source consumers"}
if {[llength [$wire getBTerms]] != 0} {error "Unexpected package branch"}
set wire [$::block findNet {_03380_}]
if {$wire eq "NULL" || [$wire getSigType] ne "SIGNAL"} {error "Missing signal source"}
set actual {}
foreach it [$wire getITerms] {lappend actual "[[$it getInst] getName]/[[$it getMTerm] getName]"}
if {[lsort $actual] ne [lsort [list {_07195_/X} {_07196_/S0} {_07511_/S0} {_07629_/S0} {_07678_/S0} {_07745_/S0} {_07761_/S0} {_07763_/S0} {_07764_/S0}]]} {error "Changed source consumers"}
if {[llength [$wire getBTerms]] != 0} {error "Unexpected package branch"}
set wire [$::block findNet {_04527_}]
if {$wire eq "NULL" || [$wire getSigType] ne "SIGNAL"} {error "Missing signal source"}
set actual {}
foreach it [$wire getITerms] {lappend actual "[[$it getInst] getName]/[[$it getMTerm] getName]"}
if {[lsort $actual] ne [lsort [list {_08797_/X} {_08798_/S} {_08799_/B} {_08800_/A2} {_08801_/B} {_08802_/A2} {_08809_/B} {_08810_/A2} {_08826_/S}]]} {error "Changed source consumers"}
if {[llength [$wire getBTerms]] != 0} {error "Unexpected package branch"}
set wire [$::block findNet {_04701_}]
if {$wire eq "NULL" || [$wire getSigType] ne "SIGNAL"} {error "Missing signal source"}
set actual {}
foreach it [$wire getITerms] {lappend actual "[[$it getInst] getName]/[[$it getMTerm] getName]"}
if {[lsort $actual] ne [lsort [list {_09463_/X} {_09464_/S} {_09468_/S} {_09469_/S} {_09470_/S} {_09472_/S} {_09473_/S} {_09474_/S} {_10664_/S}]]} {error "Changed source consumers"}
if {[llength [$wire getBTerms]] != 0} {error "Unexpected package branch"}
set wire [$::block findNet {net31}]
if {$wire eq "NULL" || [$wire getSigType] ne "SIGNAL"} {error "Missing signal source"}
set actual {}
foreach it [$wire getITerms] {lappend actual "[[$it getInst] getName]/[[$it getMTerm] getName]"}
if {[lsort $actual] ne [lsort [list {wire31/X} {_06736_/A} {memory.storage/A_DIN[14]}]]} {error "Changed source consumers"}
if {[llength [$wire getBTerms]] != 0} {error "Unexpected package branch"}
set inst [$::block findInst {_08797_}]
if {[[$inst getMaster] getName] ne {sg13cmos5l_buf_1}} {error "Changed resize source"}
replace_cell {_08797_} sg13cmos5l_buf_2
$inst setOrient R0
$inst setLocation 316800 487620
set inst [$::block findInst {_09463_}]
if {[[$inst getMaster] getName] ne {sg13cmos5l_buf_1}} {error "Changed resize source"}
replace_cell {_09463_} sg13cmos5l_buf_2
$inst setOrient MX
$inst setLocation 1114560 438480
set it [$::block findITerm {_06799_/S0}]
$it disconnect
$it connect [$::block findNet {_02967_}]
set it [$::block findITerm {_07557_/S0}]
$it disconnect
$it connect [$::block findNet {_02967_}]
set it [$::block findITerm {_07047_/S0}]
$it disconnect
$it connect [$::block findNet {_02981_}]
set it [$::block findITerm {_07070_/S0}]
$it disconnect
$it connect [$::block findNet {_02981_}]
set it [$::block findITerm {_07482_/S0}]
$it disconnect
$it connect [$::block findNet {_02981_}]
set it [$::block findITerm {_07499_/S0}]
$it disconnect
$it connect [$::block findNet {_02981_}]
set it [$::block findITerm {_07530_/S0}]
$it disconnect
$it connect [$::block findNet {_02981_}]
set it [$::block findITerm {_07629_/S0}]
$it disconnect
$it connect [$::block findNet {_03010_}]
set it [$::block findITerm {_07558_/S0}]
$it disconnect
$it connect [$::block findNet {_03037_}]
set it [$::block findITerm {_06987_/S0}]
$it disconnect
$it connect [$::block findNet {_03121_}]
set it [$::block findITerm {_07521_/S0}]
$it disconnect
$it connect [$::block findNet {_03121_}]
set it [$::block findITerm {_07037_/S0}]
$it disconnect
$it connect [$::block findNet {_03168_}]
set it [$::block findITerm {_07511_/S0}]
$it disconnect
$it connect [$::block findNet {_03183_}]
set it [$::block findITerm {_07170_/S0}]
$it disconnect
$it connect [$::block findNet {_03253_}]
set it [$::block findITerm {_07684_/S0}]
$it disconnect
$it connect [$::block findNet {_03253_}]
set it [$::block findITerm {_07761_/S0}]
$it disconnect
$it connect [$::block findNet {_03253_}]
set it [$::block findITerm {_07764_/S0}]
$it disconnect
$it connect [$::block findNet {_03253_}]
set it [$::block findITerm {_07773_/S0}]
$it disconnect
$it connect [$::block findNet {_03253_}]
set it [$::block findITerm {_07536_/S0}]
$it disconnect
$it connect [$::block findNet {_03268_}]
set it [$::block findITerm {_07027_/S0}]
$it disconnect
$it connect [$::block findNet {_03380_}]
set it [$::block findITerm {_07700_/S0}]
$it disconnect
$it connect [$::block findNet {_03380_}]
set it [$::block findITerm {_07712_/S0}]
$it disconnect
$it connect [$::block findNet {_03380_}]
set it [$::block findITerm {_07714_/S0}]
$it disconnect
$it connect [$::block findNet {_03380_}]
if {[$::block findInst {paired_locality_receiver_14}] ne "NULL" || [$::block findNet {paired_locality_receiver_14_net}] ne "NULL"} {error "Receiver name collision"}
set inst [odb::dbInst_create $::block [[ord::get_db] findMaster sg13cmos5l_buf_1] {paired_locality_receiver_14}]
odb::dbNet_create $::block {paired_locality_receiver_14_net}
$inst setOrient R0
$inst setLocation 410400 109620
$inst setPlacementStatus PLACED
[$inst findITerm A] connect [$::block findNet {net31}]
[$inst findITerm X] connect [$::block findNet {paired_locality_receiver_14_net}]
set it [$::block findITerm {memory.storage/A_DIN[14]}]
$it disconnect
$it connect [$::block findNet {paired_locality_receiver_14_net}]
check_placement -verbose
global_connect
global_route -end_incremental -allow_congestion
estimate_parasitics -global_routing
write_guide /probe/repaired.guide
write_verilog /probe/repaired.v
write_db /probe/repaired.odb
