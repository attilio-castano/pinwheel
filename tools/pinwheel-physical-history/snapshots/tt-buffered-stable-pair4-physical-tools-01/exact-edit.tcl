set block [ord::get_db_block]
set inst [$block findInst {fanout1946}]
if {[[$inst getMaster] getName] ne {sg13cmos5l_buf_1}} {error {Unexpected resize source}}
set master [[ord::get_db] findMaster {sg13cmos5l_buf_4}]
if {$master eq "NULL" || ![$inst swapMaster $master]} {error {Exact master swap failed}}
$inst setOrient MY
$inst setLocation 608640 366660
set inst [$block findInst {_18965_}]
if {[[$inst getMaster] getName] ne {sg13cmos5l_or3_1}} {error {Unexpected resize source}}
set master [[ord::get_db] findMaster {sg13cmos5l_or3_2}]
if {$master eq "NULL" || ![$inst swapMaster $master]} {error {Exact master swap failed}}
$inst setOrient R0
$inst setLocation 770400 11340
if {[$block findInst {timing_eco_hold_30685}] ne "NULL" || [$block findNet {timing_eco_hold_30685_D}] ne "NULL"} {error {ECO name collision}}
set buffer [odb::dbInst_create $block [[ord::get_db] findMaster {sg13cmos5l_dlygate4sd3_1}] {timing_eco_hold_30685}]
set branch [odb::dbNet_create $block {timing_eco_hold_30685_D}]
$buffer setOrient R0
$buffer setLocation 532800 245700
$buffer setPlacementStatus PLACED
set source [$block findNet {net7995}]
set sink [[$block findInst {_30685_}] findITerm D]
if {[$sink getNet] ne $source} {error {Unexpected terminal D source}}
[$buffer findITerm A] connect $source
[$buffer findITerm X] connect $branch
[$buffer findITerm VDD] connect [$block findNet VPWR]
[$buffer findITerm VSS] connect [$block findNet VGND]
$sink disconnect
$sink connect $branch
if {[$block findInst {timing_eco_hold_30753}] ne "NULL" || [$block findNet {timing_eco_hold_30753_D}] ne "NULL"} {error {ECO name collision}}
set buffer [odb::dbInst_create $block [[ord::get_db] findMaster {sg13cmos5l_dlygate4sd3_1}] {timing_eco_hold_30753}]
set branch [odb::dbNet_create $block {timing_eco_hold_30753_D}]
$buffer setOrient MX
$buffer setLocation 262560 219240
$buffer setPlacementStatus PLACED
set source [$block findNet {net8056}]
set sink [[$block findInst {_30753_}] findITerm D]
if {[$sink getNet] ne $source} {error {Unexpected terminal D source}}
[$buffer findITerm A] connect $source
[$buffer findITerm X] connect $branch
[$buffer findITerm VDD] connect [$block findNet VPWR]
[$buffer findITerm VSS] connect [$block findNet VGND]
$sink disconnect
$sink connect $branch
if {[$block findInst {timing_eco_hold_30779}] ne "NULL" || [$block findNet {timing_eco_hold_30779_D}] ne "NULL"} {error {ECO name collision}}
set buffer [odb::dbInst_create $block [[ord::get_db] findMaster {sg13cmos5l_dlygate4sd3_1}] {timing_eco_hold_30779}]
set branch [odb::dbNet_create $block {timing_eco_hold_30779_D}]
$buffer setOrient R0
$buffer setLocation 181440 313740
$buffer setPlacementStatus PLACED
set source [$block findNet {_03283_}]
set sink [[$block findInst {_30779_}] findITerm D]
if {[$sink getNet] ne $source} {error {Unexpected terminal D source}}
[$buffer findITerm A] connect $source
[$buffer findITerm X] connect $branch
[$buffer findITerm VDD] connect [$block findNet VPWR]
[$buffer findITerm VSS] connect [$block findNet VGND]
$sink disconnect
$sink connect $branch
if {[$block findInst {timing_eco_hold_30684}] ne "NULL" || [$block findNet {timing_eco_hold_30684_D}] ne "NULL"} {error {ECO name collision}}
set buffer [odb::dbInst_create $block [[ord::get_db] findMaster {sg13cmos5l_dlygate4sd3_1}] {timing_eco_hold_30684}]
set branch [odb::dbNet_create $block {timing_eco_hold_30684_D}]
$buffer setOrient MX
$buffer setLocation 463680 241920
$buffer setPlacementStatus PLACED
set source [$block findNet {net7998}]
set sink [[$block findInst {_30684_}] findITerm D]
if {[$sink getNet] ne $source} {error {Unexpected terminal D source}}
[$buffer findITerm A] connect $source
[$buffer findITerm X] connect $branch
[$buffer findITerm VDD] connect [$block findNet VPWR]
[$buffer findITerm VSS] connect [$block findNet VGND]
$sink disconnect
$sink connect $branch
if {[$block findInst {timing_eco_hold_30686}] ne "NULL" || [$block findNet {timing_eco_hold_30686_D}] ne "NULL"} {error {ECO name collision}}
set buffer [odb::dbInst_create $block [[ord::get_db] findMaster {sg13cmos5l_dlygate4sd3_1}] {timing_eco_hold_30686}]
set branch [odb::dbNet_create $block {timing_eco_hold_30686_D}]
$buffer setOrient MX
$buffer setLocation 458400 257040
$buffer setPlacementStatus PLACED
set source [$block findNet {net7992}]
set sink [[$block findInst {_30686_}] findITerm D]
if {[$sink getNet] ne $source} {error {Unexpected terminal D source}}
[$buffer findITerm A] connect $source
[$buffer findITerm X] connect $branch
[$buffer findITerm VDD] connect [$block findNet VPWR]
[$buffer findITerm VSS] connect [$block findNet VGND]
$sink disconnect
$sink connect $branch
if {[$block findInst {timing_eco_hold_30712}] ne "NULL" || [$block findNet {timing_eco_hold_30712_D}] ne "NULL"} {error {ECO name collision}}
set buffer [odb::dbInst_create $block [[ord::get_db] findMaster {sg13cmos5l_dlygate4sd3_1}] {timing_eco_hold_30712}]
set branch [odb::dbNet_create $block {timing_eco_hold_30712_D}]
$buffer setOrient R0
$buffer setLocation 358560 291060
$buffer setPlacementStatus PLACED
set source [$block findNet {_03216_}]
set sink [[$block findInst {_30712_}] findITerm D]
if {[$sink getNet] ne $source} {error {Unexpected terminal D source}}
[$buffer findITerm A] connect $source
[$buffer findITerm X] connect $branch
[$buffer findITerm VDD] connect [$block findNet VPWR]
[$buffer findITerm VSS] connect [$block findNet VGND]
$sink disconnect
$sink connect $branch
if {[$block findInst {timing_eco_hold_30617}] ne "NULL" || [$block findNet {timing_eco_hold_30617_D}] ne "NULL"} {error {ECO name collision}}
set buffer [odb::dbInst_create $block [[ord::get_db] findMaster {sg13cmos5l_dlygate4sd3_1}] {timing_eco_hold_30617}]
set branch [odb::dbNet_create $block {timing_eco_hold_30617_D}]
$buffer setOrient R0
$buffer setLocation 533280 291060
$buffer setPlacementStatus PLACED
set source [$block findNet {net8072}]
set sink [[$block findInst {_30617_}] findITerm D]
if {[$sink getNet] ne $source} {error {Unexpected terminal D source}}
[$buffer findITerm A] connect $source
[$buffer findITerm X] connect $branch
[$buffer findITerm VDD] connect [$block findNet VPWR]
[$buffer findITerm VSS] connect [$block findNet VGND]
$sink disconnect
$sink connect $branch
if {[$block findInst {timing_eco_hold_30616}] ne "NULL" || [$block findNet {timing_eco_hold_30616_D}] ne "NULL"} {error {ECO name collision}}
set buffer [odb::dbInst_create $block [[ord::get_db] findMaster {sg13cmos5l_dlygate4sd3_1}] {timing_eco_hold_30616}]
set branch [odb::dbNet_create $block {timing_eco_hold_30616_D}]
$buffer setOrient MX
$buffer setLocation 511200 287280
$buffer setPlacementStatus PLACED
set source [$block findNet {net8088}]
set sink [[$block findInst {_30616_}] findITerm D]
if {[$sink getNet] ne $source} {error {Unexpected terminal D source}}
[$buffer findITerm A] connect $source
[$buffer findITerm X] connect $branch
[$buffer findITerm VDD] connect [$block findNet VPWR]
[$buffer findITerm VSS] connect [$block findNet VGND]
$sink disconnect
$sink connect $branch
check_placement -verbose
