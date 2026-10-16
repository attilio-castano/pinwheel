set block [ord::get_db_block]
if {[$block findInst {timing_eco_terminal_30759}] ne "NULL" || [$block findNet {timing_eco_terminal_30759_D}] ne "NULL"} {error {Terminal name collision}}
set buffer [odb::dbInst_create $block [[ord::get_db] findMaster {sg13cmos5l_buf_1}] {timing_eco_terminal_30759}]
set branch [odb::dbNet_create $block {timing_eco_terminal_30759_D}]
$buffer setOrient MX
$buffer setLocation 363360 279720
$buffer setPlacementStatus PLACED
set source [$block findNet {net8042}]
set sink [[$block findInst {_30759_}] findITerm D]
if {[$sink getNet] ne $source} {error {Unexpected terminal D source}}
[$buffer findITerm A] connect $source
[$buffer findITerm X] connect $branch
[$buffer findITerm VDD] connect [$block findNet VPWR]
[$buffer findITerm VSS] connect [$block findNet VGND]
$sink disconnect
$sink connect $branch
if {[$block findInst {timing_eco_terminal_30606}] ne "NULL" || [$block findNet {timing_eco_terminal_30606_D}] ne "NULL"} {error {Terminal name collision}}
set buffer [odb::dbInst_create $block [[ord::get_db] findMaster {sg13cmos5l_buf_1}] {timing_eco_terminal_30606}]
set branch [odb::dbNet_create $block {timing_eco_terminal_30606_D}]
$buffer setOrient MX
$buffer setLocation 344160 294840
$buffer setPlacementStatus PLACED
set source [$block findNet {net8046}]
set sink [[$block findInst {_30606_}] findITerm D]
if {[$sink getNet] ne $source} {error {Unexpected terminal D source}}
[$buffer findITerm A] connect $source
[$buffer findITerm X] connect $branch
[$buffer findITerm VDD] connect [$block findNet VPWR]
[$buffer findITerm VSS] connect [$block findNet VGND]
$sink disconnect
$sink connect $branch
if {[$block findInst {timing_eco_terminal_30747}] ne "NULL" || [$block findNet {timing_eco_terminal_30747_D}] ne "NULL"} {error {Terminal name collision}}
set buffer [odb::dbInst_create $block [[ord::get_db] findMaster {sg13cmos5l_buf_1}] {timing_eco_terminal_30747}]
set branch [odb::dbNet_create $block {timing_eco_terminal_30747_D}]
$buffer setOrient R0
$buffer setLocation 364320 260820
$buffer setPlacementStatus PLACED
set source [$block findNet {net9291}]
set sink [[$block findInst {_30747_}] findITerm D]
if {[$sink getNet] ne $source} {error {Unexpected terminal D source}}
[$buffer findITerm A] connect $source
[$buffer findITerm X] connect $branch
[$buffer findITerm VDD] connect [$block findNet VPWR]
[$buffer findITerm VSS] connect [$block findNet VGND]
$sink disconnect
$sink connect $branch
if {[$block findInst {timing_eco_terminal_30602}] ne "NULL" || [$block findNet {timing_eco_terminal_30602_D}] ne "NULL"} {error {Terminal name collision}}
set buffer [odb::dbInst_create $block [[ord::get_db] findMaster {sg13cmos5l_buf_1}] {timing_eco_terminal_30602}]
set branch [odb::dbNet_create $block {timing_eco_terminal_30602_D}]
$buffer setOrient MX
$buffer setLocation 236640 332640
$buffer setPlacementStatus PLACED
set source [$block findNet {_00006_}]
set sink [[$block findInst {_30602_}] findITerm D]
if {[$sink getNet] ne $source} {error {Unexpected terminal D source}}
[$buffer findITerm A] connect $source
[$buffer findITerm X] connect $branch
[$buffer findITerm VDD] connect [$block findNet VPWR]
[$buffer findITerm VSS] connect [$block findNet VGND]
$sink disconnect
$sink connect $branch
if {[$block findInst {timing_eco_terminal_34083}] ne "NULL" || [$block findNet {timing_eco_terminal_34083_D}] ne "NULL"} {error {Terminal name collision}}
set buffer [odb::dbInst_create $block [[ord::get_db] findMaster {sg13cmos5l_buf_1}] {timing_eco_terminal_34083}]
set branch [odb::dbNet_create $block {timing_eco_terminal_34083_D}]
$buffer setOrient MX
$buffer setLocation 245760 325080
$buffer setPlacementStatus PLACED
set source [$block findNet {_03109_}]
set sink [[$block findInst {_34083_}] findITerm D]
if {[$sink getNet] ne $source} {error {Unexpected terminal D source}}
[$buffer findITerm A] connect $source
[$buffer findITerm X] connect $branch
[$buffer findITerm VDD] connect [$block findNet VPWR]
[$buffer findITerm VSS] connect [$block findNet VGND]
$sink disconnect
$sink connect $branch
check_placement -verbose
