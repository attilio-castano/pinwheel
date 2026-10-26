# Isolated official8x4 PDN. The staged allocation is generated from exact DEF.
source [file join [file dirname [info script]] allocation.tcl]
set streaming8_block [ord::get_db_block]
if {[$streaming8_block getDbUnitsPerMicron] != 1000} {error "Wrong8x4 DBU scale"}
set streaming8_actual_die [$streaming8_block getDieArea]
set streaming8_methods {xMin yMin xMax yMax}
for {set k 0} {$k < 4} {incr k} {
    if {[$streaming8_actual_die [lindex $streaming8_methods $k]] != [lindex $streaming8_die $k]} {error "Wrong official8x4 die"}
}
set streaming8_core [$streaming8_block getCoreArea]
for {set k 0} {$k < 4} {incr k} {
    if {[$streaming8_core [lindex $streaming8_methods $k]] != [lindex $streaming8_core_bounds $k]} {error "Changed official8x4 core extent"}
}
if {$::env(PDN_VWIDTH) * 1000 != $streaming8_width} {error "Changed8x4 stripe width"}
set streaming8_seen {}
set streaming8_modes {}
foreach term [$streaming8_block getBTerms] {
    set kind [$term getSigType]
    if {$kind eq "POWER" || $kind eq "GROUND"} {
        foreach pin [$term getBPins] {
            if {[llength [$pin getBoxes]] != 0} {error "8x4 PDN requires a fresh grid"}
        }
        continue
    }
    set name [$term getName]
    if {![dict exists $streaming8_pins $name] || [dict exists $streaming8_seen $name]} {error "Unexpected8x4 public pin"}
    set expected_direction OUTPUT
    if {$name in {clk ena rst_n} || [string match {ui_in\[*} $name] || [string match {uio_in\[*} $name]} {set expected_direction INPUT}
    if {[$term getIoType] ne $expected_direction} {error "Changed8x4 public pin direction"}
    set pins [$term getBPins]
    set expected [dict get $streaming8_pins $name]
    if {[llength $pins] == 0} {
        dict set streaming8_modes unplaced 1
    } else {
        dict set streaming8_modes placed 1
        if {[llength $pins] != 1} {error "Wrong8x4 public BPin count"}
        set boxes [[lindex $pins 0] getBoxes]
        if {[llength $boxes] != 1} {error "Wrong8x4 public box count"}
        set box [lindex $boxes 0]
        if {[[$box getTechLayer] getName] ne "Metal4"} {error "Wrong8x4 public layer"}
        for {set k 0} {$k < 4} {incr k} {
            if {[$box [lindex $streaming8_methods $k]] != [lindex $expected $k]} {error "Wrong8x4 public rectangle"}
        }
    }
    dict set streaming8_seen $name 1
    for {set first $streaming8_first_center} {$first + $streaming8_pair_delta + $streaming8_width / 2 <= [lindex $streaming8_die 2]} {incr first $streaming8_pitch} {
        foreach x [list $first [expr {$first + $streaming8_pair_delta}]] {
            set gap [expr {max([lindex $expected 0] - ($x + $streaming8_width / 2), ($x - $streaming8_width / 2) - [lindex $expected 2])}]
            if {$gap < $streaming8_public_clearance} {error "8x4 power stripe overlaps public pin"}
        }
    }
}
if {[dict size $streaming8_seen] != 43 || [dict size $streaming8_modes] != 1} {error "Incomplete/mixed8x4 public pins"}
source $::env(SCRIPTS_DIR)/openroad/common/set_global_connections.tcl
set_global_connections
set_voltage_domain -name CORE -power $::env(VDD_NET) -ground $::env(GND_NET)
define_pdn_grid -name streaming8_stdcell_grid -starts_with POWER -voltage_domain CORE -pins {Metal4}
add_pdn_stripe -grid streaming8_stdcell_grid -layer Metal1 -width $::env(PDN_RAIL_WIDTH) -followpins
add_pdn_stripe -grid streaming8_stdcell_grid -layer Metal2 -width 1.0 -pitch $::env(PDN_VPITCH) -offset $::env(PDN_VOFFSET) -spacing $::env(PDN_VSPACING) -starts_with POWER
add_pdn_stripe -grid streaming8_stdcell_grid -layer Metal3 -width $::env(PDN_HWIDTH) -pitch $::env(PDN_HPITCH) -offset $::env(PDN_HOFFSET) -spacing $::env(PDN_HSPACING) -starts_with POWER
add_pdn_stripe -grid streaming8_stdcell_grid -layer Metal4 -width $::env(PDN_VWIDTH) -pitch [expr {$streaming8_pitch / 1000.0}] -offset [expr {($streaming8_first_center - [$streaming8_core xMin]) / 1000.0}] -spacing [expr {($streaming8_pair_delta - $streaming8_width) / 1000.0}] -starts_with POWER -extend_to_boundary
add_pdn_connect -grid streaming8_stdcell_grid -layers {Metal1 Metal2}
add_pdn_connect -grid streaming8_stdcell_grid -layers {Metal2 Metal3}
add_pdn_connect -grid streaming8_stdcell_grid -layers {Metal3 Metal4}
