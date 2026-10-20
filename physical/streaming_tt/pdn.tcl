# Standard-cell-only TT grid. TopMetal1 is reserved by the parent chip.
# The fixed 43 public pins occupy Metal4 at the north edge.  A phase change
# alone cannot clear both members of the former 2.1/3.52/50 um strap pattern.
# Use a 7.68 um pair-center separation (two public-pin pitches) instead.
# These integer DBU constants are also checked by streaming_tt_pdn_geometry.py.
set streaming_pdn_m4_width_dbu 2100
set streaming_pdn_m4_pitch_dbu 50000
set streaming_pdn_m4_first_center_dbu 16160
set streaming_pdn_m4_pair_delta_dbu 7680
set streaming_pdn_public_clearance_dbu 600

# Fail before generating any grid if the floorplan differs from the admitted
# template. Classic applies the DEF pin template after PDN generation, so all
# public pins may still be unplaced here. In that case test their hash-bound
# future template positions; reject mixed placement or any placed mismatch.
# This is a geometric admission guard, not routed DRC or PG signoff.
set streaming_pdn_block [ord::get_db_block]
if {[$streaming_pdn_block getDbUnitsPerMicron] != 1000} {
    error "Streaming PDN requires exact 1000 DBU/um geometry"
}
set streaming_pdn_die [$streaming_pdn_block getDieArea]
if {[$streaming_pdn_die xMin] != 0 || [$streaming_pdn_die yMin] != 0 ||
    [$streaming_pdn_die xMax] != 1289280 || [$streaming_pdn_die yMax] != 710640} {
    error "Streaming PDN requires the official 6x4 die"
}
set streaming_pdn_core [$streaming_pdn_block getCoreArea]
if {[$streaming_pdn_core xMin] != 2880} {
    error "Streaming PDN core origin changed"
}
if {![info exists ::env(PDN_VWIDTH)] || $::env(PDN_VWIDTH) * 1000 != $streaming_pdn_m4_width_dbu} {
    error "Streaming PDN configured Metal4 width differs from admitted geometry"
}
set streaming_pdn_expected_x [dict create clk 187200 ena 191040 rst_n 183360]
foreach {prefix first} {ui_in 179520 uio_in 148800 uio_oe 56640 uio_out 87360 uo_out 118080} {
    for {set k 0} {$k < 8} {incr k} {
        dict set streaming_pdn_expected_x [format {%s[%d]} $prefix $k] [expr {$first - 3840 * $k}]
    }
}
set streaming_pdn_seen {}
set streaming_pdn_pin_modes {}
foreach term [$streaming_pdn_block getBTerms] {
    set kind [$term getSigType]
    if {$kind eq "POWER" || $kind eq "GROUND"} {
        # Fresh floorplans have no pre-existing PG port geometry.  Reusing an
        # already generated grid could otherwise retain forbidden M2/M3 pins.
        foreach pin [$term getBPins] {
            if {[llength [$pin getBoxes]] != 0} {error "Streaming PDN requires a fresh power grid"}
        }
        continue
    }
    set name [$term getName]
    if {![dict exists $streaming_pdn_expected_x $name] || [dict exists $streaming_pdn_seen $name]} {
        error "Unexpected or duplicate streaming public pin: $name"
    }
    set expected_direction OUTPUT
    if {$name in {clk ena rst_n} || [string match {ui_in\[*} $name] || [string match {uio_in\[*} $name]} {
        set expected_direction INPUT
    }
    if {[$term getIoType] ne $expected_direction} {error "Streaming public-pin direction changed: $name"}
    set pins [$term getBPins]
    set center [dict get $streaming_pdn_expected_x $name]
    if {[llength $pins] == 0} {
        dict set streaming_pdn_pin_modes unplaced 1
    } else {
        dict set streaming_pdn_pin_modes placed 1
        if {[llength $pins] != 1} {error "Streaming public pin must have one BPin: $name"}
        set boxes [[lindex $pins 0] getBoxes]
        if {[llength $boxes] != 1} {error "Streaming public pin must have one rectangle: $name"}
        set box [lindex $boxes 0]
        if {[[$box getTechLayer] getName] ne "Metal4" ||
            [$box xMin] != $center - 150 || [$box xMax] != $center + 150 ||
            [$box yMin] != 709640 || [$box yMax] != 710640} {
            error "Streaming public pin differs from the official template: $name"
        }
    }
    dict set streaming_pdn_seen $name 1
    for {set first $streaming_pdn_m4_first_center_dbu} {
        $first + $streaming_pdn_m4_pair_delta_dbu + $streaming_pdn_m4_width_dbu / 2 <= 1289280
    } {incr first $streaming_pdn_m4_pitch_dbu} {
        foreach x [list $first [expr {$first + $streaming_pdn_m4_pair_delta_dbu}]] {
            set distance [expr {abs($x - $center) - $streaming_pdn_m4_width_dbu / 2 - 150}]
            if {$distance < $streaming_pdn_public_clearance_dbu} {
                error "Streaming Metal4 power strap violates public-pin clearance: $name"
            }
        }
    }
}
if {[dict size $streaming_pdn_seen] != 43} {error "Missing streaming public pins"}
if {[dict size $streaming_pdn_pin_modes] != 1} {error "Mixed public-pin placement before PDN"}

source $::env(SCRIPTS_DIR)/openroad/common/set_global_connections.tcl
set_global_connections
set_voltage_domain -name CORE -power $::env(VDD_NET) -ground $::env(GND_NET)
define_pdn_grid -name streaming_stdcell_grid -starts_with POWER -voltage_domain CORE -pins {Metal4}
add_pdn_stripe -grid streaming_stdcell_grid -layer Metal1 -width $::env(PDN_RAIL_WIDTH) -followpins
# Adjacent-layer local straps let every horizontal row rail join the grid.
# Jumping directly from M1 to M4 leaves channel bands at the M3 straps.
add_pdn_stripe -grid streaming_stdcell_grid -layer Metal2 -width 1.0 \
    -pitch $::env(PDN_VPITCH) -offset $::env(PDN_VOFFSET) -spacing $::env(PDN_VSPACING) \
    -starts_with POWER
add_pdn_stripe -grid streaming_stdcell_grid -layer Metal3 -width $::env(PDN_HWIDTH) \
    -pitch $::env(PDN_HPITCH) -offset $::env(PDN_HOFFSET) -spacing $::env(PDN_HSPACING) \
    -starts_with POWER
# Only the full-height M4 stripes are package power ports.  Extending M2/M3
# to the die edge also creates automatic edge pins in the pinned PDN runtime,
# even when those layers are absent from define_pdn_grid -pins.
add_pdn_stripe -grid streaming_stdcell_grid -layer Metal4 -width $::env(PDN_VWIDTH) \
    -pitch [expr {$streaming_pdn_m4_pitch_dbu / 1000.0}] \
    -offset [expr {($streaming_pdn_m4_first_center_dbu - [$streaming_pdn_core xMin]) / 1000.0}] \
    -spacing [expr {($streaming_pdn_m4_pair_delta_dbu - $streaming_pdn_m4_width_dbu) / 1000.0}] \
    -starts_with POWER -extend_to_boundary
add_pdn_connect -grid streaming_stdcell_grid -layers {Metal1 Metal2}
add_pdn_connect -grid streaming_stdcell_grid -layers {Metal2 Metal3}
add_pdn_connect -grid streaming_stdcell_grid -layers {Metal3 Metal4}
