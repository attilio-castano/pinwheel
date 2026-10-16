# Copyright 2026 LibreLane Contributors
#
# Adapted from OpenLane 2
#
# Copyright 2020-2023 Efabless Corporation
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#      http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

# This file supports one defined corner per-process.
# Any more defined corners will be ignored: aggregation is left to the LibreLane
# step.


source $::env(SCRIPTS_DIR)/openroad/common/io.tcl

set_cmd_units\
    -time ns\
    -capacitance pF\
    -current mA\
    -voltage V\
    -resistance kOhm\
    -distance um

set sta_report_default_digits 6

if { ![namespace exists ::ord] } {error "OpenROAD required; no standalone or placement RC fallback"}
read_current_odb
source $::env(SCRIPTS_DIR)/openroad/common/set_rc.tcl
source $::env(SCRIPTS_DIR)/openroad/common/set_routing_layers.tcl
source $::env(SCRIPTS_DIR)/openroad/common/set_layer_adjustments.tcl
set_macro_extension $::env(GRT_MACRO_EXTENSION)
proc pinwheel_ndr_snapshot {filename} {
    set rows {}
    foreach net [$::block getNets] {
        set rule [$net getNonDefaultRule]
        set rule_name {}
        if {$rule != "NULL"} {set rule_name [$rule getName]}
        set net_name [$net getName]
        if {[regexp {[\t\n]} $net_name] || [regexp {[\t\n]} $rule_name]} {error "Invalid TSV name"}
        lappend rows "$net_name\t$rule_name"
    }
    set output [open $filename w]
    foreach row [lsort $rows] {puts $output $row}
    close $output
}
pinwheel_ndr_snapshot ndr-before-import.txt
write_def timing-input.def
set width_file [open ndr-width-equivalence.txt w]
foreach layer_name {Metal1 Metal2 Metal3 Metal4 TopMetal1} {
    set layer [$::tech findLayer $layer_name]
    set default_width [$layer getWidth]
    foreach rule [$::block getNonDefaultRules] {
        set layer_rule [$rule getLayerRule $layer]
        if {$layer_rule == "NULL"} {error "Missing routed-layer NDR rule"}
        set width [$layer_rule getWidth]
        if {$width != $default_width} {error "Runtime NDR fallback RC width ambiguity"}
        puts $width_file [list $layer_name [$rule getName] $default_width $width]
    }
}
close $width_file
read_global_route_segments $::env(PINWHEEL_TIMING_ROOT)/after_grt.segments
if { ![grt::have_routes] } {error "Imported native global routes absent"}
write_global_route_segments imported.segments
pinwheel_ndr_snapshot ndr-after-import.txt
write_verilog timing-before.v
puts "PINWHEEL_ROUTE_SEGMENTS_IMPORTED_AND_GLOBAL_RC_REQUIRED"
set rc_file [open layer-rc.tsv w]
foreach layer_name {Metal1 Metal2 Metal3 Metal4 TopMetal1} {
 set layer [$::tech findLayer $layer_name]
 puts $rc_file [join [list $layer_name [$layer getRoutingLevel] [est::dblayer_wire_rc $layer]] "\t"]
}
close $rc_file
grt::write_pin_locations pin-grid.txt
estimate_parasitics -global_routing -spef_file estimated.spef
puts PINWHEEL_FULL_PRECISION_PINRC_BEGIN
set_cmd_units -capacitance fF
sta::set_cmd_unit_digits capacitance 12
sta::set_cmd_unit_digits resistance 12
puts "PINWHEEL_CAP_UNIT_SCALE [sta::unit_scale capacitance]"
set_debug_level EST est_rc 1
estimate_parasitics -global_routing -spef_file capture-ff.spef
set_debug_level EST est_rc 0
puts PINWHEEL_FULL_PRECISION_PINRC_END
set_cmd_units -capacitance pF
write_global_route_segments after-timing.segments
write_verilog timing-after.v
write_def timing-after.def
puts PINWHEEL_PINRC_READONLY_EXPORT_FINISHED
puts "PINWHEEL_GLOBAL_ROUTE_RC_ESTIMATED"
# Inherited SPEF/SDF are deliberately absent; only the freshly estimated RC is used.

