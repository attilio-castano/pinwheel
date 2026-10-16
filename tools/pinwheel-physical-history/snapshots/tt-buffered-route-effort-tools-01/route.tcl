source $::env(SCRIPTS_DIR)/openroad/common/io.tcl
read_current_odb
source $::env(SCRIPTS_DIR)/openroad/common/dpl_cell_pad.tcl
set_propagated_clock [all_clocks]
source $::env(SCRIPTS_DIR)/openroad/common/set_routing_layers.tcl
source $::env(SCRIPTS_DIR)/openroad/common/set_layer_adjustments.tcl
set_macro_extension $::env(GRT_MACRO_EXTENSION)
write_verilog /work/diagnostic/before.v
write_def /work/diagnostic/before.def
global_route -congestion_iterations $::env(GRT_OVERFLOW_ITERS) -verbose -allow_congestion -congestion_report_file /work/diagnostic/congestion.json
write_global_route_segments /work/diagnostic/after_grt.segments
write_guide /work/diagnostic/after_grt.guide
write_verilog /work/diagnostic/after.v
write_def /work/diagnostic/routed.def
write_db /work/diagnostic/routed.odb
