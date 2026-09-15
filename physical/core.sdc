# Core-level synchronous timing experiment; units are ns and pF.
# These are boundary assumptions, not a claim about asynchronous protocol pins.
create_clock -name clk -period $::env(CLOCK_PERIOD) [get_ports clk]
set nonclock_inputs [get_ports {init reset command[*] data[*] incoming[*]}]
set_input_delay -clock clk -max 4.0 $nonclock_inputs
set_input_delay -clock clk -min 0.2 $nonclock_inputs
set_output_delay -clock clk -max 4.0 [all_outputs]
set_output_delay -clock clk -min 0.2 [all_outputs]
set_driving_cell -lib_cell sg13cmos5l_buf_2 -pin X $nonclock_inputs
set_load 0.010 [all_outputs]
set_clock_uncertainty 0.2 [get_clocks clk]
set_clock_transition 0.15 [get_clocks clk]
if { [info exists ::env(OPENLANE_SDC_IDEAL_CLOCKS)] && $::env(OPENLANE_SDC_IDEAL_CLOCKS) } {
    unset_propagated_clock [all_clocks]
} else {
    set_propagated_clock [all_clocks]
}
