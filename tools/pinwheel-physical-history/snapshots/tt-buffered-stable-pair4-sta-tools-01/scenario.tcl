# Pure standalone OpenSTA ConcreteNetwork. Never loads an OpenDB/LEF/DEF.
set sta_report_default_digits 6
define_corners $::env(PINWHEEL_CORNER)
foreach library $::env(PINWHEEL_LIBRARIES) {read_liberty -corner $::env(PINWHEEL_CORNER) $library}
read_verilog $::env(PINWHEEL_NETLIST)
link_design tt_um_pinwheel_buffered
set ::env(CLOCK_PERIOD) 20
source $::env(PINWHEEL_SDC)
read_spef -corner $::env(PINWHEEL_CORNER) $::env(PINWHEEL_SPEF)
puts "PINWHEEL_STANDALONE_FIXED_WIRE_RC_LOADED_NO_PHYSICAL_DATABASE"
foreach instance {fanout914 fanout913} {
    set cell [get_cells $instance]
    if {[llength $cell] != 1} {error "Missing/ambiguous virtual buffer"}
    puts "PINWHEEL_MASTER $instance [get_property $cell ref_name]"
}
set corner $::env(PINWHEEL_CORNER)
puts "%OL_CREATE_REPORT global-max.rpt"
report_checks -path_delay max -sort_by_slack -group_path_count 1000 -fields {slew cap input net fanout} -format full_clock_expanded -corner $corner
puts "%OL_END_REPORT"
puts "%OL_CREATE_REPORT global-min.rpt"
report_checks -path_delay min -sort_by_slack -group_path_count 1000 -fields {slew cap input net fanout} -format full_clock_expanded -corner $corner
puts "%OL_END_REPORT"
puts "PINWHEEL_GLOBAL_SETUP [worst_slack -max -corner $corner]"
puts "PINWHEEL_GLOBAL_HOLD [worst_slack -min -corner $corner]"
set failures [open global-violations.tsv w]
foreach kind {max min} {
    set paths [find_timing_paths -path_delay $kind -sort_by_slack -unique_paths_to_endpoint -group_path_count 999999999 -slack_max 0]
    set count 0
    foreach path $paths {
        set slack [get_property $path slack]
        if {$slack < 0} {
            puts $failures "$kind\t[get_property [get_property $path endpoint] full_name]\t[get_property [get_property $path startpoint] full_name]\t$slack"
            incr count
        }
    }
    puts "PINWHEEL_GLOBAL_FAILURE_COUNT $kind $count"
}
close $failures
puts "%OL_CREATE_REPORT checks.rpt"
report_check_types -max_slew -max_capacitance -max_fanout -violators -corner $corner
report_parasitic_annotation -report_unannotated
check_setup -verbose -unconstrained_endpoints -multiple_clock -no_clock -no_input_delay -loops -generated_clocks
puts "%OL_END_REPORT"
puts "%OL_CREATE_REPORT clock.rpt"
report_clock_latency -clock [get_clocks clk] -corner $corner
puts "%OL_END_REPORT"
set output [open coverage.tsv w]
foreach driver {fanout914 fanout913} {
    set through [get_pins $driver/X]
    foreach trace {all timing} {
        foreach endpoint [get_fanout -from $through -flat -endpoints_only -trace_arcs $trace] {puts $output "REACH\t$driver\t$trace\t[get_property $endpoint full_name]"}
    }
    foreach edge {rise fall} {
        set flag -${edge}_through
        foreach kind {max min} {
            set paths [find_timing_paths $flag $through -path_delay $kind -sort_by_slack -unique_paths_to_endpoint -group_path_count 999999999]
            foreach path $paths {puts $output "PATH\t$driver\t$edge\t$kind\t[get_property [get_property $path endpoint] full_name]\t[get_property [get_property $path startpoint] full_name]\t[get_property $path slack]"}
            puts "%OL_CREATE_REPORT resetpair-$driver-$edge-$kind.rpt"
            report_checks $flag $through -path_delay $kind -sort_by_slack -unique_paths_to_endpoint -group_path_count 999999999 -fields {slew cap input net fanout} -format full_clock_expanded -corner $corner
            puts "%OL_END_REPORT"
        }
    }
}
close $output
puts "PINWHEEL_COMPLETE_FIXED_WIRE_TIMING_SCENARIO"
exit
