read_db /work/diagnostic/input.odb
check_power_grid -net VPWR -error_file /work/diagnostic/VPWR-grid-errors.rpt
check_power_grid -net VGND -error_file /work/diagnostic/VGND-grid-errors.rpt
