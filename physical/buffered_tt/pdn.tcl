# Experimental CMOS5L tile grid. SRAM columns are connected by the following
# Project.BufferedSramPower step; an empty automatic macro grid is omitted.
source $::env(SCRIPTS_DIR)/openroad/common/set_global_connections.tcl
set_global_connections
set_voltage_domain -name CORE -power $::env(VDD_NET) -ground $::env(GND_NET)
define_pdn_grid -name stdcell_grid -starts_with POWER -voltage_domain CORE -pins Metal4
add_pdn_stripe -grid stdcell_grid -layer Metal4 -width $::env(PDN_VWIDTH) \
    -pitch $::env(PDN_VPITCH) -offset $::env(PDN_VOFFSET) \
    -spacing $::env(PDN_VSPACING) -starts_with POWER -extend_to_boundary
add_pdn_stripe -grid stdcell_grid -layer Metal1 -width $::env(PDN_RAIL_WIDTH) -followpins
add_pdn_connect -grid stdcell_grid -layers {Metal1 Metal4}
