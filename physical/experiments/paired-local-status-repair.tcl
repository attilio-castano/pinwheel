# One controlled change: divide the long eight-load register-clock trunk into
# four spatial pairs. Retain every existing cell, location and logic connection.
# Incremental coarse routing updates the affected wires before any measurement.
write_verilog /probe/before.v
set originals [$::block getInsts]
set_routing_layers -signal Metal2-Metal4 -clock Metal2-Metal4
set_global_routing_layer_adjustment * 0.3
global_route -start_incremental

set pairs {
  {0 {485.0 400.0} {clkbuf_3_0_0_clk_regs/A clkbuf_3_1_0_clk_regs/A}}
  {1 {500.0 490.0} {clkbuf_3_2_0_clk_regs/A clkbuf_3_3_0_clk_regs/A}}
  {2 {815.0 400.0} {clkbuf_3_4_0_clk_regs/A clkbuf_3_5_0_clk_regs/A}}
  {3 {800.0 475.0} {clkbuf_3_6_0_clk_regs/A clkbuf_3_7_0_clk_regs/A}}
}
foreach pair $pairs {
  lassign $pair index location loads
  foreach pin $loads {
    set terminal [$::block findITerm $pin]
    if {$terminal eq "NULL" || [[$terminal getNet] getName] ne "clknet_0_clk_regs"} {
      error "Unexpected clock trunk connection: $pin"
    }
  }
  # Direct database insertion avoids the pinned resizer's uninitialized DPL
  # post-insertion path. Normal legalization still checks the final geometry.
  set inst [odb::dbInst_create $::block [[ord::get_db] findMaster sg13cmos5l_buf_8] paired_clock_trunk_$index]
  set branch [odb::dbNet_create $::block paired_clock_branch_$index]
  $branch setSigType CLOCK
  [$inst findITerm A] connect [$::block findNet clknet_0_clk_regs]
  [$inst findITerm X] connect $branch
  foreach pin $loads {
    set terminal [$::block findITerm $pin]
    $terminal disconnect
    $terminal connect $branch
  }
  lassign $location x y
  $inst setLocation [expr {int($x * [$::block getDbUnitsPerMicron])}] [expr {int($y * [$::block getDbUnitsPerMicron])}]
  $inst setPlacementStatus PLACED
}

# Buffer the union of all-corner electrical failures plus the two loaded
# critical status gates. Original drivers and logical cells remain unchanged.
set loads {
  {0 {_01717_} {_05524_/X} {401.76 362.88}}
  {1 {_01719_} {_05526_/Y} {593.28 347.76}}
  {2 {_01784_} {_05599_/Y} {336.96 366.66}}
  {3 {_01793_} {_05608_/Y} {488.64 102.06}}
  {4 {_01825_} {_05640_/Y} {728.64 113.4}}
  {5 {_01853_} {_05668_/Y} {631.2 347.76}}
  {6 {_01877_} {_05692_/X} {960.96 525.42}}
  {7 {_02584_} {_06399_/X} {817.92 529.2}}
  {8 {_02930_} {_06745_/Y} {1046.88 151.2}}
  {9 {_02935_} {_06750_/Y} {924.48 495.18}}
  {10 {_02940_} {_06755_/Y} {888.48 453.6}}
  {11 {_02944_} {_06759_/X} {902.88 631.26}}
  {12 {_02945_} {_06760_/X} {904.8 631.26}}
  {13 {_02956_} {_06771_/X} {745.44 102.06}}
  {14 {_02960_} {_06775_/X} {1176.48 555.66}}
  {15 {_02961_} {_06776_/X} {1075.2 665.28}}
  {16 {_02963_} {_06778_/X} {1020.48 642.6}}
  {17 {_02969_} {_06784_/X} {1156.32 438.48}}
  {18 {_02976_} {_06791_/X} {593.76 567.0}}
  {19 {_02980_} {_06795_/X} {930.72 529.2}}
  {20 {_02982_} {_06797_/X} {1063.68 604.8}}
  {21 {_02992_} {_06807_/X} {977.28 627.48}}
  {22 {_02994_} {_06809_/X} {1128.48 419.58}}
  {23 {_02997_} {_06812_/Y} {950.88 525.42}}
  {24 {_03009_} {_06824_/X} {1142.4 514.08}}
  {25 {_03016_} {_06831_/X} {1161.12 412.02}}
  {26 {_03036_} {_06851_/X} {933.12 434.7}}
  {27 {_03043_} {_06858_/X} {983.52 536.76}}
  {28 {_03046_} {_06861_/X} {1091.52 449.82}}
  {29 {_03047_} {_06862_/X} {331.2 430.92}}
  {30 {_03062_} {_06877_/X} {1129.92 427.14}}
  {31 {_03072_} {_06887_/X} {1017.12 548.1}}
  {32 {_03082_} {_06897_/X} {645.6 498.96}}
  {33 {_03099_} {_06914_/X} {1101.12 438.48}}
  {34 {_03100_} {_06915_/X} {343.68 529.2}}
  {35 {_03101_} {_06916_/X} {1123.2 438.48}}
  {36 {_03114_} {_06929_/X} {1125.12 498.96}}
  {37 {_03151_} {_06966_/X} {363.84 597.24}}
  {38 {_03157_} {_06972_/X} {343.68 532.98}}
  {39 {_03167_} {_06982_/X} {929.28 502.74}}
  {40 {_03181_} {_06996_/X} {1137.6 434.7}}
  {41 {_03185_} {_07000_/X} {1154.4 442.26}}
  {42 {_03246_} {_07061_/X} {331.68 419.58}}
  {43 {_03283_} {_07098_/X} {435.84 585.9}}
  {44 {_03340_} {_07155_/Y} {918.72 495.18}}
  {45 {_03398_} {_07213_/X} {1040.16 536.76}}
  {46 {_04197_} {_08012_/Y} {412.32 113.4}}
  {47 {_04294_} {_08148_/X} {374.4 529.2}}
  {48 {_04300_} {_08160_/X} {348.96 495.18}}
  {49 {_04336_} {_08216_/X} {437.28 374.22}}
  {50 {_04354_} {_08246_/X} {307.2 449.82}}
  {51 {_04361_} {_08268_/Y} {231.84 449.82}}
  {52 {_04369_} {_08295_/Y} {300.0 446.04}}
  {53 {_04371_} {_08301_/X} {303.84 449.82}}
  {54 {_04375_} {_08320_/Y} {263.52 457.38}}
  {55 {_04382_} {_08346_/Y} {246.72 442.26}}
  {56 {_04384_} {_08352_/X} {286.08 461.16}}
  {57 {_04397_} {_08399_/X} {823.2 532.98}}
  {58 {_04399_} {_08401_/Y} {270.24 442.26}}
  {59 {_04403_} {_08409_/X} {312.48 540.54}}
  {60 {_04410_} {_08431_/Y} {271.68 457.38}}
  {61 {_04432_} {_08491_/Y} {240.96 453.6}}
  {62 {_04436_} {_08504_/X} {358.08 430.92}}
  {63 {_04440_} {_08518_/Y} {282.72 453.6}}
  {64 {_04448_} {_08545_/Y} {279.36 461.16}}
  {65 {_04468_} {_08604_/X} {384.96 525.42}}
  {66 {_04479_} {_08633_/X} {420.96 514.08}}
  {67 {_04480_} {_08635_/X} {382.08 544.32}}
  {68 {_04513_} {_08745_/X} {238.56 461.16}}
  {69 {_04518_} {_08767_/Y} {251.52 483.84}}
  {70 {_04536_} {_08814_/X} {754.56 427.14}}
  {71 {_04553_} {_08860_/X} {336.48 563.22}}
  {72 {_04572_} {_08955_/X} {336.48 555.66}}
  {73 {_04583_} {_09004_/X} {354.72 544.32}}
  {74 {_04605_} {_09078_/Y} {229.44 438.48}}
  {75 {_04611_} {_09103_/Y} {293.28 449.82}}
  {76 {_04623_} {_09153_/Y} {295.68 438.48}}
  {77 {_04628_} {_09177_/Y} {233.76 446.04}}
  {78 {_04635_} {_09203_/Y} {296.16 446.04}}
  {79 {_04642_} {_09229_/Y} {262.56 449.82}}
  {80 {_04659_} {_09265_/Y} {243.84 438.48}}
  {81 {_04669_} {_09313_/Y} {266.4 438.48}}
  {82 {_04689_} {_09409_/Y} {278.88 453.6}}
  {83 {_05222_} {_10456_/X} {258.24 351.54}}
  {84 {net1888} {hold1888/X} {924.96 351.54}}
  {85 {net1891} {hold1891/X} {880.8 113.4}}
  {86 {net1897} {hold1897/X} {505.44 347.76}}
  {87 {net1901} {hold1901/X} {673.44 347.76}}
  {88 {net1903} {hold1903/X} {494.88 347.76}}
  {89 {net1916} {hold1916/X} {640.8 347.76}}
  {90 {net1921} {hold1921/X} {669.12 347.76}}
  {91 {net1940} {hold1940/X} {474.72 347.76}}
  {92 {net1946} {hold1946/X} {719.04 347.76}}
  {93 {net1969} {hold1969/X} {501.12 347.76}}
  {94 {net1972} {hold1972/X} {883.68 355.32}}
  {95 {net1980} {hold1980/X} {442.56 374.22}}
  {96 {net1989} {hold1989/X} {573.6 385.56}}
  {97 {net28} {wire28/X} {710.88 427.14}}
  {98 {net29} {wire29/X} {754.08 483.84}}
}
foreach row $loads {
  lassign $row index net_name driver location
  set terminal [$::block findITerm $driver]
  set wire [$::block findNet $net_name]
  if {$terminal eq "NULL" || $wire eq "NULL" || [$terminal getNet] ne $wire || [$wire getSigType] ne "SIGNAL"} {
    error "Unexpected signal driver $driver"
  }
  set inst [odb::dbInst_create $::block [[ord::get_db] findMaster sg13cmos5l_buf_8] paired_signal_$index]
  set stub [odb::dbNet_create $::block paired_signal_stub_$index]
  $terminal disconnect
  $terminal connect $stub
  [$inst findITerm A] connect $stub
  [$inst findITerm X] connect $wire
  lassign $location x y
  $inst setLocation [expr {int($x * [$::block getDbUnitsPerMicron])}] [expr {int($y * [$::block getDbUnitsPerMicron])}]
  $inst setPlacementStatus PLACED
}

# Four drivers from the sole remaining slow violating setup path.
set additional_status {
  {99 {_01782_} {_05597_/Y} {875.52 113.4}}
  {100 {_01786_} {_05601_/Y} {900.96 359.1}}
  {101 {_01999_} {_05814_/Y} {790.56 427.14}}
  {102 {_02000_} {_05815_/X} {530.88 427.14}}
}
foreach row $additional_status {
  lassign $row index net_name driver location
  set terminal [$::block findITerm $driver]
  set wire [$::block findNet $net_name]
  if {$terminal eq "NULL" || $wire eq "NULL" || [$terminal getNet] ne $wire || [$wire getSigType] ne "SIGNAL"} {
    error "Unexpected signal driver $driver"
  }
  set inst [odb::dbInst_create $::block [[ord::get_db] findMaster sg13cmos5l_buf_8] paired_signal_$index]
  set stub [odb::dbNet_create $::block paired_signal_stub_$index]
  $terminal disconnect
  $terminal connect $stub
  [$inst findITerm A] connect $stub
  [$inst findITerm X] connect $wire
  lassign $location x y
  $inst setLocation [expr {int($x * [$::block getDbUnitsPerMicron])}] [expr {int($y * [$::block getDbUnitsPerMicron])}]
  $inst setPlacementStatus PLACED
}

# Endpoint-specific hold chains; no logical or pipeline state is added.
set endpoints {
  {0 {_10883_/D} {controller._GEN_63[28]} 13 {646.08 94.5} sg13cmos5l_buf_1}
  {1 {_10766_/D} {_01401_} 6 {551.52 90.72} sg13cmos5l_buf_1}
  {2 {memory.storage/A_DIN[56]} {net1849} 5 {954.38 108.0} sg13cmos5l_buf_1}
  {3 {memory.storage/A_DIN[13]} {net1980} 5 {401.54 108.0} sg13cmos5l_buf_1}
  {4 {memory.storage/A_DIN[55]} {net1843} 5 {943.14 108.0} sg13cmos5l_buf_1}
  {5 {memory.storage/A_DIN[57]} {net1855} 5 {965.62 108.0} sg13cmos5l_buf_1}
  {6 {memory.storage/A_DIN[61]} {net1869} 5 {1010.58 108.0} sg13cmos5l_buf_1}
  {7 {memory.storage/A_DIN[59]} {net1860} 5 {988.1 108.0} sg13cmos5l_buf_1}
  {8 {memory.storage/A_DIN[9]} {net1969} 4 {356.58 108.0} sg13cmos5l_buf_1}
  {9 {memory.storage/A_DIN[62]} {net1838} 4 {1021.82 108.0} sg13cmos5l_buf_1}
  {10 {memory.storage/A_DIN[48]} {net1891} 4 {864.46 108.0} sg13cmos5l_buf_1}
  {11 {memory.storage/A_ADDR[3]} {memory.mem_addr0[3]} 3 {647.2 108.0} sg13cmos5l_buf_1}
  {12 {_10770_/D} {_01397_} 3 {632.16 98.28} sg13cmos5l_buf_1}
  {13 {_10764_/D} {_01403_} 3 {511.68 90.72} sg13cmos5l_buf_1}
  {14 {_10762_/D} {_01405_} 3 {450.72 90.72} sg13cmos5l_buf_1}
  {15 {_10878_/D} {controller._GEN_63[23]} 3 {502.08 98.28} sg13cmos5l_buf_1}
  {16 {_10879_/D} {controller._GEN_63[24]} 3 {521.28 98.28} sg13cmos5l_buf_1}
  {17 {memory.storage/A_DIN[16]} {net29} 1 {435.26 108.0} sg13cmos5l_buf_8}
}
foreach row $endpoints {
  lassign $row index pin old_name stages location cell
  set terminal [$::block findITerm $pin]
  if {$terminal eq "NULL" || [[$terminal getNet] getName] ne $old_name} {error "Unexpected hold/slew endpoint $pin"}
  set wire [$terminal getNet]
  $terminal disconnect
  for {set stage 0} {$stage < $stages} {incr stage} {
    set inst [odb::dbInst_create $::block [[ord::get_db] findMaster $cell] paired_endpoint_${index}_${stage}]
    set next [odb::dbNet_create $::block paired_endpoint_net_${index}_${stage}]
    [$inst findITerm A] connect $wire
    [$inst findITerm X] connect $next
    lassign $location x y
    $inst setLocation [expr {int($x * [$::block getDbUnitsPerMicron])}] [expr {int($y * [$::block getDbUnitsPerMicron])}]
    $inst setPlacementStatus PLACED
    set wire $next
  }
  $terminal connect $wire
}

# Final observed status branch and positive hold margin follow-up.
set final_status {
  {103 {_01854_} {_05669_/Y} {796.32 113.4}}
  {104 {_01856_} {_05671_/Y} {805.44 366.66}}
  {105 {_02905_} {_06720_/Y} {1001.76 491.4}}
}
foreach row $final_status {
  lassign $row index net_name driver location
  set terminal [$::block findITerm $driver]
  set wire [$::block findNet $net_name]
  if {$terminal eq "NULL" || $wire eq "NULL" || [$terminal getNet] ne $wire || [$wire getSigType] ne "SIGNAL"} {
    error "Unexpected signal driver $driver"
  }
  set inst [odb::dbInst_create $::block [[ord::get_db] findMaster sg13cmos5l_buf_8] paired_signal_$index]
  set stub [odb::dbNet_create $::block paired_signal_stub_$index]
  $terminal disconnect
  $terminal connect $stub
  [$inst findITerm A] connect $stub
  [$inst findITerm X] connect $wire
  lassign $location x y
  $inst setLocation [expr {int($x * [$::block getDbUnitsPerMicron])}] [expr {int($y * [$::block getDbUnitsPerMicron])}]
  $inst setPlacementStatus PLACED
}


set final_endpoints {
  {18 {memory.storage/A_DIN[0]} {net1887} 4 {255.42000000000002 108.0} sg13cmos5l_buf_1}
  {19 {_10877_/D} {controller._GEN_63[22]} 4 {420.96 90.72} sg13cmos5l_buf_1}
  {20 {memory.storage/A_DIN[7]} {net33} 4 {334.1 108.0} sg13cmos5l_buf_1}
  {21 {memory.storage/A_DIN[12]} {net1989} 4 {390.3 108.0} sg13cmos5l_buf_1}
  {22 {memory.storage/A_DIN[16]} {paired_endpoint_net_17_0} 4 {435.26 108.0} sg13cmos5l_buf_1}
  {23 {memory.storage/A_DIN[4]} {net1881} 4 {300.38 108.0} sg13cmos5l_buf_1}
  {24 {memory.storage/A_DIN[1]} {net1892} 3 {266.65999999999997 108.0} sg13cmos5l_buf_1}
  {25 {memory.storage/A_DIN[18]} {net28} 3 {457.74 108.0} sg13cmos5l_buf_1}
  {26 {memory.storage/A_DIN[6]} {net34} 3 {322.86 108.0} sg13cmos5l_buf_1}
  {27 {memory.storage/A_DIN[3]} {net1875} 3 {289.14 108.0} sg13cmos5l_buf_1}
  {28 {memory.storage/A_DIN[60]} {net1896} 3 {999.34 108.0} sg13cmos5l_buf_1}
  {29 {memory.storage/A_DIN[5]} {net1886} 3 {311.62 108.0} sg13cmos5l_buf_1}
  {30 {memory.storage/A_DIN[62]} {paired_endpoint_net_9_3} 2 {1021.82 108.0} sg13cmos5l_buf_1}
}
foreach row $final_endpoints {
  lassign $row index pin old_name stages location cell
  set terminal [$::block findITerm $pin]
  if {$terminal eq "NULL" || [[$terminal getNet] getName] ne $old_name} {error "Unexpected hold/slew endpoint $pin"}
  set wire [$terminal getNet]
  $terminal disconnect
  for {set stage 0} {$stage < $stages} {incr stage} {
    set inst [odb::dbInst_create $::block [[ord::get_db] findMaster $cell] paired_endpoint_${index}_${stage}]
    set next [odb::dbNet_create $::block paired_endpoint_net_${index}_${stage}]
    [$inst findITerm A] connect $wire
    [$inst findITerm X] connect $next
    lassign $location x y
    $inst setLocation [expr {int($x * [$::block getDbUnitsPerMicron])}] [expr {int($y * [$::block getDbUnitsPerMicron])}]
    $inst setPlacementStatus PLACED
    set wire $next
  }
  $terminal connect $wire
}


# Remaining slow critical path after the first margin check.
set remaining_status {
  {106 {_02168_} {_05983_/Y} {579.84 601.02}}
  {107 {_02179_} {_05994_/Y} {268.8 612.36}}
  {108 {uo_out[4]} {_08066_/Y} {95.04 487.62}}
}
foreach row $remaining_status {
  lassign $row index net_name driver location
  set terminal [$::block findITerm $driver]
  set wire [$::block findNet $net_name]
  if {$terminal eq "NULL" || $wire eq "NULL" || [$terminal getNet] ne $wire || [$wire getSigType] ne "SIGNAL"} {
    error "Unexpected signal driver $driver"
  }
  set inst [odb::dbInst_create $::block [[ord::get_db] findMaster sg13cmos5l_buf_8] paired_signal_$index]
  set stub [odb::dbNet_create $::block paired_signal_stub_$index]
  $terminal disconnect
  $terminal connect $stub
  [$inst findITerm A] connect $stub
  [$inst findITerm X] connect $wire
  lassign $location x y
  $inst setLocation [expr {int($x * [$::block getDbUnitsPerMicron])}] [expr {int($y * [$::block getDbUnitsPerMicron])}]
  $inst setPlacementStatus PLACED
}



set remaining_endpoints {
  {31 {memory.storage/A_DIN[6]} {paired_endpoint_net_26_2} 3 {322.86 108.0} sg13cmos5l_buf_1}
}
foreach row $remaining_endpoints {
  lassign $row index pin old_name stages location cell
  set terminal [$::block findITerm $pin]
  if {$terminal eq "NULL" || [[$terminal getNet] getName] ne $old_name} {error "Unexpected hold/slew endpoint $pin"}
  set wire [$terminal getNet]
  $terminal disconnect
  for {set stage 0} {$stage < $stages} {incr stage} {
    set inst [odb::dbInst_create $::block [[ord::get_db] findMaster $cell] paired_endpoint_${index}_${stage}]
    set next [odb::dbNet_create $::block paired_endpoint_net_${index}_${stage}]
    [$inst findITerm A] connect $wire
    [$inst findITerm X] connect $next
    lassign $location x y
    $inst setLocation [expr {int($x * [$::block getDbUnitsPerMicron])}] [expr {int($y * [$::block getDbUnitsPerMicron])}]
    $inst setPlacementStatus PLACED
    set wire $next
  }
  $terminal connect $wire
}



# Shared loaded drivers in the 100-path near-critical status audit.
set shared_status {
  {109 {_02061_} {_05876_/Y} {510.24 427.14}}
  {110 {_02062_} {_05877_/Y} {159.36 423.36}}
}
foreach row $shared_status {
  lassign $row index net_name driver location
  set terminal [$::block findITerm $driver]
  set wire [$::block findNet $net_name]
  if {$terminal eq "NULL" || $wire eq "NULL" || [$terminal getNet] ne $wire || [$wire getSigType] ne "SIGNAL"} {
    error "Unexpected signal driver $driver"
  }
  set inst [odb::dbInst_create $::block [[ord::get_db] findMaster sg13cmos5l_buf_8] paired_signal_$index]
  set stub [odb::dbNet_create $::block paired_signal_stub_$index]
  $terminal disconnect
  $terminal connect $stub
  [$inst findITerm A] connect $stub
  [$inst findITerm X] connect $wire
  lassign $location x y
  $inst setLocation [expr {int($x * [$::block getDbUnitsPerMicron])}] [expr {int($y * [$::block getDbUnitsPerMicron])}]
  $inst setPlacementStatus PLACED
}




set statuses {}
foreach inst $originals {
  lappend statuses $inst [$inst getPlacementStatus]
  if {[$inst getPlacementStatus] eq "PLACED"} {$inst setPlacementStatus FIRM}
}
detailed_placement -max_displacement {50 20}
check_placement -verbose
foreach {inst status} $statuses {$inst setPlacementStatus $status}
global_connect
global_route -end_incremental -allow_congestion
estimate_parasitics -global_routing
write_guide /probe/repaired.guide
write_verilog /probe/repaired.v
write_db /probe/repaired.odb
puts {PINWHEEL_LOCAL_STATUS_REPAIR_DONE}
