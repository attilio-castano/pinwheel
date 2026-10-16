"""Render direct native exact ECO; no optimizer or placement movement."""
import json
from pathlib import Path
HERE=Path(__file__).resolve().parent
p=json.loads((HERE/'plan.json').read_text())
def lit(s):assert all(c not in s for c in '{}\n');return '{'+s+'}'
lines=['read_db /work/diagnostic/input.odb','set block [ord::get_db_block]','write_verilog /work/diagnostic/before.v','write_def /work/diagnostic/before.def','set old_status [dict create]','foreach inst [$block getInsts] {dict set old_status [$inst getName] [$inst getPlacementStatus]; $inst setPlacementStatus FIRM}']
for n,r in p['resizes'].items():
 lines += ['set inst [$block findInst '+lit(n)+']','if {[[$inst getMaster] getName] ne '+lit(r['before'])+'} {error {Unexpected resize source}}','set master [[ord::get_db] findMaster '+lit(r['after'])+']','if {$master eq "NULL" || ![$inst swapMaster $master]} {error {Exact master swap failed}}','$inst setOrient '+r['orientation'],'$inst setLocation '+' '.join(map(str,r['bbox_dbu'][:2]))]
for a in p['additions']:
 lines += ['if {[$block findInst '+lit(a['instance'])+'] ne "NULL" || [$block findNet '+lit(a['new_net'])+'] ne "NULL"} {error {ECO name collision}}','set buffer [odb::dbInst_create $block [[ord::get_db] findMaster '+lit(a['master'])+'] '+lit(a['instance'])+']','set branch [odb::dbNet_create $block '+lit(a['new_net'])+']','$buffer setOrient '+a['orientation'],'$buffer setLocation '+' '.join(map(str,a['bbox_dbu'][:2])),'$buffer setPlacementStatus PLACED','set source [$block findNet '+lit(a['source_net'])+']','set sink [[$block findInst '+lit(a['endpoint'])+'] findITerm D]','if {[$sink getNet] ne $source} {error {Unexpected terminal D source}}','[$buffer findITerm A] connect $source','[$buffer findITerm X] connect $branch','[$buffer findITerm VDD] connect [$block findNet VPWR]','[$buffer findITerm VSS] connect [$block findNet VGND]','$sink disconnect','$sink connect $branch']
lines += ['foreach inst [$block getInsts] {set name [$inst getName]; if {[dict exists $old_status $name]} {$inst setPlacementStatus [dict get $old_status $name]}}','check_placement -verbose','write_verilog /work/diagnostic/after.v','write_def /work/diagnostic/candidate.def','write_db /work/diagnostic/candidate.odb','check_power_grid -net VPWR -error_file /work/diagnostic/VPWR-grid-errors.rpt','check_power_grid -net VGND -error_file /work/diagnostic/VGND-grid-errors.rpt']
(HERE/'edit.tcl').write_text('\n'.join(lines)+'\n')
