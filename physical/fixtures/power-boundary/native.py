"""Container worker: read the saved chip, change only analysis assumptions."""
import json
import os
from pathlib import Path
import subprocess
import sys
from librelane.common import get_script_dir

spec_path = Path(sys.argv[1])
spec = json.loads(spec_path.read_text())
out = Path('/output')
scripts = get_script_dir()
os.environ['SCRIPTS_DIR'] = str(scripts)
os.environ['STEP_DIR'] = str(out)
tcl = '''source /probe/finalize-01/output/flow/05-openroad-irdropreport/_env.tcl
# Reconstruct the three analysis-only variables LibreLane normally passes in
# its process environment (they are not included in the saved _env.tcl).
set ::env(_LIB_CORNER_0) [concat [list $::env(DEFAULT_CORNER)] [dict get $::env(CELL_LIBS) $::env(DEFAULT_CORNER)] [list /work/core/experiments/paired-balance-place-02/macro/RM_IHPSG13_1P_512x64_c2_bm_bist_typ_1p20V_25C.lib]]
set ::env(_SDC_IN) $::env(PNR_SDC_FILE)
set ::env(_PNR_EXCLUDED_CELLS) {}
source $::env(SCRIPTS_DIR)/openroad/common/io.tcl
read_current_odb
source $::env(SCRIPTS_DIR)/openroad/common/set_power_nets.tcl
source $::env(SCRIPTS_DIR)/openroad/common/set_rc.tcl
read_spef $::env(CURRENT_SPEF_DEFAULT_CORNER)
utl::set_debug_level PSM solve 3
'''
if spec.get('vcd'):
    tcl += 'read_vcd -scope power_tb.dut {' + spec['vcd'] + '}\n'
tcl += '''report_activity_annotation > /output/activity.rpt
report_power -digits 9 -format json > /output/power.json
report_power -digits 9 > /output/power.rpt
'''
tcl += f'set_pdnsim_source_settings -external_resistance {spec["external_resistance_ohm_per_node"]}\n'
for net, voltage in [('VPWR', 1.2), ('VGND', 0)]:
    tcl += f'set_pdnsim_net_voltage -net {net} -voltage {voltage}\n'
    args = f'-net {net}'
    if spec.get('sources'):
        args += ' -vsrc {' + str(spec_path.parent / spec['sources'][net]) + '}'
    tcl += f'analyze_power_grid {args} -voltage_file /output/{net}.csv\n'
    if spec.get('export_source_nodes'):
        tcl += f'write_pg_spice {args} /output/{net}.spice\n'
tcl += 'exit\n'
(out / 'analysis.tcl').write_text(tcl)
subprocess.run(['openroad', '-version'], check=True)
subprocess.run(['openroad', '-exit', '-threads', '4', '-no_splash', '-metrics', '/output/metrics.json', '/output/analysis.tcl'], check=True)
# Keep the exported source identities; the full PG SPICE is also retained.
# This exporter omits external series resistance, so it is NOT a circuit replay
# of the resistance scenario. It audits only resolved source-node identity.
for net in ['VPWR', 'VGND']:
    p = out / f'{net}.spice'
    if p.exists():
        with p.open() as f:
            sources = [line.strip() for line in f if line.startswith('V')]
        (out / f'{net}-sources.json').write_text(json.dumps(sources, indent=2) + '\n')
