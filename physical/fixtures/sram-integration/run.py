"""One hierarchical macro diagnostic; preserves source and private deck history."""
from collections import Counter
from pathlib import Path
import hashlib
import argparse
import json
import os
import shutil
import subprocess
import sys
import time

CASE = Path(__file__).resolve().parent
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--macro-gds', type=Path, required=True)
parser.add_argument('--macro-cdl', type=Path, required=True)
parser.add_argument('--pdk-deck', type=Path, required=True)
parser.add_argument('--fixtures', type=Path, required=True)
parser.add_argument('--output', type=Path, required=True)
args = parser.parse_args()
OUT = args.output.resolve()
MACRO = 'RM_IHPSG13_1P_512x64_c2_bm_bist'
GDS = args.macro_gds.resolve()
CDL = args.macro_cdl.resolve()
PDK = args.pdk_deck.resolve()
FIXTURES = args.fixtures.resolve()

def require(ok, message):
    if not ok:
        raise RuntimeError(message)

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def write(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')

def value(obj, name):
    item = getattr(obj, name)
    return item() if callable(item) else item

identities = json.loads((CASE / 'inputs.json').read_text())
require(sha(GDS) == identities['macro_gds_sha256'], 'Changed supplied GDS')
require(sha(CDL) == identities['macro_cdl_sha256'], 'Changed supplied CDL')
require(sha(FIXTURES / 'check_inputs.py') == identities['fixture_helper_sha256'], 'Changed model adapter')
deck_files = {str(p.relative_to(PDK)): sha(p) for p in PDK.rglob('*') if p.is_file()}
require(deck_files == identities['deck_sha256'], 'Changed pinned LVS deck')
require(not OUT.exists(), 'Refuse to overwrite experiment output')
OUT.mkdir(parents=True)
sys.path.insert(0, str(FIXTURES))
from check_inputs import translate
source = CDL.read_text()
adapted = translate(source, {'width_um': 0.26, 'length_um': 0.6})
require(source.count('lvsres') - adapted.count('lvsres') == 1, 'Unexpected model translation')
cdl = OUT / (MACRO + '.metal1.cdl')
cdl.write_text(adapted)
deck = OUT / 'deck'
shutil.copytree(PDK, deck)
path = deck / 'sg13cmos5l.lvs'
text = path.read_text()
replacements = [
    ('  target_netlist.simplify if SIMPLIFY',
     '  if SIMPLIFY\n    target_netlist.combine_devices\n'
     '    target_netlist.each_circuit { |c| c.purge_nets_keep_pins }\n  end'),
    ('  # === Aligns the extracted netlist vs. the schematic ===',
     (CASE / 'policy.rb').read_text() + '\n  # === Aligns the extracted netlist vs. the schematic ==='),
    ('  align\n', '  align\n  pw_after_align.call\n'),
    ('  #=== IGNORE EXTREME VALUES ===', '  pw_verify_prepared.call\n  #=== IGNORE EXTREME VALUES ==='),
    ('  #------------- COMPARISON RESULTS ---------------',
     '  pw_finish.call(success)\n  #------------- COMPARISON RESULTS ---------------'),
]
for before, after in replacements:
    require(text.count(before) == 1, 'Changed deck anchor')
    text = text.replace(before, after)
path.write_text(text)
changed = [str(p.relative_to(PDK)) for p in PDK.rglob('*') if p.is_file()
           and sha(p) != sha(deck / p.relative_to(PDK))]
require(changed == ['sg13cmos5l.lvs'], 'Unexpected private deck changes')
cmd = ['python3', '-B', str(deck / 'run_lvs.py'), '--layout=' + str(GDS),
       '--netlist=' + str(cdl), '--topcell=' + MACRO, '--run_mode=deep', '--run_dir=' + str(OUT / 'lvs')]
started = time.monotonic()
with (OUT / 'native.log').open('w') as f:
    result = subprocess.run(cmd, stdout=f, stderr=subprocess.STDOUT, timeout=480,
                            env=dict(os.environ, QT_QPA_PLATFORM='offscreen', OMP_NUM_THREADS='4',
                                     PINWHEEL_POLICY_REPORT=str(OUT / 'policy.json'),
                                     PINWHEEL_POLICY_CONTRACT=str(CASE / 'contract.json')))
log = (OUT / 'native.log').read_text()
report = dict(command=cmd, exit_code=result.returncode, seconds=round(time.monotonic() - started, 3),
              qualification=False, changed_private_deck_files=changed,
              source_gds_sha256=sha(GDS), source_cdl_sha256=sha(CDL),
              adapted_cdl_sha256=sha(cdl),
              native_final_pass='Congratulations! Netlists match.' in log,
              native_final_fail="ERROR : Netlists don't match" in log)
if (OUT / 'policy.json').exists():
    report['policy'] = json.loads((OUT / 'policy.json').read_text())
database = OUT / 'lvs' / (MACRO + '.lvsdb')
if database.exists():
    import klayout.db as db
    nl = db.LayoutVsSchematic()
    nl.read(str(database))
    xref = nl.xref()
    rows = []
    for pair in xref.each_circuit_pair():
        row = {'status': str(pair.status())}
        for side, c in [('layout', pair.first()), ('schematic', pair.second())]:
            row[side] = None if c is None else dict(name=c.name,
                devices=dict(Counter(d.device_class().name for d in c.each_device())),
                pins=[value(p, 'name') for p in c.each_pin()],
                children=dict(Counter(s.circuit_ref().name for s in c.each_subcircuit())))
        for kind, iterator in [('device', xref.each_device_pair), ('net', xref.each_net_pair),
                               ('pin', xref.each_pin_pair), ('subcircuit', xref.each_subcircuit_pair)]:
            row[kind + '_statuses'] = dict(Counter(str(p.status()) for p in iterator(pair)))
        rows.append(row)
    report['circuits'] = rows
    report['database_match'] = bool(rows) and all(r['status'] == 'Match' for r in rows)
write(OUT / 'report.json', report)
require(result.returncode == 0 and report.get('policy', {}).get('status') in ['native_match', 'native_no_match']
        and 'circuits' in report, 'Incomplete hierarchical comparison; inspect preserved output')
print(json.dumps({k: report[k] for k in ['exit_code', 'seconds', 'native_final_pass', 'native_final_fail', 'database_match']}, indent=2), flush=True)
