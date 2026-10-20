"""Small native ODB buffer-partition detector and placement controls.

This deliberately uses a 17-cell fixture, not a qualified streaming device.
The full native executor's separate 6039-FF source guard is never relaxed.
"""
import argparse
import json
from pathlib import Path

from streaming_tt_apply_fanout import execute, checked_tcl
from streaming_tt_export_odb import export_block
from streaming_tt_fanout import build_plan, verify_result
from streaming_tt_intake import dependency_closure
from streaming_tt_physical import require, sha, write
from streaming_tt_simulation import libraries


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--pdk', required=True, type=Path)
    parser.add_argument('--out', required=True, type=Path)
    args = parser.parse_args(); args.out.mkdir(parents=True, exist_ok=False)
    top = 'pinwheel_native_fanout_control'; root = Path(__file__).resolve().parents[1]
    cellroot = args.pdk/'ihp-sg13cmos5l/libs.ref/sg13cmos5l_stdcell'
    techlef, celllef = cellroot/'lef/sg13cmos5l_tech.lef', cellroot/'lef/sg13cmos5l_stdcell.lef'
    pins = {'typ': ('typ_1p20V_25C', '34163f3e7de9f854afac57332ba06f1739b78e7ac35660a8a5ddd39c570124ad'),
        'fast': ('fast_1p32V_m40C', 'af12d75a72d19648fa690027d29843fbae550aa91f4e40dd3339c7116d6e425d'),
        'slow': ('slow_1p08V_125C', '3ee222c580ba33acb2131ac2bf224ff8ee9700751835b73aaec72b670bb31d3c')}
    corners = {name: dict(path=str(cellroot/('lib/sg13cmos5l_stdcell_'+suffix+'.lib')), sha256=digest)
        for name, (suffix, digest) in pins.items()}
    closure = dependency_closure(root, ['scripts/streaming_tt_fanout_control.py'])
    files = [techlef, celllef, *(Path(value['path']) for value in corners.values()), *(root/name for name in closure['files'])]
    hashes = {str(path): sha(path) for path in files}
    library, functions = libraries(corners, {'sg13cmos5l_buf_8', 'sg13cmos5l_antennanp'})
    import odb
    from openroad import Tech, Design
    database = odb.dbDatabase.create(); odb.read_lef(database, str(techlef)); odb.read_lef(database, str(celllef))
    chip = odb.dbChip_create(database, database.getTech()); block = odb.dbBlock_create(chip, top)
    unit = block.getDbUnitsPerMicron(); require(unit == 1000, 'Unexpected actual fixture DB units')
    block.setDieArea(odb.Rect(0, 0, 96000, 15120))
    nets = {}
    for name, kind in (('VPWR', 'POWER'), ('VGND', 'GROUND'), ('clk', 'CLOCK'), ('leaf', 'CLOCK')):
        nets[name] = odb.dbNet_create(block, name); nets[name].setSigType(kind)
    for name, direction in (('VPWR', 'INOUT'), ('VGND', 'INOUT'), ('clk', 'INPUT')):
        term = odb.dbBTerm_create(nets[name], name); term.setIoType(direction); term.setSigType(nets[name].getSigType())
        pin = odb.dbBPin_create(term); pin.setPlacementStatus('PLACED')
        layer = database.getTech().findLayer('Metal2' if name == 'clk' else 'Metal1')
        y = {'VPWR': 3500, 'VGND': 0, 'clk': 1500}[name]
        odb.dbBox_create(pin, layer, 0, y, 480, y+400)
    def instance(name, master, x, signal):
        inst = odb.dbInst_create(block, database.findMaster(master), name)
        inst.setOrient('R0'); inst.setLocation(x, 0); inst.setPlacementStatus('PLACED')
        for term in inst.getITerms():
            kind, pin = str(term.getMTerm().getSigType()), term.getMTerm().getName()
            if kind in ('POWER', 'GROUND'): term.connect(nets['VPWR' if kind == 'POWER' else 'VGND'])
            else: term.connect(nets[signal[pin]])
        return inst
    instance('source', 'sg13cmos5l_buf_8', 0, {'A': 'clk', 'X': 'leaf'})
    for index in range(16): instance('load'+str(index), 'sg13cmos5l_antennanp', 10080+2880*index, {'A': 'leaf'})
    reference = dict(modules={top: dict(ports={'clk': dict(direction='input', bits=[2])})})
    _, original = export_block(block, reference, top)
    plan, projected = build_plan(original, library)
    require(len(plan['operations']) == 1 and plan['balanced_public_clock_prefix_levels'] == 0,
        'Small native fixture did not exercise one equal-master clone')
    seed = args.out/'fixture-before-floorplan.odb'; odb.write_db(database, str(seed))
    tech = Tech(); tech.readLiberty(corners['typ']['path']); design = Design(tech); design.readDb(str(seed))
    fixture_journal = []
    checked_tcl(design, 'initialize_floorplan -die_area {0 0 96 30.24} '
        '-core_area {0.48 0 95.52 30.24} -site CoreSite', fixture_journal)
    source = args.out/'source.odb'
    checked_tcl(design, 'write_db {'+str(source)+'}', fixture_journal)
    source_sha = sha(source)
    database, block = design.getDb(), design.getBlock()
    for operation in plan['operations']: execute(odb, database, block, operation)
    _, positive = export_block(block, reference, top); verify_result(original, positive, plan, library)
    journal = []
    checked_tcl(design, 'set_thread_count 1', journal)
    checked_tcl(design, 'detailed_placement -max_displacement {500 100}', journal)
    checked_tcl(design, 'check_placement -verbose', journal)
    target = args.out/'positive.odb'; checked_tcl(design, 'write_db {'+str(target)+'}', journal)
    checked_tcl(design, 'write_verilog {'+str(args.out/'positive.v')+'}', journal)
    reread = odb.dbDatabase.create(); odb.read_db(reread, str(target))
    _, positive = export_block(reread.getChip().getBlock(), reference, top)
    verify_result(original, positive, plan, library)
    controls = []
    error_journal = []
    try: checked_tcl(design, 'pinwheel_intentional_unknown_command', error_journal)
    except ValueError as error:
        require(len(error_journal) == 1 and error_journal[0]['tcl_catch_status'] == '1',
            'Intentional actual Tcl error did not return exact failed status')
        tcl_control = dict(rejected=True, native_command=error_journal[0], error=str(error))
    else: raise ValueError('Actual Tcl failure escaped status guard')
    missing_tech = Tech(); missing_tech.readLiberty(corners['typ']['path'])
    missing_clock = Design(missing_tech); missing_clock.readDb(str(target))
    missing_clock_block = missing_clock.getBlock()
    for pin in list(missing_clock_block.findBTerm('clk').getBPins()): odb.dbBPin_destroy(pin)
    require(not list(missing_clock_block.findBTerm('clk').getBPins()), 'Missing-clock-BPin mutation failed')
    odb.write_db(missing_clock.getDb(), str(args.out/'missing_clock_bpin.odb'))
    dpl_error_journal = []
    try: checked_tcl(missing_clock, 'detailed_placement -max_displacement {500 100}', dpl_error_journal)
    except ValueError as error:
        require(len(dpl_error_journal) == 1 and dpl_error_journal[0]['tcl_catch_status'] == '1'
            and dpl_error_journal[0]['tcl_result'] == 'DPL-0386',
            'Actual missing-clock-BPin DPL error did not return the exact failed status and event')
        dpl_control = dict(rejected=True, actual_positive_odb_re_read=True, clock_bpin_removed=True,
            native_command=dpl_error_journal[0], error=str(error))
    else: raise ValueError('Actual DPL-0386 failure escaped status guard')
    for name in ('moved_load', 'collapsed_power', 'clock_feedback'):
        negative = odb.dbDatabase.create(); odb.read_db(negative, str(target)); block = negative.getChip().getBlock()
        new = block.findInst(plan['operations'][0]['new_instance'])
        if name == 'moved_load':
            selected = plan['operations'][0]['loads'][0]
            block.findInst(selected[1]).findITerm(selected[2]).connect(block.findNet('clk'))
        elif name == 'collapsed_power': new.findITerm('VDD').connect(block.findNet('VGND'))
        else: new.findITerm('A').connect(block.findNet(plan['operations'][0]['new_net']))
        bad = args.out/(name+'.odb'); odb.write_db(negative, str(bad))
        actual = odb.dbDatabase.create(); odb.read_db(actual, str(bad))
        try:
            _, inventory = export_block(actual.getChip().getBlock(), reference, top)
            verify_result(original, inventory, plan, library)
        except ValueError as error:
            controls.append(dict(name=name, native_mutation_written_and_re_read=True, rejected=True, error=str(error)))
        else: raise ValueError('Actual native corruption escaped detection: '+name)
    require(hashes == {str(path): sha(path) for path in files} and sha(source) == source_sha,
        'Native detector control changed a frozen source input')
    artifacts = {path.name: sha(path) for path in args.out.iterdir() if path.is_file()}
    write(args.out/'report.json', dict(schema='pinwheel.streaming-tt-native-fanout-controls.v1', passed=True,
        qualified=False, physical_acceptance_claim=False, source_instances=17, added_positive_buffer_instances=1,
        streaming_device_state_qualification=False, actual_three_corner_functions=functions,
        actual_positive_partition_and_ODB_roundtrip=True, native_detailed_placement_and_check=True,
        native_tcl_commands=journal, native_tcl_all_success=all(row['tcl_catch_status'] == '0' for row in journal),
        native_fixture_floorplan_commands=fixture_journal,
        actual_native_tcl_error_control=tcl_control,
        actual_native_dpl_missing_clock_bpin_control=dpl_control,
        negative_controls=controls, input_sha256=hashes, inputs_unchanged=True, source_odb_unchanged=True,
        producer_dependency_closure=closure, artifacts_sha256=artifacts,
        boundary='Tiny actual stdcell-LEF ODB detector controls only. The full 6039-state device guard is unchanged; '
            'whole-device source correspondence, routing and physical signoff remain separate.'))


if __name__ == '__main__': main()
