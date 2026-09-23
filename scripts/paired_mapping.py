"""Full paired-chip mapping, exact macro/state intake and bounded cell STA."""
from collections import Counter
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import re
import runpy
import shutil

from map_distribution import distribute, boundary_loads
from tiled_chip import FF, state_cut, project_pruned_state
from validation_run import sha

ROOT=Path(__file__).resolve().parents[1]
CAD=ROOT/'build/tools/oss-cad-suite/bin'
VIEWS=ROOT/'build/storage/macros'
MACRO='RM_IHPSG13_1P_512x64_c2_bm_bist'


def write(path,value):path.write_text(json.dumps(value,indent=2)+'\n')


def signal(module,name,width):
    bits=module['netnames'].get(name,{}).get('bits')
    if bits is None or len(bits)!=width:raise ValueError('missing paired signal: '+name)
    return bits


def binding(module,description):
    macros={n:c for n,c in module['cells'].items() if c['type'].startswith('RM_IHP')}
    if set(macros)!={'memory.storage'} or macros['memory.storage']['type']!=MACRO:
        raise ValueError('paired chip must contain exactly one 512x64 macro')
    expected=dict(A_CLK=module['ports']['clk']['bits'],A_MEN=['1'],A_DLY=['1'],
        A_ADDR=signal(module,'controller.mem_addr0',9),A_DIN=signal(module,'controller.mem_data',64),
        A_DOUT=signal(module,'controller.mem_q0',64),A_WEN=signal(module,'controller.mem_write',1),
        A_REN=signal(module,'controller.mem_read',1),A_BM=['1']*64,
        A_BIST_CLK=['0'],A_BIST_EN=['0'],A_BIST_MEN=['0'],A_BIST_WEN=['0'],A_BIST_REN=['0'],
        A_BIST_ADDR=['0']*9,A_BIST_DIN=['0']*64,A_BIST_BM=['0']*64)
    cell=macros['memory.storage']
    if cell['connections']!=expected or cell['port_directions']!={
            p:'output' if p=='A_DOUT' else 'input' for p in expected}:
        raise ValueError('changed paired macro terminal')
    ports={'clk':module['ports']['clk']}
    for direction,key in [('input','inputs'),('output','outputs')]:
        for p in description[key]:
            if not p['name'].startswith('mem_'):
                ports[p['name']]=dict(direction=direction,
                                     bits=signal(module,'controller.'+p['name'],p['width']))
    if ports!=module['ports']:raise ValueError('paired package boundary mismatch')
    return macros


def cut(module,description):
    """Validate package/macro wiring before exposing the actual response pins.

    The shared exact-state cut then accounts for every surviving FF and rejects
    omitted state, unsupported clocks/resets and unbound derived state.
    """
    macros=binding(module,description)
    view=deepcopy(module)
    for name in macros:del view['cells'][name]
    desc=deepcopy(description)
    view['ports']={'clk':module['ports']['clk']}
    for direction,key in [('input','inputs'),('output','outputs')]:
        for p in desc[key]:
            bits=signal(module,'controller.'+p['name'],p['width'])
            view['ports'][p['name']]=dict(direction=direction,bits=bits)
            view['netnames'][p['name']]=dict(hide_name=0,bits=bits,attributes={})
    for slot in desc['registers']:
        slot['name']='controller.'+slot['name']
    # Yosys represents six unused reserved token bits as literal x, rather
    # than named undriven wires. Accept only those exact coordinates, and
    # only when no real cell or port contains x. Give the state census fresh
    # unconnected identities; no functional connection is changed or masked.
    observed=[b for c in view['cells'].values() for bs in c['connections'].values() for b in bs]
    observed += [b for p in view['ports'].values() for b in p['bits']]
    if 'x' in observed or 'z' in observed:raise ValueError('unknown value in live paired logic')
    all_bits=observed+[b for n in view['netnames'].values() for b in n['bits']]
    fresh=max(b for b in all_bits if isinstance(b,int))+1
    unused=[]
    for slot in desc['registers']:
        bits=view['netnames'][slot['name']]['bits']
        for k,b in enumerate(bits):
            if b=='x':
                if slot['name'] not in ['controller.r_boot_b0','controller.r_boot_b1','controller.r_current'] or k not in [30,31]:
                    raise ValueError('unexpected unknown paired state coordinate')
                unused.append([slot['name'],k]);bits[k]=fresh;fresh+=1
    result,projection=state_cut(view,desc,True)
    projection['unused_reserved_x_coordinates']=unused
    return result,projection


def metrics(data,description):
    module=data['modules']['tt_um_pinwheel']
    binding(module,description)
    counts=Counter(c['type'] for c in module['cells'].values() if c['type']!='$scopeinfo')
    areas={kind:float(data['modules'][kind]['attributes']['area']) for kind in counts}
    loads=Counter()
    clock=module['ports']['clk']['bits'][0]
    for c in module['cells'].values():
        if c['type']=='$scopeinfo':continue
        for p,bits in c['connections'].items():
            if c['port_directions'][p]=='input':loads.update(b for b in bits if isinstance(b,int) and b!=clock)
    for p in module['ports'].values():
        if p['direction']=='output':loads.update(b for b in p['bits'] if isinstance(b,int))
    return dict(cells=sum(counts.values()),flip_flops=counts[FF],macros=counts[MACRO],
                standard_cell_area_um2=round(sum(areas[k]*n for k,n in counts.items() if k!=MACRO),4),
                macro_area_um2=areas[MACRO],total_cell_and_macro_area_um2=round(sum(areas[k]*n for k,n in counts.items()),4),
                maximum_signal_fanout=max(loads.values()),cell_types=dict(sorted(counts.items())))


def mapping(run,out,description,report):
    helper=runpy.run_path(str(ROOT/'scripts/check-map-tile.py'))
    libraries=helper['pinned_libraries']()
    report['libraries_sha256']={k:sha(v) for k,v in libraries.items()}
    def yosys(label,lines,reject=None):
        script=out/(label+'.ys');script.write_text('\n'.join(map(str,lines))+'\n')
        return run([CAD/'yosys','-Q','-T','-s',script],label,reject=reject)
    (out/'abc.constr').write_text('set_driving_cell sg13cmos5l_buf_2\nset_load 10\n')
    (out/'abc-eight.script').write_text('strash; &get -n; &fraig -x; &put; scorr; dc2; dretime; '
        'retime -o -D 10000; strash; &get -n; &dch -f; &nf -D 10000; '
        '&put; buffer -N 8; upsize -D 10000; dnsize -D 10000; stime -p\n')
    typical_macro=VIEWS/(MACRO+'_typ_1p20V_25C.lib')
    generic=out/'generic.json'
    yosys('generic',[f'read_liberty -lib {typical_macro}',
        f'read_verilog -sv {out}/chip.sv {ROOT}/test/paired_chip.sv',
        'synth -top tt_um_pinwheel -flatten -noabc','dffunmap','clean','check -assert',f'write_json {generic}'])
    reference,projection=cut(json.loads(generic.read_text())['modules']['tt_um_pinwheel'],description)
    report['generic_state_projection']=projection
    write(out/'reference-cut.json',dict(modules=dict(reference=reference)))
    report['variants']={}
    for corner,lib in libraries.items():
        folder=out/corner;folder.mkdir()
        macro=VIEWS/(MACRO+('_typ_1p20V_25C.lib' if corner=='typical' else '_slow_1p08V_125C.lib'))
        mapped=folder/'mapped.json'
        yosys(corner+'-map',[f'read_liberty -lib {lib}',f'read_liberty -lib {macro}',
            f'read_verilog -sv {out}/chip.sv {ROOT}/test/paired_chip.sv',
            'synth -top tt_um_pinwheel -flatten -noabc',f'dfflibmap -liberty {lib}',
            f'abc -liberty {lib} -constr {out}/abc.constr -D 10000 -script {out}/abc-eight.script',
            'clean','check -assert',f'write_json {mapped}'])
        data=json.loads(mapped.read_text())
        before=metrics(data,description)
        data,distribution=distribute(data,'tt_um_pinwheel',{},limit=8,
                                      fixed_cells=['memory.storage'],prefix='paired_distribution_')
        if any(n['loads']>8 for n in boundary_loads(data['modules'],'tt_um_pinwheel',['memory.storage'])):
            raise ValueError('unrepaired paired distribution fanout')
        write(folder/'buffered.json',data);write(folder/'distribution.json',distribution)
        yosys(corner+'-save',[f'read_json {folder}/buffered.json','hierarchy -check -top tt_um_pinwheel',
            'clean','check -assert',f'write_verilog -noattr -noexpr {folder}/design.v'])
        yosys(corner+'-readback',[f'read_liberty -lib {lib}',f'read_liberty -lib {macro}',
            f'read_verilog {folder}/design.v','hierarchy -check -top tt_um_pinwheel',
            'check -assert',f'write_json {folder}/readback.json'])
        back=json.loads((folder/'readback.json').read_text())
        measured=metrics(back,description)
        if measured!=metrics(data,description) or measured['maximum_signal_fanout']>8:
            raise ValueError('paired readback census or fanout mismatch')
        candidate,cp=cut(back['modules']['tt_um_pinwheel'],description)
        pr=project_pruned_state(reference,candidate,cp,projection['pruned_state_positions'])
        write(folder/'reference-cut.json',dict(modules=dict(reference=pr)))
        write(folder/'candidate-cut.json',dict(modules=dict(candidate=candidate)))

        def prove(path,label,reject=None):
            log=yosys(label,[f'read_liberty -ignore_miss_func {lib}',f'read_json {folder}/reference-cut.json',
                f'read_json {path}','miter -equiv -flatten -make_outputs reference candidate miter',
                'hierarchy -check -top miter','flatten','opt -full',
                'sat -verify -prove trigger 0 -set-def-inputs miter'],reject)
            if not reject and 'SAT proof finished - no model found: SUCCESS!' not in log:
                raise ValueError('incomplete full paired-controller equivalence')
        prove(folder/'candidate-cut.json',corner+'-proof')
        if corner=='typical':
            mutant=deepcopy(candidate)
            cell=next(c for c in mutant['cells'].values() if c['type']=='sg13cmos5l_buf_1')
            cell['type']='sg13cmos5l_inv_1';cell['connections']['Y']=cell['connections'].pop('X')
            cell['port_directions']['Y']=cell['port_directions'].pop('X')
            write(folder/'negative-cut.json',dict(modules=dict(candidate=mutant)))
            prove(folder/'negative-cut.json','inverted-buffer-negative','proof did fail')
        report['variants'][corner]=dict(metrics=measured,state_projection=cp,
            unbuffered_metrics=before,distribution=distribution,mapped_sha256=sha(folder/'design.v'))
        shutil.copyfile(lib,folder/'cells.lib');shutil.copyfile(macro,folder/'macro.lib')
    return libraries


def timing(run,out,description,report):
    helper=runpy.run_path(str(ROOT/'scripts/check-sram-timing.py'))
    lock=json.loads((ROOT/'tools/physical-toolchain.json').read_text())
    info=json.loads(run(['docker','image','inspect',lock['container_tag']],'timing-image'))[0]
    runtime={k:v for k,v in info['Config'].items() if v is not None}
    digest=hashlib.sha256(json.dumps(runtime,sort_keys=True).encode()).hexdigest()
    if (info['Architecture']!='arm64' or info['Os']!='linux' or
        info['RootFS']['Layers']!=lock['container_rootfs_diff_ids'] or digest!=lock['container_runtime_config_sha256']):
        raise ValueError('unpinned paired timing image')
    report.update(tool_image=info['Id'],runtime_config_sha256=digest,containers={})
    for corner in ['typical','slow']:
        folder=out/corner
        data=json.loads((folder/'readback.json').read_text())
        module=data['modules']['tt_um_pinwheel']
        flops={c['connections']['Q'][0]:name for name,c in module['cells'].items() if c['type']==FF}
        entry=[]
        for name,width in [('cached',20),('samples',16),('levels',3),('enabled',3),
                           ('mode',3),('remaining',8),('wait_left',8),('payload',8)]:
            entry += [flops[b]+'/D' for b in signal(module,'controller.r_'+name,width) if b in flops]
        if len(set(entry))!=len(entry) or not entry or any(any(x in p for x in '{}[]\\\n\r') for p in entry):
            raise ValueError('ambiguous paired entry state endpoints')
        extra='''set responses [get_pins {memory.storage/A_DOUT*}]
set addresses [get_pins {memory.storage/A_ADDR*}]
if {[llength $responses] != 64 || [llength $addresses] != 9} { error "Missing paired macro paths" }
puts "PINWHEEL_SRAM_TO_SRAM"
report_checks -from $responses -to $addresses -path_delay max -group_path_count 3 -fields {slew cap fanout} -format full_clock_expanded
set entry [get_pins [list '''+' '.join('{'+p+'}' for p in entry)+''']]
if {[llength $entry] != '''+str(len(entry))+'''} { error "Missing entry state pins" }
puts "PINWHEEL_PARAMETER_ENTRY"
report_checks -from $responses -to $entry -path_delay max -group_path_count 3 -fields {slew cap fanout} -format full_clock_expanded
'''
        script=helper['timing_script'](False,extra).replace('read_verilog design.v','read_liberty macro.lib\nread_verilog design.v')
        (folder/'timing.tcl').write_text(script)
        log=helper['run_sta'](run,folder,info['Id'],'pinwheel-'+out.name+'-'+corner,
                              report['containers'],corner+'-sta')
        result=helper['parse_timing'](log)
        part=log.split('PINWHEEL_PARAMETER_ENTRY',1)[1].split('PINWHEEL_',1)[0]
        slacks=re.findall(r'(-?\d+(?:\.\d+)?)\s+slack \((?:MET|VIOLATED)\)',part)
        if not slacks or 'Startpoint:' not in part:raise ValueError('missing parameter/entry timing')
        result['sram_to_entry_slack_ns']=min(map(float,slacks))
        result['entry_state_endpoints']=len(entry)
        report['variants'][corner]['cell_timing']=result
