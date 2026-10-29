"""Read-only geometric PG connectivity on one closed final 8x4 ODB.

Preparation is HOST only. Native execution requires a separate Root GO and the
campaign resource guard. PSM's short check is a stub: this leaf establishes no
cross-rail short, cell-internal GDS, package delivery, IR-drop or EM claim.
"""
import argparse
import hashlib
from pathlib import Path
import re
import shutil
import subprocess
import sys
import uuid

import process_group
import streaming_8x4_signoff_execute as V
from streaming_8x4_geometry import regular, require, sha
from streaming_tt_intake import dependency_closure

P=V.P
R=V.R
COMMIT='dcf36133a369abc8f3c5e5738cd4d82e4903c0e0'
SOURCE_MANIFEST_SHA256='7e20a6c7a1075fb1605fb9a49ec7eb93f84a5c424bc9f56afeb40ae0a2afb012'
ENTRIES=('scripts/streaming_8x4_power_grid.py','scripts/streaming_tt_export_odb.py','tools/physical-toolchain.json')
LEAF_SECONDS=180
OUTER_SECONDS=240
BOUNDARY=('Geometric same-rail open-path connectivity of all inventoried PG terminals, '
    'under OpenDB/LEF/via semantics. PSM checkShort is a stub. No cross-rail short, '
    'cell-internal GDS, package delivery, IR-drop, activity, EM or full physical acceptance.')
LAUNCHER='from streaming_8x4_power_grid import native\nnative("/work/pg/inputs/request.json")\n'


def bound(path):
    path=regular(path).resolve();return dict(path=str(path),sha256=sha(path))


def artifacts(root):
    root=Path(root).resolve()
    return {name:value for name,value in P.inventory(root).items() if name!='report.json'}


def source_evidence(root):
    root=Path(root).resolve();manifest=root/'manifest.json'
    require(sha(manifest)==SOURCE_MANIFEST_SHA256,'Pinned PSM source intake changed')
    value=P.read(manifest)
    require(value.get('schema')=='pinwheel.streaming-8x4-psm-source-intake.v1' and
        value.get('commit')==COMMIT and value.get('repository')=='https://github.com/The-OpenROAD-Project/OpenROAD' and
        value.get('native_executed') is False,'PSM source intake identity differs')
    expected={'manifest.json':SOURCE_MANIFEST_SHA256}
    for row in value['files']:
        name=row['path'];require(not Path(name).is_absolute() and '..' not in Path(name).parts and name not in expected,
            'Unsafe/duplicate PSM source member')
        data=regular(root/name).read_bytes()
        blob=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
        require(len(data)==row['bytes'] and sha(root/name)==row['sha256'] and blob==row['git_blob'],
            'Pinned PSM source bytes/blob differ')
        expected[name]=row['sha256']
    require(len(expected)==10 and P.inventory(root)==expected,'PSM source intake membership differs')
    return expected


def expected_rails(inventory):
    require(inventory.get('schema')=='pinwheel.streaming-tt-odb-inventory.v1' and
        inventory.get('power_connectivity_signed_off') is False,'Not canonical unqualified ODB inventory')
    rails={name:dict(signal_type=row['signal_type'],iterms=[],bterms=[]) for name,row in inventory['nets'].items()
        if row['signal_type'] in ('POWER','GROUND')}
    require(rails and {row['signal_type'] for row in rails.values()}=={'POWER','GROUND'},'Missing supply/ground rail')
    for name in rails:require(re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*',name),'Unsupported literal Tcl rail name')
    for name,instance in inventory['instances'].items():
        for pin,row in instance['terminals'].items():
            if row['signal_type'] not in ('POWER','GROUND'):continue
            net=row['net'];require(net in rails and rails[net]['signal_type']==row['signal_type'],
                'Disconnected/wrong-type inventoried PG ITerm')
            rails[net]['iterms'].append([name,pin,instance['master']])
    for name,row in inventory['power_bterms'].items():
        net=row['net'];require(net in rails and row['signal_type']==rails[net]['signal_type'],'Wrong PG BTerm net/type')
        rails[net]['bterms'].append(name)
    for row in rails.values():
        row['iterms'].sort();row['bterms'].sort()
        require(row['iterms'] and row['bterms'],'Vacuous required PG terminal inventory')
    return dict(sorted(rails.items()))


def inventory_totals(inventory):
    rails=expected_rails(inventory)
    return dict(instances=len(inventory['instances']),masters=len(inventory['masters']),
        physical_only_instances=len(inventory['physical_only_instances']),
        power_iterms=sum(len(row['iterms']) for row in rails.values()),
        power_bterms=sum(len(row['bterms']) for row in rails.values()),supply_nets=len(rails))


def closed_views(path):
    path=regular(path).resolve();report,preparation=V.closed_views(path)
    require(artifacts(path.parent)==report['artifact_sha256'],'Final view artifact membership differs')
    inventory=path.parent/'actual-signal/inventory.json'
    expected_rails(P.read(inventory))
    return report,preparation


def stage_producer(inputs):
    closure=dependency_closure(P.ROOT,ENTRIES)
    commit=subprocess.check_output(['git','rev-parse','HEAD'],cwd=P.ROOT,text=True,timeout=30).strip();sources={}
    for name in closure['files']:
        data=subprocess.check_output(['git','show',commit+':'+name],cwd=P.ROOT,timeout=30)
        require(hashlib.sha256(data).hexdigest()==sha(P.ROOT/name),'Commit new PG producer first: '+name)
        target=inputs/'producer'/name;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data)
        sources[name]=sha(target)
    return commit,sources,closure


def prepare(views_path,source_root,output):
    views_path=regular(views_path).resolve();views,original=closed_views(views_path)
    selected_runtime=P.read(views['target']['physical_report']['path'])['runtime']
    validate_runtime(views['runtime'],selected_runtime)
    source_root=Path(source_root).resolve();source_files=source_evidence(source_root)
    output=Path(output).absolute();require(not output.exists(),'Preserve prior PG owner')
    inputs=output/'inputs';inputs.mkdir(parents=True)
    commit,sources,closure=stage_producer(inputs)
    for name in source_files:
        target=inputs/'psm-source'/name;target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(source_root/name,target)
    for source,name in [(views_path.parent/'actual-signal/inventory.json','inventory.json'),
        (views_path.parent/'inputs/reference.json','reference.json')]:shutil.copyfile(source,inputs/name)
    target=views['target'];source_odb=regular(target['actual_odb']['path']).resolve()
    require(sha(source_odb)==target['actual_odb']['sha256'],'Selected final PG database changed')
    request=dict(schema='pinwheel.streaming-8x4-power-grid-request.v1',source_odb='/work/target.odb',
        source_odb_sha256=sha(source_odb),inventory_sha256=sha(inputs/'inventory.json'),
        reference_sha256=sha(inputs/'reference.json'),top=P.read(inputs/'inventory.json')['top'],
        rails=expected_rails(P.read(inputs/'inventory.json')),openroad_source_commit=COMMIT,
        leaf_timeout_seconds=LEAF_SECONDS,outer_timeout_seconds=OUTER_SECONDS,
        floorplanning=False,dont_require_terminals=False,qualified=False,physical_acceptance=False)
    P.write(inputs/'request.json',request)
    result=dict(schema='pinwheel.streaming-8x4-power-grid-preparation.v1',views_report=bound(views_path),
        target=target,physical_candidate=views['physical_candidate'],source_odb=bound(source_odb),
        runtime=selected_runtime,
        source_evidence_root=str(source_root),source_evidence_sha256=source_files,
        producer_commit=commit,producer_sha256=sources,producer_dependency_closure=closure,
        input_sha256=P.inventory(inputs),executed=False,qualified=False,physical_acceptance=False,boundary=BOUNDARY)
    P.write(output/'preparation.json',result);return result


def verify_preparation(output):
    output=Path(output).absolute();packet=P.read(output/'preparation.json')
    require(packet.get('schema')=='pinwheel.streaming-8x4-power-grid-preparation.v1' and
        packet.get('executed') is False and packet.get('physical_acceptance') is False and
        P.inventory(output/'inputs')==packet['input_sha256'],'PG preparation contract/membership differs')
    path=packet['views_report'];require(sha(path['path'])==path['sha256'],'PG final views receipt changed')
    views,_=closed_views(path['path'])
    require(views['target']==packet['target'] and views['physical_candidate']==packet['physical_candidate'] and
        packet['source_odb']==bound(views['target']['actual_odb']['path']),'PG selected physical candidate differs')
    require(packet['runtime']==P.read(packet['target']['physical_report']['path'])['runtime'],
        'PG selected physical runtime authority changed')
    validate_runtime(views['runtime'],packet['runtime'])
    require(source_evidence(packet['source_evidence_root'])==packet['source_evidence_sha256']==
        source_evidence(output/'inputs/psm-source'),'PG source evidence differs')
    require(dependency_closure(P.ROOT,ENTRIES)==packet['producer_dependency_closure'] and
        set(packet['producer_sha256'])==set(packet['producer_dependency_closure']['files']),
        'PG producer closure membership differs')
    for name,value in packet['producer_sha256'].items():
        require(sha(P.ROOT/name)==value==sha(output/'inputs/producer'/name),'PG producer changed: '+name)
        committed=subprocess.check_output(['git','show',packet['producer_commit']+':'+name],cwd=P.ROOT,timeout=30)
        require(hashlib.sha256(committed).hexdigest()==value,'PG producer differs from its original committed source')
    request=P.read(output/'inputs/request.json')
    require(request==dict(schema='pinwheel.streaming-8x4-power-grid-request.v1',source_odb='/work/target.odb',
        source_odb_sha256=packet['source_odb']['sha256'],inventory_sha256=sha(output/'inputs/inventory.json'),
        reference_sha256=sha(output/'inputs/reference.json'),top=P.read(output/'inputs/inventory.json')['top'],
        rails=expected_rails(P.read(output/'inputs/inventory.json')),openroad_source_commit=COMMIT,
        leaf_timeout_seconds=LEAF_SECONDS,outer_timeout_seconds=OUTER_SECONDS,
        floorplanning=False,dont_require_terminals=False,qualified=False,physical_acceptance=False),'PG request differs')
    return packet


def positive_rect(box):
    require(box.xMin()<box.xMax() and box.yMin()<box.yMax(),'Empty/inverted PG pin/shape')
    return [box.xMin(),box.yMin(),box.xMax(),box.yMax()]


def pin_shapes(boxes):
    """Conservative supported pin geometry; never silently ignore any box.

    The actual template/cell PG pins use routing rectangles. Via-only/nonrouting
    pin boxes are explicitly blocked here rather than counted as PSM terminals.
    Special-wire vias are separately required and checked by PSM's via graph.
    """
    boxes=list(boxes);require(boxes,'PG terminal has no physical pin boxes')
    rows=[]
    for box in boxes:
        require(not box.isVia(),'Unsupported via PG pin geometry; no terminal may be skipped')
        layer=box.getTechLayer();require(layer is not None and layer.getRoutingLevel()>0,'Nonrouting PG pin geometry')
        rows.append(dict(layer=layer.getName(),bounds_dbu=positive_rect(box)))
    return sorted(rows,key=lambda row:(row['layer'],row['bounds_dbu']))


def census(block,inventory):
    expected=expected_rails(inventory);nets={net.getName():net for net in block.getNets()};result={}
    require({name for name,net in nets.items() if str(net.getSigType()) in ('POWER','GROUND')}==set(expected),
        'Actual PG net membership differs')
    for name,wanted in expected.items():
        net=nets[name];iterms=[];bterms=[];swires=list(net.getSWires());via_count=0;wire_shapes=0
        for term in net.getITerms():
            inst=term.getInst();master=inst.getMaster();mterm=term.getMTerm()
            require(inst.isPlaced(),'PSM would skip an unplaced PG instance')
            positive_rect(term.getBBox())
            require(term.getNet().getName()==name and str(mterm.getSigType())==wanted['signal_type'],'Actual PG ITerm rail/type differs')
            mpins=list(mterm.getMPins());require(mpins,'PG ITerm has no MPins')
            shapes=[pin_shapes(pin.getGeometry()) for pin in mpins]
            iterms.append(dict(instance=inst.getName(),pin=mterm.getName(),master=master.getName(),
                instance_placed=True,bbox_dbu=positive_rect(term.getBBox()),mpins=shapes))
        require(sorted([row['instance'],row['pin'],row['master']] for row in iterms)==wanted['iterms'],
            'Actual PG ITerm census omits/adds canonical terminals')
        for term in net.getBTerms():
            require(str(term.getSigType())==wanted['signal_type'],'PG BTerm type differs')
            pins=[]
            for pin in term.getBPins():
                status=str(pin.getPlacementStatus());require(status in ('PLACED','LOCKED','FIRM','COVER'),'Unplaced PG BPin')
                pins.append(dict(placement_status=status,boxes=pin_shapes(pin.getBoxes())))
            require(pins,'Required PG BTerm has no BPins');bterms.append(dict(name=term.getName(),bpins=pins))
        require(sorted(row['name'] for row in bterms)==wanted['bterms'],'Actual PG BTerm census differs')
        for wire in swires:
            boxes=list(wire.getWires());require(boxes,'Empty PG special wire')
            for box in boxes:
                positive_rect(box)
                if box.isVia():via_count+=1
                else:
                    layer=box.getTechLayer();require(layer is not None and layer.getRoutingLevel()>0,'Nonrouting PG SWire')
                    wire_shapes+=1
        require(swires and via_count>0 and wire_shapes>0,'Vacuous PG special wire/via network')
        result[name]=dict(signal_type=wanted['signal_type'],iterms=sorted(iterms,key=lambda row:(row['instance'],row['pin'])),
            bterms=sorted(bterms,key=lambda row:row['name']),iterm_count=len(iterms),bterm_count=len(bterms),
            bpin_count=sum(len(row['bpins']) for row in bterms),swire_count=len(swires),
            swire_routing_shapes=wire_shapes,swire_vias=via_count,skipped_iterms=0,skipped_bpins=0)
    return result


def validate_census(value,inventory):
    expected=expected_rails(inventory);require(set(value)==set(expected),'PG census rail membership differs')
    for name,row in value.items():
        wanted=expected[name]
        require(row['signal_type']==wanted['signal_type'] and row['skipped_iterms']==0 and row['skipped_bpins']==0 and
            row['iterm_count']==len(row['iterms'])==len(wanted['iterms']) and
            row['bterm_count']==len(row['bterms'])==len(wanted['bterms']) and
            sorted([r['instance'],r['pin'],r['master']] for r in row['iterms'])==wanted['iterms'] and
            sorted(r['name'] for r in row['bterms'])==wanted['bterms'],'PG census canonical terminal totals differ')
        for term in row['iterms']:
            require(term['instance_placed'] is True and term['mpins'],'PG census has skipped/unplaced ITerm')
            coords=term['bbox_dbu'];require(len(coords)==4 and coords[0]<coords[2] and coords[1]<coords[3],'Invalid PG ITerm bbox')
            for shapes in term['mpins']:validate_shapes(shapes)
        require(row['bpin_count']==sum(len(term['bpins']) for term in row['bterms'])>0,'PG BPin census total differs')
        for term in row['bterms']:
            require(term['bpins'],'Missing PG BPin')
            for pin in term['bpins']:
                require(pin['placement_status'] in ('PLACED','LOCKED','FIRM','COVER'),'PG census includes unplaced BPin')
                validate_shapes(pin['boxes'])
        require(all(type(row[key]) is int and row[key]>0 for key in
            ('swire_count','swire_routing_shapes','swire_vias')),'Vacuous PG wire/via census')
    return value


def validate_shapes(shapes):
    require(type(shapes) is list and shapes,'Missing PG routing shapes')
    for shape in shapes:
        c=shape['bounds_dbu'];require(type(shape['layer']) is str and shape['layer'] and len(c)==4 and
            all(type(x) is int for x in c) and c[0]<c[2] and c[1]<c[3],'Malformed PG routing rectangle')


def caught(design,command):
    status=design.evalTclString('catch {'+command+'} _pinwheel_pg_message')
    message=design.evalTclString('set _pinwheel_pg_message')
    require(str(status)=='0','OpenROAD PG query failed: '+str(message));return str(message)


def revision_identity(version,describe):
    """The pinned API's version is authoritative; describe may be empty.

    OpenRoad.i exposes getVersion/getGitDescribe separately. In the actual
    pinned replay runtime, openroad_version returned the full commit while
    openroad_git_describe returned an empty string. Preserve both raw values;
    a nonempty optional description must contain the same complete revision.
    """
    require(type(version) is str and type(describe) is str,'Unsupported PG version observations')
    tokens=lambda value:{token for token in re.findall(r'[0-9a-f]+',value) if len(token)>=40}
    require(tokens(version)=={COMMIT},'PG required full OpenROAD version differs/empty')
    require(not describe.strip() or tokens(describe)=={COMMIT},
        'PG optional OpenROAD description conflicts/lacks full revision')
    return COMMIT


def observe_revision(design):
    version=caught(design,'ord::openroad_version')
    describe=caught(design,'ord::openroad_git_describe')
    revision_identity(version,describe)
    return dict(openroad_version=version,openroad_git_describe=describe)


def native(request_path):
    """Invoked only by OpenROAD embedded Python, no child tools or DB writes."""
    from openroad import Tech,Design
    from streaming_tt_export_odb import export_block
    request=P.read(request_path);root=Path('/work/pg');inputs=root/'inputs'
    require(request.get('schema')=='pinwheel.streaming-8x4-power-grid-request.v1' and
        request.get('floorplanning') is False and request.get('dont_require_terminals') is False and
        request.get('openroad_source_commit')==COMMIT and request.get('leaf_timeout_seconds')==LEAF_SECONDS and
        request.get('outer_timeout_seconds')==OUTER_SECONDS,'Not strict full-terminal PG request')
    frozen={request['source_odb']:request['source_odb_sha256'],str(inputs/'inventory.json'):request['inventory_sha256'],
        str(inputs/'reference.json'):request['reference_sha256']}
    require(all(sha(path)==pin for path,pin in frozen.items()),'PG Native input changed')
    design=Design(Tech());design.readDb(request['source_odb']);block=design.getBlock()
    revision=observe_revision(design)
    inventory=P.read(inputs/'inventory.json');_,actual=export_block(block,P.read(inputs/'reference.json'),request['top'])
    require(actual==inventory and expected_rails(actual)==request['rails'],'Same-ODB canonical inventory differs')
    measured=census(block,inventory);validate_census(measured,inventory)
    caught(design,'set_debug_level PSM stats 1');checks=[]
    for index,name in enumerate(request['rails']):
        error=root/('rail-'+str(index)+'-errors.rpt');error.write_bytes(b'')
        # Fixed marker tokens and validated rail identifiers prevent Tcl interpolation.
        caught(design,'puts {PINWHEEL_PG_BEGIN '+name+'}; flush stdout')
        command='check_power_grid -net '+name+' -error_file '+str(error)
        result=caught(design,command)
        caught(design,'puts {PINWHEEL_PG_END '+name+'}; flush stdout')
        require(result=='1' and error.read_bytes()==b'','PG connectivity returned false/nonempty error report')
        checks.append(dict(net=name,argv=command.split(),catch_status=0,result=result,error_file=error.name,
            error_sha256=sha(error),error_bytes=0,floorplanning=False,dont_require_terminals=False))
    require(census(block,inventory)==measured and all(sha(path)==pin for path,pin in frozen.items()),
        'PG query changed inputs or terminal/physical census')
    P.write(root/'native.json',dict(schema='pinwheel.streaming-8x4-power-grid-native.v1',completed=True,
        input_sha256=frozen,source_odb_unchanged=True,canonical_inventory_rederived=True,
        inventory_totals=inventory_totals(inventory),
        **revision,openroad_source_commit=COMMIT,rails=measured,checks=checks,
        geometric_open_path_connectivity=True,shorts_checked=False,ir_drop_qualified=False,
        physical_acceptance=False,qualified=False,boundary=BOUNDARY))


def parse_log(text,rails):
    require(not re.search(r'\[(?:WARNING|ERROR|CRITICAL)\b',text),'PG Native log contains warning/error')
    require(text.count('PINWHEEL_PG_BEGIN ')==len(rails) and text.count('PINWHEEL_PG_END ')==len(rails),
        'Missing/extra PG command log boundary')
    result={}
    for name in rails:
        chunks=re.findall(r'^PINWHEEL_PG_BEGIN '+re.escape(name)+r'\r?\n(.*?)^PINWHEEL_PG_END '+
            re.escape(name)+r'\r?$',text,re.M|re.S)
        require(len(chunks)==1,'Missing/duplicate PG rail log section');chunk=chunks[0]
        require(chunk.count('[INFO PSM-0040] All shapes on net '+name+' are connected.')==1,
            'Missing exact PSM connectivity success message')
        stats={}
        for label in ('shapes','nodes','connections'):
            values=re.findall(r'^Total '+label+r': ([0-9]+)\r?$',chunk,re.M)
            require(len(values)==1 and int(values[0])>0,'Vacuous/duplicate/missing PSM graph statistics')
            stats[label]=int(values[0])
        result[name]=stats
    require(text.count('[INFO PSM-0040]')==len(rails),'Extra PSM connectivity result outside required calls')
    return result


def native_result(output,packet):
    output=Path(output);request=P.read(output/'inputs/request.json');value=P.read(output/'native.json')
    require(value.get('schema')=='pinwheel.streaming-8x4-power-grid-native.v1' and value.get('completed') is True and
        value.get('source_odb_unchanged') is True and value.get('canonical_inventory_rederived') is True and
        value.get('geometric_open_path_connectivity') is True and value.get('shorts_checked') is False and
        value.get('ir_drop_qualified') is False and value.get('physical_acceptance') is False and value.get('qualified') is False and
        value.get('openroad_source_commit')==COMMIT and value.get('input_sha256')=={
            '/work/target.odb':packet['source_odb']['sha256'],
            '/work/pg/inputs/inventory.json':sha(output/'inputs/inventory.json'),
            '/work/pg/inputs/reference.json':sha(output/'inputs/reference.json')},'PG native claim/target differs')
    revision_identity(value['openroad_version'],value['openroad_git_describe'])
    validate_census(value['rails'],P.read(output/'inputs/inventory.json'))
    require(value.get('inventory_totals')==inventory_totals(P.read(output/'inputs/inventory.json')),
        'Native total instance/master/PG inventory differs')
    require(len(value['checks'])==len(request['rails']),'PG command count differs')
    for index,(name,row) in enumerate(zip(request['rails'],value['checks'])):
        filename='rail-'+str(index)+'-errors.rpt'
        require(row==dict(net=name,argv=['check_power_grid','-net',name,'-error_file','/work/pg/'+filename],
            catch_status=0,result='1',error_file=filename,error_sha256=sha(output/filename),error_bytes=0,
            floorplanning=False,dont_require_terminals=False) and regular(output/filename).read_bytes()==b'',
            'PG command/error-file/required-terminal contract differs')
    require(sorted(path.name for path in output.glob('rail-*-errors.rpt'))==
        sorted(row['error_file'] for row in value['checks']),'Extra/missing PG error report')
    leaf=P.read(output/'leaf.json')
    require(leaf.get('schema')=='pinwheel.streaming-8x4-power-grid-leaf.v1' and leaf.get('completed') is True and
        leaf.get('exit_code')==0 and leaf.get('timeout_seconds')==LEAF_SECONDS and
        leaf.get('argv')==[leaf.get('openroad_executable'),'-no_init','-exit','-python','/work/pg/launch.py'] and
        Path(leaf['openroad_executable']).is_absolute() and leaf.get('log_sha256')==sha(output/'openroad.log') and
        (output/'launch.py').read_text()==LAUNCHER,'PG leaf command/budget/log changed')
    return value,parse_log(regular(output/'openroad.log').read_text(),request['rails'])


def native_supervise(root=Path('/work/pg')):
    root=Path(root);require((root/'launch.py').read_text()==LAUNCHER,'PG launch source differs')
    executable=str(Path(shutil.which('openroad')).resolve(strict=True))
    command=[executable,'-no_init','-exit','-python',str(root/'launch.py')]
    row=dict(schema='pinwheel.streaming-8x4-power-grid-leaf.v1',argv=command,openroad_executable=executable,
        completed=False,timeout_seconds=LEAF_SECONDS)
    try:
        result=process_group.run_captured(command,cwd=root,timeout=LEAF_SECONDS,log_path=root/'openroad.log')
        row.update(exit_code=result.returncode,completed=result.returncode==0)
    except BaseException as error:
        row.update(error=type(error).__name__+': '+str(error),exit_code=124 if isinstance(error,subprocess.TimeoutExpired) else 2,
            process_group_stopped=getattr(error,'process_group_stopped',False))
    if (root/'openroad.log').is_file():row['log_sha256']=sha(root/'openroad.log')
    P.write(root/'leaf.json',row);return 0 if row['completed'] else 2


def validate_runtime(runtime,selected_runtime):
    lock=P.read(P.ROOT/'tools/physical-toolchain.json')
    # OCI's config descriptor is not Docker's loaded image ID. The exact ID is
    # observed and hash-bound by the selected physical run and final views.
    require(re.fullmatch(r'sha256:[0-9a-f]{64}',selected_runtime.get('image_id','')) and
        runtime==selected_runtime==dict(image_id=selected_runtime['image_id'],architecture='arm64',os='linux',
        rootfs_diff_ids=lock['container_rootfs_diff_ids'],runtime_config_sha256=lock['container_runtime_config_sha256']),
        'PG runtime differs from the selected physical image or pinned rootfs/config')


def container_command(output,packet,runtime,owner,name):
    require(re.fullmatch(r'pinwheel-[A-Za-z0-9_-]+',name) and str(uuid.UUID(owner))==owner,'Unsafe PG container name/owner')
    validate_runtime(runtime,packet['runtime'])
    return ['docker','run','--rm','--pull','never','--name',name,'--label','org.pinwheel.streaming8_owner='+owner,
        '--network','none','--cpus','1','--memory','2g','--memory-swap','2g','--read-only','--tmpfs','/tmp:rw,size=128m',
        '--env','PYTHONDONTWRITEBYTECODE=1','--env','PYTHONPATH=/work/pg/inputs/producer/scripts',
        '--mount',f'type=bind,source={output},target=/work/pg',
        '--mount',f'type=bind,source={output/"inputs"},target=/work/pg/inputs,readonly',
        '--mount',f'type=bind,source={packet["source_odb"]["path"]},target=/work/target.odb,readonly',
        '--workdir','/work/pg',runtime['image_id'],'python3','-B',
        '/work/pg/inputs/producer/scripts/streaming_8x4_power_grid.py','native-supervise']


def run(output,name):
    output=Path(output).absolute();packet=verify_preparation(output)
    require({path.name for path in output.iterdir()}=={'inputs','preparation.json'},'PG output is not fresh')
    require(re.fullmatch(r'pinwheel-[A-Za-z0-9_-]+',name),'Unsafe PG container name')
    runtime=V.inspect_runtime(P.read(P.ROOT/'tools/physical-toolchain.json'));owner=str(uuid.uuid4())
    (output/'launch.py').write_text(LAUNCHER)
    command=container_command(output,packet,runtime,owner,name)
    execution=V.owned_native(command,output,owner,OUTER_SECONDS)
    report=dict(schema='pinwheel.streaming-8x4-power-grid-run.v1',preparation=bound(output/'preparation.json'),
        target=packet['target'],physical_candidate=packet['physical_candidate'],runtime=runtime,execution=execution,
        leaf_timeout_seconds=LEAF_SECONDS,outer_timeout_seconds=OUTER_SECONDS,passed=False,
        outer_resource_cleanup_required=True,
        resource_cleanup_join='Separate exact campaign resource-supervisor receipt remains mandatory.',
        geometric_open_path_connectivity=False,shorts_checked=False,ir_drop_qualified=False,
        qualified=False,physical_acceptance=False,boundary=BOUNDARY)
    try:
        require(execution.get('status')=='completed' and execution.get('exit_code')==0 and
            execution.get('timeout_seconds')==OUTER_SECONDS and
            execution.get('container_termination',{}).get('status')=='absent','PG Native execution/cleanup did not close')
        native_value,stats=native_result(output,packet)
        require(verify_preparation(output)==packet and V.inspect_runtime(P.read(P.ROOT/'tools/physical-toolchain.json'))==runtime,
            'PG source/input/runtime changed across execution')
        report.update(passed=True,geometric_open_path_connectivity=True,native=bound(output/'native.json'),
            census_totals={name:{key:row[key] for key in ('iterm_count','bterm_count','bpin_count','swire_count',
                'swire_routing_shapes','swire_vias','skipped_iterms','skipped_bpins')} for name,row in native_value['rails'].items()},
            psm_graph_statistics=stats,inputs_runtime_unchanged=True)
    except BaseException as error:report['error']=type(error).__name__+': '+str(error)
    report['artifact_sha256']=artifacts(output);P.write(output/'report.json',report);return report


def verify(path):
    path=regular(path).resolve();report=P.read(path);output=path.parent
    require(report.get('schema')=='pinwheel.streaming-8x4-power-grid-run.v1' and report.get('passed') is True and
        report.get('geometric_open_path_connectivity') is True and report.get('shorts_checked') is False and
        report.get('ir_drop_qualified') is False and report.get('physical_acceptance') is False and
        report.get('qualified') is False and report.get('inputs_runtime_unchanged') is True and
        report.get('outer_resource_cleanup_required') is True and
        report.get('leaf_timeout_seconds')==LEAF_SECONDS and report.get('outer_timeout_seconds')==OUTER_SECONDS and
        artifacts(output)==report.get('artifact_sha256'),'PG run/claim/artifact membership is not closed')
    packet=verify_preparation(output);execution=P.read(output/'execution.json')
    command=execution.get('argv');require(type(command) is list and len(command)>6 and
        command==container_command(output,packet,report['runtime'],execution['owner'],command[6]),
        'PG container command/resource/mount contract differs')
    require(report['preparation']==bound(output/'preparation.json') and report['target']==packet['target'] and
        report['physical_candidate']==packet['physical_candidate'] and report['execution']==execution and
        execution.get('status')=='completed' and execution.get('exit_code')==0 and execution.get('timeout_seconds')==OUTER_SECONDS and
        execution.get('container_termination',{}).get('status')=='absent' and report['native']==bound(output/'native.json'),
        'PG execution/target binding differs')
    value,stats=native_result(output,packet)
    require(report['psm_graph_statistics']==stats and report['census_totals']=={name:{key:row[key] for key in
        ('iterm_count','bterm_count','bpin_count','swire_count','swire_routing_shapes','swire_vias','skipped_iterms','skipped_bpins')}
        for name,row in value['rails'].items()},'PG rederived observation differs')
    return report


def main():
    parser=argparse.ArgumentParser(description=__doc__);sub=parser.add_subparsers(dest='mode',required=True)
    p=sub.add_parser('prepare')
    for name in ('views-report','source-root','output'):p.add_argument('--'+name,type=Path,required=True)
    p=sub.add_parser('run');p.add_argument('--output',type=Path,required=True);p.add_argument('--container-name',required=True)
    p=sub.add_parser('verify');p.add_argument('--report',type=Path,required=True)
    sub.add_parser('native-supervise')
    args=parser.parse_args()
    if args.mode=='prepare':prepare(args.views_report,args.source_root,args.output)
    elif args.mode=='run':return 0 if run(args.output,args.container_name)['passed'] else 2
    elif args.mode=='native-supervise':return native_supervise()
    else:verify(args.report)
    return 0


if __name__=='__main__':raise SystemExit(main())
