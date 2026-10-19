"""Actual ODB inventory checks for STA annotation and logical rail bindings.

Logical pin/rail identity does not establish geometric power connectivity,
IR drop, analog correctness or layout-versus-schematic acceptance.
"""
from physical_checkpoint_sta import measurement_quality
from streaming_tt_signoff import require


def inventory_context(inventory):
    require(inventory.get('schema')=='pinwheel.streaming-tt-odb-inventory.v1','Wrong actual ODB inventory')
    nets=inventory['nets'];masters=inventory['masters'];instances=inventory['instances']
    require(nets and masters and instances,'Empty actual ODB inventory')
    require(len({row['wire'] for row in nets.values()})==len(nets),'Aliased actual ODB net IDs')
    context=dict(nets={name:dict(type=row['signal_type'],ports=[],terminals=[]) for name,row in nets.items()})
    disconnected=set()
    for name,instance in instances.items():
        require(instance['master'] in masters,'Unknown actual ODB master')
        terms=instance['terminals'];signature=masters[instance['master']]
        require({pin:{key:row[key] for key in ('direction','signal_type')} for pin,row in terms.items()}==signature,
            'Actual ODB terminal inventory differs from master')
        for pin,row in terms.items():
            kind,direction,net=row['signal_type'],row['direction'],row['net']
            require(kind in ('SIGNAL','CLOCK','POWER','GROUND') and direction in ('INPUT','OUTPUT','INOUT'),
                'Unclassified actual ODB terminal')
            if net is None:
                require(kind in ('POWER','GROUND') or direction=='OUTPUT','Disconnected functional ODB input')
                if kind not in ('POWER','GROUND'):disconnected.add(name+'/'+pin)
                continue
            require(net in nets,'Actual ODB terminal names missing net')
            require((kind in ('POWER','GROUND') and nets[net]['signal_type']==kind) or
                (kind in ('SIGNAL','CLOCK') and nets[net]['signal_type'] in ('SIGNAL','CLOCK')),
                'Actual ODB terminal shorts a power/signal boundary')
            context['nets'][net]['terminals'].append(dict(instance=name,pin=pin,direction=direction))
    require(disconnected==set(inventory['unconnected_signal_outputs']),'Unconnected actual output inventory differs')
    seen=set();port_directions={}
    for collection in ('public_bterms','power_bterms'):
        for name,row in inventory[collection].items():
            require(name not in seen and row['net'] in nets,'Aliased/unresolved actual ODB block terminal')
            seen.add(name);context['nets'][row['net']]['ports'].append(name)
            if collection=='public_bterms':
                require(row.get('direction') in ('input','output'),'Missing actual public direction')
                port_directions[name]=row['direction']
    for name,row in context['nets'].items():
        if row['type'] in ('POWER','GROUND'):continue
        consumed=any(term['direction']=='INPUT' for term in row['terminals']) or any(
            port_directions[port]=='output' for port in row['ports'])
        drivers=sum(term['direction']=='OUTPUT' for term in row['terminals'])+sum(
            port_directions[port]=='input' for port in row['ports'])
        require(not consumed or drivers==1,'Consumed actual ODB net lacks exactly one driver: '+name)
    return context,disconnected


def logical_power(inventory,*,power='VPWR',ground='VGND'):
    inventory_context(inventory)
    require(power!=ground and inventory['nets'].get(power,{}).get('signal_type')=='POWER' and
        inventory['nets'].get(ground,{}).get('signal_type')=='GROUND','Missing/distinct power rail identity')
    expected={'POWER':power,'GROUND':ground};failures=[];terminals=0
    actual_rails={name for name,row in inventory['nets'].items() if row['signal_type'] in expected}
    if actual_rails!={power,ground}:failures.append(dict(kind='unexpected_rail_inventory',actual=sorted(actual_rails)))
    for name,instance in inventory['instances'].items():
        counts={'POWER':0,'GROUND':0}
        for pin,row in instance['terminals'].items():
            kind=row['signal_type']
            if kind not in expected:continue
            terminals+=1;counts[kind]+=1
            if row['net']!=expected[kind] or row['direction']!='INOUT':
                failures.append(dict(kind='misbound_power_terminal',instance=name,pin=pin,actual=row['net'],expected=expected[kind]))
        if not all(counts.values()):failures.append(dict(kind='missing_instance_rail',instance=name,counts=counts))
    bterms=inventory['power_bterms']
    if set(bterms)!={power,ground}:failures.append(dict(kind='missing_or_extra_power_bterm',actual=sorted(bterms)))
    for kind,name in expected.items():
        row=bterms.get(name)
        if row is not None and (row['net']!=name or row['signal_type']!=kind or row['direction']!='INOUT'):
            failures.append(dict(kind='misbound_power_bterm',terminal=name,actual=row))
    require(terminals>0,'Vacuous logical rail check')
    return dict(passed=not failures,checked_power_terminals=terminals,checked_instances=len(inventory['instances']),
        failures=failures,geometric_connectivity_qualified=False,ir_drop_qualified=False,
        boundary='Actual logical power-pin/rail inventory only; native routed power-grid and GDS/LVS checks remain required.')


def timing_quality(inventory,checks):
    context,disconnected=inventory_context(inventory)
    result=measurement_quality(checks,context,disconnected)
    result['annotation_complete_for_consumed_nets']=result['wire_annotation']['complete_for_consumed_nets']
    result['raw_fanout_violations']=len(result['fanout_violations'])
    return result


def check_receipts(sta_path,export_path,out):
    """Reconcile sealed fresh measurements with the same actual ODB inventory."""
    from collections import Counter
    from pathlib import Path
    import subprocess
    from streaming_tt_rc import CORNERS
    from streaming_tt_signoff import read,regular,sha,unchanged,write
    sta_path,export_path=map(regular,(sta_path,export_path));out=Path(out)
    require(not out.exists(),'Preserve earlier timing-quality receipts')
    sta=read(sta_path);export=read(export_path)
    require(sta.get('schema')=='pinwheel.streaming-tt-fresh-sta-host.v1' and
        sta.get('status')=='completed' and sta.get('exit_code')==0 and
        sta.get('inputs_unchanged') is True and sta.get('owned_container_absent') is True and
        sta.get('closed_constraint_sha256'),'Fresh STA host inputs/constraints/cleanup are not closed')
    require(export.get('schema')=='pinwheel.streaming-tt-odb-export.v1' and
        export.get('read_only_database') is True,'Missing actual ODB export receipt')
    native_path=regular(sta_path.parent/'native/report.json');native=read(native_path)
    require(sta.get('native_report_sha256')==sha(native_path) and
        native.get('schema')=='pinwheel.streaming-tt-fresh-sta.v1' and
        native.get('measurements_completed') is True and native.get('inputs_unchanged') is True and
        set(native.get('corners',{}))==set(CORNERS) and native.get('mode')==sta.get('mode'),
        'Changed/incomplete actual fresh STA measurements')
    frozen={str(path):sha(path) for path in (sta_path,export_path,native_path,regular(__file__))}
    for name,digest in sta['closed_constraint_sha256'].items():
        path=regular(name);require(sha(path)==digest,'Closed fresh timing constraint changed');frozen[str(path)]=digest
    databases={name:digest for name,digest in sta['input_sha256'].items() if name.endswith('.odb')}
    require(len(databases)==1 and next(iter(databases.values()))==export['database_sha256'],
        'STA and exported inventory refer to different actual ODBs')
    for name,digest in databases.items():
        path=regular(name);require(sha(path)==digest,'Actual timing ODB changed');frozen[str(path)]=digest
    inventory_path=regular(export_path.parent/'inventory.json')
    require(export.get('artifacts_sha256',{}).get('inventory.json')==sha(inventory_path),
        'Actual ODB inventory changed')
    inventory=read(inventory_path);frozen[str(inventory_path)]=sha(inventory_path)
    power=logical_power(inventory);qualities={}
    for corner in CORNERS:
        files=native['corners'][corner]['artifacts_sha256'];directory=native_path.parent/corner
        checks=regular(directory/'checks.rpt')
        require(files.get('checks.rpt')==sha(checks),'Fresh raw timing checks changed')
        log_name='openroad-stamidpnr.log' if sta['mode']=='nominal' else 'openroad-stapostpnr.log'
        log=regular(directory/log_name)
        require(files.get(log_name)==sha(log),'Fresh native timing log changed')
        marker='PINWHEEL_PROPAGATED_CLOCK 1' if sta['mode']=='nominal' else 'PINWHEEL_EXTRACTED_PROPAGATED_CLOCK 1'
        require(marker in log.read_text(),'Actual propagated clock not confirmed')
        frozen.update({str(path):sha(path) for path in (checks,log)})
        quality=timing_quality(inventory,checks.read_text())
        count=native['corners'][corner]['metrics']['design__max_fanout_violation__count__corner:'+corner]
        require(type(count) is int and count==quality['raw_fanout_violations'],
            'Native fanout count differs from actual reconciled driver rows')
        quality['fanout_by_net_type']=dict(Counter(row['kind'] for row in quality['fanout_violations']))
        qualities[corner]=quality
    unchanged(frozen)
    result=dict(schema='pinwheel.streaming-tt-timing-quality.v1',qualified=False,physical_acceptance_claim=False,
        actual_odb_sha256=export['database_sha256'],mode=sta['mode'],corner_quality=qualities,
        logical_power=power,assessment=native['assessment'],input_sha256_before=frozen,inputs_unchanged=True,
        producer_commit=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),
        annotation_complete_for_consumed_nets=all(row['annotation_complete_for_consumed_nets'] for row in qualities.values()),
        final_extracted_timing_qualified=False,functional_correspondence_qualified=False,
        boundary='Actual consumed-net annotation, raw fanout and logical rail reconciliation. Extractor model validity, routed geometry, source behavior and complete physical acceptance remain separate.')
    out.parent.mkdir(parents=True,exist_ok=True)
    write(out,result);return result


def main():
    import argparse
    from pathlib import Path
    parser=argparse.ArgumentParser(description=__doc__)
    for name in ('sta-report','odb-export','out'):parser.add_argument('--'+name,required=True,type=Path)
    args=parser.parse_args();check_receipts(args.sta_report,args.odb_export,args.out);print(args.out)


if __name__=='__main__':main()
