"""Restore only native real-pin wire ground capacitances omitted by pinned writer."""
import json,hashlib,re,decimal,math,time,struct
from pathlib import Path
D=decimal.Decimal
def f32(v):return struct.unpack('f',struct.pack('f',float(v)))[0]
ROOT=Path(__file__).resolve().parents[3]; OUT=ROOT/'build/physical/tt-buffered-pinrc-export-01'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_text())
def write(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
def quantum(s):
    return D(10)**D(s).as_tuple().exponent
def parse_debug(log):
    assert log.count('PINWHEEL_FULL_PRECISION_PINRC_BEGIN')==log.count('PINWHEEL_FULL_PRECISION_PINRC_END')==1
    trace=log.split('PINWHEEL_FULL_PRECISION_PINRC_BEGIN')[1].split('PINWHEEL_FULL_PRECISION_PINRC_END')[0]
    scale=re.findall(r'PINWHEEL_CAP_UNIT_SCALE\s+(\S+)',trace);assert len(scale)==1
    assert abs(float(scale[0])/1e-15-1)<1e-6
    nets={};net=None
    for line in trace.splitlines():
        m=re.search(r'\bnet (\S+)\s*$',line)
        if m:net=m[1];assert net not in nets; nets[net]=[];continue
        m=re.search(r'(\S+) -> (\S+) \((-?\d+\.\d+), (-?\d+\.\d+)\) (\d+\.\d+)u layer=(\d+) r=(\S+) via_res=(\S+) c=(\S+)\s*$',line)
        if m:
            assert net is not None
            cap=m[9];assert re.fullmatch(r'\d+\.\d{12}',cap),('Notfullprecision',cap)
            nets[net].append(dict(grid_node=m[1],native_pin=m[2],pin_xy_um=[m[3],m[4]],stub_length_um=m[5],layer=int(m[6]),wire_res_user=m[7],via_res_user=m[8],full_stub_cap_fF=cap,pin_cap_pf=str(D(cap)/D(2000))))
    assert nets and sum(map(len,nets.values()))>1000
    # Recover the native cap float through the actual coefficient and one unique
    # integer DBU wire length; never infer a pin cap from D_NET residual.
    coeff={}
    for row in (OUT/'layer-rc.tsv').read_text().splitlines():
        name,layer,values=row.split('\t');r,c=map(float,values.split());assert c>0;coeff[int(layer)]=[r,c]
    dbu=read(ROOT/'build/physical/tt-buffered-hold30712-route-02/candidate/native-inventory.json')['dbu_per_micron']
    capscale=f32(scale[0])
    for name,events in nets.items():
        for e in events:
            native_display=float(e['full_stub_cap_fF']);cper=coeff[e['layer']][1]
            estimate=native_display*capscale/cper*dbu*1e6
            candidates=[]
            for length in range(max(0,round(estimate)-2),round(estimate)+3):
                length_m=f32(length/(dbu*1e6));native_cap=f32(cper*length_m)
                displayed=f32(native_cap/capscale)
                if abs(displayed)<1e-6:displayed=0.0
                if format(displayed,'.12f')==e['full_stub_cap_fF']:
                    candidates.append((length,native_cap))
            assert len(candidates)==1,(name,e['native_pin'],'NativefloatDBUnotunique',estimate,candidates)
            length,native_cap=candidates[0]
            assert abs(length/dbu-float(e['stub_length_um']))<=.005001,(name,'Debugroundedlengthdiffers')
            e.update(unique_stub_length_dbu=length,native_stub_cap_farads_float32=native_cap,pin_cap_pf=str(D.from_float(native_cap)*D('1e12')/2),native_float32_replayed_debug_exact=True)
    return nets,scale[0]
def repair(raw,debug,native_nets):
    assert '*C_UNIT 1 PF\n' in raw and '*DELIMITER :\n' in raw and '"PIN_CAP NONE"' in raw
    blocks=list(re.finditer(r'(?ms)^\*D_NET (\S+) (\S+)\n(.*?)^\*END\n',raw));assert blocks
    outputs=[];cursor=0;proof={};seen=set();events=0
    for m in blocks:
        name,total,body=m.groups();assert name not in seen;seen.add(name)
        assert name in debug and name in native_nets,('Missingnativenet',name)
        expected=set()
        for inst,pin,_ in native_nets[name]['terminals']:expected.add(inst+':'+pin)
        expected.update(native_nets[name]['ports'])
        conn=body.split('*CONN\n')[1].split('*CAP\n')[0]
        terminals=re.findall(r'^\*[IP] (\S+) [IOB](?:\s|$)',conn,re.M);assert len(set(terminals))==len(terminals)
        assert set(terminals)<=expected,(name,'CONNnotnative')
        mapping={}
        for term in terminals:
            native=term.rsplit(':',1)[0]+'/'+term.rsplit(':',1)[1] if ':' in term else term
            assert native not in mapping;mapping[native]=term
        capbody=body.split('*CAP\n')[1].split('*RES\n')[0]
        records=[]
        for line in capbody.splitlines():
            fields=line.split();assert len(fields)==3,'ExpectedgroundonlyCAP'
            assert fields[1] not in terminals,'Pinnedoriginalrealpincapunexpected'
            records.append(fields)
        ids=[int(f[0]) for f in records];assert len(set(ids))==len(ids)
        attachments=debug[name];assert len(attachments)==len(mapping),(name,'Attachmentcount',len(attachments),len(mapping))
        assigned=set();new=[];last=max(ids,default=0)
        for e in attachments:
            pin=e['native_pin'];assert pin in mapping and pin not in assigned,(name,'Pinmappingambiguous',pin,mapping)
            assigned.add(pin);term=mapping[pin]
            assert e['grid_node'] not in terminals
            # EST emits network node names with colon or slash according to native name formatting.
            res=body.split('*RES\n')[1]
            assert any(term in f.split()[1:3] for f in res.splitlines()),(name,'NoexistingRattachment',term)
            last+=1;new.append(f'{last} {term} {e["pin_cap_pf"]}\n');e['spef_terminal']=term;events+=1
        assert assigned==set(mapping)
        oldsum=sum((D(f[2]) for f in records),D(0));added=sum((D(e['pin_cap_pf']) for e in attachments),D(0));summed=oldsum+added;error=abs(summed-D(total))
        # All original values are six-significant-digit serialized native floating values.
        # DNET/node CAP decimal rounding intervals plus one float32 relative ULP cover source serialization;
        # no residual is allocated or used to change any pin value.
        tolerance=quantum(total)/2+sum((quantum(f[2])/2 for f in records if D(f[2])!=0),D(0))+D('0.00000012')*(oldsum+added)+D('0.000000000001')
        assert error<=tolerance,(name,'DNETdoesnotclose',str(error),str(tolerance),str(added))
        newbody=body.replace('*RES\n',''.join(new)+'*RES\n',1)
        assert newbody.replace(''.join(new),'',1)==body
        result=m[0].replace(body,newbody,1)
        outputs.append(raw[cursor:m.start()]+result);cursor=m.end()
        proof[name]=dict(D_NET_total_pf=total,original_CAP_sum_pf=str(oldsum),added_native_pin_CAP_pf=str(added),reconstructed_total_pf=str(summed),closure_abs_error_pf=str(error),source_serialization_tolerance_pf=str(tolerance),attachments=attachments,original_CAP_records_count=len(records),added_CAP_records_count=len(new))
    outputs.append(raw[cursor:]);out=''.join(outputs)
    assert len(proof)==len(blocks) and seen==set(debug),('SPEF/debugnetcoverage',seen^set(debug))
    return out,proof,events
def main():
    started=time.monotonic();native=read(OUT/'report.json');assert native['status']=='passed' and native['exit_code']==0 and native['inputs_unchanged'] and native['container_termination']['status']=='absent'
    assert all(sha(Path(p))==h for p,h in native['input_sha256'].items())
    assert all(sha(OUT/p)==h for p,h in native['artifact_sha256'].items())
    original=ROOT/'build/physical/tt-buffered-hold30712-route-02/candidate/estimated.spef';assert sha(original)==sha(OUT/'estimated.spef')=='4d8fc8bb02d05652d49ffbe6a329fdcf7a4a1d17d342a041ad4069f1f424721e'
    inventory=ROOT/'build/physical/tt-buffered-hold30712-route-02/candidate/native-inventory.json';I=read(inventory)
    debug,scale=parse_debug((OUT/'native.log').read_text());text,proof,count=repair(original.read_text(),debug,I['nets'])
    corrected=OUT/'corrected-02.spef';assert not corrected.exists();corrected.write_text(text)
    write(OUT/'per-pin-cap-proof-02.json',dict(schema='pinwheel-buffered-tt-pinrc-correction-proof-v1',net_count=len(proof),pin_attachment_count=count,cap_debug_unit_scale=scale,nets=proof))
    corners={}
    pre=ROOT/'build/physical/tt-buffered-holdreset-pair-preflight-01/preflight';corner_names=['nom_typ_1p20V_25C','nom_slow_1p08V_125C','nom_fast_1p32V_m40C']
    originals={}
    for corner in corner_names:
        src=pre/corner/'estimated.spef';assert sha(src)==sha(original);originals[str(src)]=sha(src)
        corners[corner]={'path':str(corrected.resolve()),'sha256':sha(corrected)}
    inputs={**native['input_sha256'],str(OUT/'report.json'):sha(OUT/'report.json'),str(original):sha(original),str(inventory):sha(inventory),str(Path(__file__).resolve()):sha(Path(__file__).resolve()),str(OUT/'layer-rc.tsv'):sha(OUT/'layer-rc.tsv'),str(OUT/'native.log'):sha(OUT/'native.log'),**originals}
    artifacts={str(corrected.resolve()):sha(corrected),str((OUT/'per-pin-cap-proof-02.json').resolve()):sha(OUT/'per-pin-cap-proof-02.json')}
    receipt=dict(schema='pinwheel-buffered-tt-pinrc-corrected-export-v1',status='passed',source_database_sha256=native['source_database_sha256'],source_segments_sha256=native['source_segments_sha256'],corrected_spef_by_corner=corners,invariants=dict(native_pin_node_wire_caps_exact=True,all_D_NET_totals_conserved=True,all_non_CAP_sections_unchanged=True,original_CAP_records_unchanged=True,original_SPEFs_unchanged=True,R_sections_unchanged=True,CONN_sections_unchanged=True),input_sha256=inputs,artifact_sha256=artifacts,native_export_report={'path':str((OUT/'report.json').resolve()),'sha256':sha(OUT/'report.json')},net_count=len(proof),pin_attachment_count=count,precision='Native EST detail full stub C in fF with12decimals; half assigned to exact existing CONN terminal. Per-pin unique integerDBU length+nativefloat32 coefficient replay recovers source cap/2 exactly; no net residual distributed.',clock_wire_CAP_restored=True,host_elapsed_seconds=round(time.monotonic()-started,3),qualification='Derivative global-route estimated RC network only. Faithful timing transfer requires independent fresh <=1ps controls before any virtual sizing inference.')
    assert all(sha(Path(p))==h for p,h in inputs.items());write(OUT/'corrected-export-report-02.json',receipt);print(sha(OUT/'corrected-export-report-02.json'),len(proof),count,receipt['host_elapsed_seconds'])
if __name__=='__main__':main()
