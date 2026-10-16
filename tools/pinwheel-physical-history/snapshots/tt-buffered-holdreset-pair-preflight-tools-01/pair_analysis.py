"""Complete endpoint coverage plus deliberately conservative library-only bounds."""
import hashlib, re
from pathlib import Path

def group(text, start):
    position=text.index('{',start);depth=1;end=position+1
    while depth:
        depth += (text[end]=='{')-(text[end]=='}');end+=1
    return text[start:end]

def table(cell,output,input_pin,kind):
    pin_match=re.search(r'pin\s*\(\s*'+re.escape(output)+r'\s*\)',cell);assert pin_match
    pin=group(cell,pin_match.start())
    for timing_match in re.finditer(r'timing\s*\(\s*\)',pin):
        timing=group(pin,timing_match.start())
        related=re.search(r'related_pin\s*:\s*"([^"]+)"',timing)
        if related and input_pin in related[1].split():
            match=re.search(r'\b'+kind+r'\s*\(',timing)
            if match:
                body=group(timing,match.start())
                axes=[list(map(float,re.search(r'index_'+str(number)+r'\s*\(\s*"([^"]+)"',body)[1].split(','))) for number in [1,2]]
                values=body[body.index('values'):];rows=[list(map(float,row.split(','))) for row in re.findall(r'"([^"]+)"',values)]
                assert len(rows)==len(axes[0]) and all(len(row)==len(axes[1]) for row in rows)
                return axes,rows
    raise AssertionError(('Missing combinational NLDM arc',output,input_pin,kind))

def interpolate(lookup,slew,cap):
    axes,values=lookup
    def interval(axis,value):
        assert axis[0]<=value<=axis[-1],('Outside NLDM table',value,axis[0],axis[-1])
        index=next((i for i in range(len(axis)-1) if axis[i]<=value<=axis[i+1]),len(axis)-2)
        return index,(value-axis[index])/(axis[index+1]-axis[index])
    x,fx=interval(axes[0],slew);y,fy=interval(axes[1],cap)
    return ((1-fx)*(1-fy)*values[x][y]+fx*(1-fy)*values[x+1][y]+(1-fx)*fy*values[x][y+1]+fx*fy*values[x+1][y+1])

def arcs(block):
    data=block.split('data arrival time')[0];rows=[]
    pattern=r'^\s*(?:(\d+)\s+(\d+\.\d+)\s+)?(\d+\.\d+)\s+(\d+\.\d+)\s+(\d+\.\d+)\s+([\^v])\s+(\S+)\s+\(([^)]+)\)'
    for line in data.splitlines():
        match=re.match(pattern,line)
        if match:rows.append(dict(pin=match[7],master=match[8],delay_ns=float(match[4]),slew_ns=float(match[3]),edge=match[6],cap_pf=float(match[2]) if match[2] else None))
    return rows

def analyze_pair(folder,libpath):
    folder=Path(folder);library=Path(libpath).read_text();cells={}
    def get_cell(master):
        if master not in cells:
            found=re.search(r'cell\s*\(\s*'+re.escape(master)+r'\s*\)',library);assert found,('Nonstandard data master',master)
            cells[master]=group(library,found.start())
        return cells[master]
    coverage=(folder/'resetpair-coverage.tsv').read_text().splitlines();reach=set();ledger={'max':{},'min':{}}
    for line in coverage:
        fields=line.split('\t')
        if fields[0]=='REACH':assert len(fields)==2 and fields[1] not in reach;reach.add(fields[1])
        elif fields[0]=='PATH':
            assert len(fields)==5 and fields[1] in ledger and fields[2] not in ledger[fields[1]]
            ledger[fields[1]][fields[2]]=dict(startpoint=fields[3],slack_ns=float(fields[4]))
        else:assert fields[0]=='API' and len(fields)==2
    assert reach and set(ledger['max'])==set(ledger['min'])==reach,('Incomplete reset-pair constrained endpoint coverage',sorted(reach-set(ledger['max'])),sorted(reach-set(ledger['min'])))
    analyzed={};slow_gain=[];speedup_bounds=[]
    for kind in ['max','min']:
        report=(folder/('resetpair-'+kind+'.rpt')).read_text();blocks=re.findall(r'(?ms)^Startpoint: .*?(?=^Startpoint:|\Z)',report);actual={}
        for block in blocks:
            rows=arcs(block);assert rows;endpoint=rows[-1]['pin'];assert endpoint not in actual and endpoint in ledger[kind]
            slack=float(re.findall(r'(-?\d+\.\d+)\s+slack \((?:MET|VIOLATED)\)',block)[-1]);assert abs(slack-ledger[kind][endpoint]['slack_ns'])<=1e-5
            pair=[(i,row) for i,row in enumerate(rows) if row['pin'] in ['fanout914/X','fanout913/X']];assert pair
            bound=0.;direct_gain=0.;details=[]
            for index,row in pair:
                input_row=rows[index-1];assert input_row['pin']==row['pin'].split('/')[0]+'/A'
                model=table(get_cell('sg13cmos5l_buf_4'),'X','A','cell_rise' if row['edge']=='^' else 'cell_fall')
                predicted=interpolate(model,input_row['slew_ns'],row['cap_pf']);gain=row['delay_ns']-predicted;direct_gain+=gain
                min_axis=model[0][0][0]
                fastest=interpolate(model,min_axis,row['cap_pf']);bound+=max(0,row['delay_ns']-fastest)
                details.append(dict(instance=row['pin'].split('/')[0],old_delay_ns=row['delay_ns'],fixed_input_slew_ns=input_row['slew_ns'],old_output_cap_pf=row['cap_pf'],rough_buf4_delay_same_slew_load_ns=predicted,rough_fixed_slew_gain_ns=gain))
            # Bound all downstream cell speedups independently at the minimum
            # tabulated input slew. This deliberately overstates slew benefit.
            last_pair=max(index for index,row in pair)
            for index,row in enumerate(rows[last_pair+1:],last_pair+1):
                if row['cap_pf'] is None or '/' not in row['pin']:continue
                input_row=rows[index-1]
                if input_row['pin'].split('/')[0]!=row['pin'].split('/')[0]:continue
                output=row['pin'].split('/')[-1];input_pin=input_row['pin'].split('/')[-1]
                model=table(get_cell(row['master']),output,input_pin,'cell_rise' if row['edge']=='^' else 'cell_fall')
                fastest=interpolate(model,model[0][0][0],row['cap_pf']);bound+=max(0,row['delay_ns']-fastest)
            # Additional100ps allowance covers unmodelled wire/pin geometry and
            # effective-capacitance discrepancies; this is an engineering gate.
            conservative=bound+.1
            if kind=='min':speedup_bounds.append(conservative)
            if kind=='max':slow_gain.append(direct_gain-.1)
            actual[endpoint]=dict(slack_ns=slack,startpoint=ledger[kind][endpoint]['startpoint'],pair_arcs=details,rough_direct_pair_gain_ns=direct_gain,downstream_min_slew_speedup_plus100ps_allowance_ns=conservative)
        assert set(actual)==reach,('Full report endpoint coverage differs from native ledger',kind)
        analyzed[kind]=actual
    return dict(coverage_complete=True,reachable_endpoint_count=len(reach),endpoints=sorted(reach),max_paths=analyzed['max'],min_paths=analyzed['min'],minimum_through_setup_ns=min(row['slack_ns'] for row in analyzed['max'].values()),minimum_through_hold_ns=min(row['slack_ns'] for row in analyzed['min'].values()),maximum_library_downstream_speedup_bound_ns=max(speedup_bounds),minimum_rough_setup_pair_gain_after100ps_loading_allowance_ns=min(slow_gain),library_sha256=hashlib.sha256(Path(libpath).read_bytes()).hexdigest(),scope='Library-only engineering bound at fixed reported load: replacement pair plus all downstream cells independently evaluated at minimum tabulated input slew, plus100ps. Does not constitute post-ECO STA or a formal delay bound. Upstream increasedinputcap can slow path; zero upstream penalty assumed for hold-safety conservatism,100ps reserved against setup gains.')
