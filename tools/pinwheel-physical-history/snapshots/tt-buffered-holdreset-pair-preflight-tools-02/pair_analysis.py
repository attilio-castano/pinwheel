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

def analyze_pair(folder,libpaths):
    folder=Path(folder);library='\n'.join(Path(path).read_text() for path in libpaths);cells={}
    def get_cell(master):
        if master not in cells:
            found=re.search(r'cell\s*\(\s*'+re.escape(master)+r'\s*\)',library);assert found,('Missing data master',master)
            cells[master]=group(library,found.start())
        return cells[master]
    reach={driver:{trace:set() for trace in ['all','timing']} for driver in ['fanout914','fanout913']}
    ledger={(driver,edge,kind):{} for driver in reach for edge in ['rise','fall'] for kind in ['max','min']}
    for line in (folder/'resetpair-coverage.tsv').read_text().splitlines():
        fields=line.split('\t')
        if fields[0]=='REACH':assert len(fields)==4;reach[fields[1]][fields[2]].add(fields[3])
        elif fields[0]=='PATH':
            assert len(fields)==7;key=tuple(fields[1:4]);assert fields[4] not in ledger[key]
            ledger[key][fields[4]]=dict(startpoint=fields[5],slack_ns=float(fields[6]))
        else:assert fields[0] in ['API','EMPTY']
    analyzed={};loss_bounds=[];setup_gains=[];coverage=[];constraint_unknown=[]
    for key,native_paths in ledger.items():
        driver,edge,kind=key;filename='resetpair-'+driver+'-'+edge+'-'+kind+'.rpt'
        report=(folder/filename).read_text();blocks=re.findall(r'(?ms)^Startpoint: .*?(?=^Startpoint:|\Z)',report);actual={}
        for block in blocks:
            rows=arcs(block);assert rows;endpoint=rows[-1]['pin'];assert endpoint not in actual and endpoint in native_paths
            slack=float(re.findall(r'(-?\d+\.\d+)\s+slack \((?:MET|VIOLATED)\)',block)[-1]);assert abs(slack-native_paths[endpoint]['slack_ns'])<=1e-5
            pins=[row['pin'] for row in rows];assert driver+'/X' in pins
            if driver=='fanout913':assert 'fanout914/X' in pins and pins.index('fanout914/X')<pins.index('fanout913/X'), 'Serial913 path omitted914'
            selected=[(index,row) for index,row in enumerate(rows) if row['pin'] in ['fanout914/X','fanout913/X']]
            direct_gain=0.;bound=0.;details=[]
            for index,row in selected:
                source=rows[index-1];assert source['pin']==row['pin'].split('/')[0]+'/A'
                model=table(get_cell('sg13cmos5l_buf_4'),'X','A','cell_rise' if row['edge']=='^' else 'cell_fall')
                predicted=interpolate(model,source['slew_ns'],row['cap_pf']);gain=row['delay_ns']-predicted;direct_gain+=gain
                fastest=interpolate(model,model[0][0][0],row['cap_pf']);bound+=max(0,row['delay_ns']-fastest)
                details.append(dict(instance=row['pin'].split('/')[0],old_delay_ns=row['delay_ns'],fixed_input_slew_ns=source['slew_ns'],output_cap_pf=row['cap_pf'],rough_buf4_delay_same_slew_load_ns=predicted,fixed_slew_gain_ns=gain))
            for index,row in enumerate(rows[max(index for index,row in selected)+1:],max(index for index,row in selected)+1):
                if row['cap_pf'] is None or '/' not in row['pin']:continue
                source=rows[index-1]
                if source['pin'].split('/')[0]!=row['pin'].split('/')[0]:continue
                model=table(get_cell(row['master']),row['pin'].split('/')[-1],source['pin'].split('/')[-1],'cell_rise' if row['edge']=='^' else 'cell_fall')
                fastest=interpolate(model,model[0][0][0],row['cap_pf']);bound+=max(0,row['delay_ns']-fastest)
            constraint_drift=0.;constraint_known=True;constraint_proof={'kind':'fixed_output_delay'}
            if kind=='min' and '/' in endpoint:
                terminal=rows[-1];pin_name=endpoint.split('/')[-1];pin_match=re.search(r'pin\s*\(\s*'+re.escape(pin_name)+r'\s*\)',get_cell(terminal['master']));assert pin_match
                pin_body=group(get_cell(terminal['master']),pin_match.start())
                capture=arcs(block.split('data arrival time',1)[1]);clock_rows=[row for row in capture if row['pin'].rsplit('/',1)[0]==endpoint.rsplit('/',1)[0]]
                hold=re.search(r'(-?\d+\.\d+)\s+(-?\d+\.\d+)\s+library hold time',block)
                max_constraints=[]
                for timing_match in re.finditer(r'timing\s*\(\s*\)',pin_body):
                    timing=group(pin_body,timing_match.start())
                    if not re.search(r'timing_type\s*:\s*hold_(?:rising|falling)',timing):continue
                    for constraint in ['rise_constraint','fall_constraint']:
                        found=re.search(r'\b'+constraint+r'\s*\(\s*(\w+)',timing)
                        if not found:continue
                        body=group(timing,found.start());template=re.search(r'lu_table_template\s*\(\s*'+re.escape(found[1])+r'\s*\)',library)
                        assert template,('Constraint template missing',found[1]);definition=group(library,template.start())
                        assert re.search(r'variable_1\s*:\s*constrained_pin_transition',definition) and re.search(r'variable_2\s*:\s*related_pin_transition',definition), 'Unknown constraint axis order'
                        axes=[list(map(float,re.search(r'index_'+str(number)+r'\s*\(\s*"([^"]+)"',body)[1].split(','))) for number in [1,2]]
                        values=[list(map(float,row.split(','))) for row in re.findall(r'"([^"]+)"',body[body.index('values'):])]
                        if not clock_rows or not hold or not axes[1][0]<=clock_rows[-1]['slew_ns']<=axes[1][-1]:constraint_known=False;continue
                        max_constraints.extend(interpolate((axes,values),data_slew,clock_rows[-1]['slew_ns']) for data_slew in axes[0])
                if max_constraints and hold and constraint_known:
                    constraint_drift=max(0,max(max_constraints)-float(hold[1]));constraint_proof=dict(kind='endpoint_hold_table_at_fixed_actual_clock_slew',current_native_hold_ns=float(hold[1]),clock_slew_ns=clock_rows[-1]['slew_ns'],worst_allowed_data_slew_hold_ns=max(max_constraints),maximum_hold_requirement_increase_ns=constraint_drift)
                else:constraint_known=False;constraint_unknown.append(endpoint);constraint_proof={'kind':'unknown_endpoint_constraint_domain'}
            async_or_clock=bool(re.search(r'/(?:CLK|A_CLK|RESET_B|SET_B|GATE)$',endpoint))
            if async_or_clock:constraint_known=False;constraint_unknown.append(endpoint)
            total_bound=bound+constraint_drift+.1
            if kind=='min':loss_bounds.append(total_bound)
            if kind=='max':setup_gains.append(direct_gain-.1)
            actual[endpoint]=dict(slack_ns=slack,startpoint=native_paths[endpoint]['startpoint'],pair_arcs=details,rough_direct_pair_gain_ns=direct_gain,total_sizing_hold_loss_bound_ns=total_bound,downstream_min_input_slew_speedup_bound_ns=bound,endpoint_constraint=constraint_proof,endpoint_constraint_known=constraint_known,async_or_clock_endpoint=async_or_clock)
        assert set(actual)==set(native_paths),('Native full report and endpoint ledger disagree',key)
        analyzed['/'.join(key)]=actual
    for driver,traces in reach.items():
        covered={kind:set().union(*(set(ledger[(driver,edge,kind)]) for edge in ['rise','fall'])) for kind in ['max','min']}
        missing=sorted(traces['all']-(covered['max']&covered['min']))
        coverage.append(dict(driver=driver,structural_all_endpoints=sorted(traces['all']),timing_enabled_endpoints=sorted(traces['timing']),disabled_or_constant_structural_only=sorted(traces['all']-traces['timing']),covered_max_endpoints=sorted(covered['max']),covered_min_endpoints=sorted(covered['min']),uncovered_structural_unknown=missing))
    complete=all(row['structural_all_endpoints'] and not row['uncovered_structural_unknown'] for row in coverage) and not constraint_unknown
    max_slacks=[row['slack_ns'] for key,paths in analyzed.items() if key.endswith('/max') for row in paths.values()]
    min_slacks=[row['slack_ns'] for key,paths in analyzed.items() if key.endswith('/min') for row in paths.values()];assert max_slacks and min_slacks
    return dict(coverage_complete=complete,coverage_ledger=coverage,unknown_constraint_endpoints=sorted(set(constraint_unknown)),separate_driver_and_data_edge_paths=analyzed,minimum_through_setup_ns=min(max_slacks),minimum_through_hold_ns=min(min_slacks),maximum_library_downstream_speedup_bound_ns=max(loss_bounds),minimum_rough_setup_pair_gain_after100ps_loading_allowance_ns=min(setup_gains),scope='Separate914/913 andrise/fall endpoint paths; complete structuralall coverage orreject. Engineering hold-loss budget includes pair+all downstream minimum-input-slew library estimates, endpoint hold-table drift at frozen clock slew, plus100ps wire/loading allowance. Unknown constraint domains/clock/async endpoints reject sizing. Not post-ECO STA or signoff.')

