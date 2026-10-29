"""Synthetic matrix→import-slot→consumer units control; no physical fitting.

Native import labels select documented importer branches. They do not assert a
physical three-neighbor training geometry for the synthetic two-signal matrix.
"""
from decimal import Decimal as D
import hashlib
import re
import streaming_8x4_model24_contract as K
import streaming_8x4_model24_native_geometry as N
import streaming_8x4_rc_cap_marker_geometry as G
import streaming_8x4_rc_cap_marker_spef as Z
import streaming_8x4_rc_consumer_cap_spef as Q
P=K.P
MODES=('legacy-projection','explicit-diagonal-projection')
WIDTHS={1:D('.16'),2:D('.2'),3:D('.2'),4:D('.2'),5:D('1.64')}
TARGET='1v2/MODEL24_TYP/UnderDiag1/M1duM2/W0.16_W0.2/S0.18_S0_L10/wires'


def policy():
    return dict(schema='pinwheel.model24-synthetic-diagonal-policy.v1',calls=2,modes=list(MODES),
        synthetic_lower_layer='Metal1',synthetic_upper_layer='Metal2',synthetic_wire_length_um='20',
        synthetic_pair_coupling_F_per_m='0.000000000002',synthetic_ground_F_per_m='0.000000000003',
        importer_divides_total_fF_by_nm_length_and_two=True,source_expected_zero_distance_fringe_fF_per_nm='0.000001',
        source_expected_actual_consumer_pair_slope_F_per_m='0.000000000002',
        consumer_callback_accumulation_factor=2,original_factor_two_prediction_failure_preserved=True,
        import_dist_is_actual_edge_distance_not_lower_neighbor_spacing=True,import_upper_width_axis_not_supported=True,
        logical_nonopen_import_slot_is_not_a_physical_three_wire_claim=True,
        supporting_rule_records_are_synthetic_scaffolding_not_physical_coefficients=True,
        fixed_default_upper_width_only=True,extractor_version='1.0',coupling_threshold='0',cc_model='10',context_depth=5,
        lef_res=False,merge_via_wire_res=False,no_cells_iterms_vias=True,fixture_lengths_um=[50,100,150],
        coupling_prediction_relative_tolerance='0.001',coupling_consecutive_slope_tolerance='0.001',
        full_matrix_ground_consecutive_slope_tolerance='0.05',all_warnings_fatal=True,
        leaf_seconds=30,work_seconds=90,outer_seconds=120,cpu=1,memory_bytes=2147483648,
        extra_swap_bytes=0,tmpfs_bytes=134217728,maximum_output_bytes=268435456,
        physical_model_accuracy='unmeasured',coefficient_fitted=False,model_qualified=False,qualified_timing=False)


def synthetic_projection():
    roles=[dict(ordinal=i,name=n,role='ground' if i==1 else 'signal',matrix_name='g'+str(i)+'_'+n,
        origin='declared synthetic unit-control conductor, no foundry physics') for i,n in enumerate(('GROUND','LOWER','UPPER'),1)]
    names=K.role_names(roles);g=D('3e-12');k=D('2e-12');extra=D('1e-12')
    density=[[2*g+extra,-g,-g],[-g,g+k,-k],[-g,-k,g+k]];rows=[]
    for length in (D(10),D(20)):
        matrix=[[str(v*length/D(1000000)) for v in row] for row in density];P.matrix_physics(names,matrix)
        rows.append(dict(ordered_conductor_roles=roles,signal_names=['LOWER','UPPER'],
            signal_matrix_F=[row[1:] for row in matrix[1:]],full_matrix_F=matrix,length_um=str(length)))
    slope=K.length_difference(rows[0],rows[1],'10','20');pair=-D(slope['matrix_F_per_m'][0][1]);P.need(pair==k,'Synthetic projected pair units differ')
    total=pair*D('20e-6')*D('1e15');wlen=D(20)*1000;coefficient=total/wlen/2
    P.need(coefficient==D('1e-6'),'Synthetic import /2 units differ')
    return dict(roles=roles,rows=rows,slopes=slope,pair_F_per_m=str(pair),total_pair_fF_at_20um=str(total),
        importer_length_nm=str(wlen),expected_imported_fringe_fF_per_nm=str(coefficient),
        actual_consumer_callback_factor=2,expected_consumer_pair_F_per_m=str(coefficient*2*D('1e-6')),
        physical_coefficients=False,model_qualified=False)


def table_line(met,under,over,diag,dist,width,length,cc,fr,tc,cc2,path,diagcc=None):
    row=f'Metal {met} Over {under} '+('DiagUnder ' if diag else 'Under ')+f'{over} Dist {dist} Width {width} LEN {length} CC {cc} FR {fr} TC {tc} CC2 {cc2}'
    if diag:row+=f' DiagDist 0 DiagWidth {WIDTHS[int(over)]} DiagCC {diagcc if diagcc is not None else 0}'
    return row+' '+path+'\n'


def caps(patterns,mode):
    P.need(mode in MODES and len(patterns)==310 and len({r['path'] for r in patterns})==310,'Complete fixed synthetic scaffold universe required')
    projection=synthetic_projection();lines=[];special=0
    for item in patterns:
        parsed=N.parse(item['text'],item['path']);target=next(r for r in parsed['wires'] if r['voltage']==1);met=int(target['name'].split('_')[0][1:]);width=WIDTHS[met]
        grounds=[int(r['name'].split('_')[0][1:]) for r in parsed['grounds']];diag=parsed['family'].startswith('UnderDiag')
        under=0 if parsed['family'].startswith('Under') else grounds[0];over=0 if parsed['family'].startswith('Over') and not parsed['family'].startswith('OverUnder') else (int(parsed['wires'][-1]['name'].split('_')[0][1:]) if diag else grounds[-1])
        dist=item['path'].split('/')[-2].split('_')[0][1:];length=10;wlen=width*length*1000;fr=D('3e-6')*wlen;cc=D(0)
        logical='/'.join(item['path'].split('/')[1:-1])+'/wire_'+str(target['index'])
        if item['path']==TARGET:
            special+=1;length=125;cc=D(0) if mode==MODES[0] else D(projection['total_pair_fF_at_20um'])
            # The old parser's FR diagonal-minus-same-layer CC includes this
            # pair coupling. The corrected diagonal branch stores CC instead.
            fr=D('0.1') if mode==MODES[0] else D('0.06')
            logical='MODEL24_SYNTHETIC/'+('UnderDiag1' if mode==MODES[0] else 'UnderDiag3')+'/M1duM2/W0.16_W0.2/S0_S0_L125/wire_'+('1' if mode==MODES[0] else '2')
            dist='.18' if mode==MODES[0] else '0'
        lines.append(table_line(met,under,over,diag,dist,width,length,cc,fr,cc+fr,0,logical,
            projection['total_pair_fF_at_20um'] if item['path']==TARGET else '0'))
    P.need(special==1,'Exact synthetic target replacement required')
    # Positive resistance scaffolding only: the arithmetic is deliberately not
    # admitted as a CMOS5L R model or used for a resistance qualification claim.
    for met,width in WIDTHS.items():
        lines.append(f'Metal {met} RESOVER 0 Under 0 Dist 0 Width {width} LEN 10 CC 0 FR 0 TC 0 CC2 0 RES 1 MODEL24_SYNTHETIC/Over1/M{met}oM0/W{width}_W{width}/S0_S0_L10/wire_0\n')
    return ''.join(lines)


def fixture():
    return G.fixture(G.definition('retained'))


def import_grid(text,mode):
    P.need(mode in MODES and re.findall(r'^LayerCount\s+(\d+)\s*$',text,re.M)==['5']
        and re.findall(r'^Corners\s+1\s*:\s*(\w+)\s*$',text,re.M)==['MODEL24_SYNTHETIC']
        and re.findall(r'^DIAGMODEL\s+(\w+)\s*$',text,re.M)==['ON'],'Synthetic imported model header/version/corner differs')
    P.need(re.findall(r'^Version\s+([^\n]+)$',text,re.M)==['1.2'],'Synthetic imported table format differs')
    found=re.findall(r'^Metal 1 DIAGUNDER 2\s*\nDIST count (\d+) width (\S+)\s*\n(.*?)^END DIST\s*$',text,re.M|re.S)
    P.need(len(found)==1 and D(found[0][1])==D('.16'),'Exact imported diagonal width grid required')
    count,_,body=found[0];rows=[[P.number(x) for x in line.split()] for line in body.splitlines() if line.strip()]
    P.need(len(rows)==int(count) and all(len(r)==4 and all(v>=0 for v in r) for r in rows),'Complete imported grid numeric membership differs')
    zero=[r for r in rows if r[0]==0];wanted=D(0) if mode==MODES[0] else D('1e-6')
    P.need(len(zero)==1 and zero[0]==[D(0),D(0),wanted,D(0)],'Source-predicted exact imported zero-distance coefficient differs')
    P.need(all(r[1:]==[D(0)]*3 for r in rows if r[0]!=0),'Unintended nonzero diagonal support knot')
    return dict(ordered_grid=[[str(x) for x in row] for row in rows],exact_zero_row=list(map(str,zero[0])),
        projection_import_units_passed=True,physical_accuracy=False)


def read_cap(spef,mode):
    job=G.definition('retained');names=[r['net'] for r in job['rows']]
    if mode==MODES[0]:
        error=None
        try:Q.parse(spef,names,job['partners'])
        except ValueError as e:error=str(e)
        P.need(error=='Missing intended coupling or incident total differs','Exact legacy zero-coupling strict failure must remain')
        zero=Z.zero_inventory(spef,names,job['partners']);P.need(zero['all_three_intended_couplings_exactly_zero'] is True,'Legacy exact three zero couplings required')
        return dict(strict_physics_passed=False,strict_error='ValueError: '+error,zero_inventory=zero)
    values=Q.parse(spef,names,job['partners']);slopes=G.C.slopes(None,values);couplings=[-D(s['matrix_F_per_m'][0][1]) for s in slopes]
    expected=D('2e-12');errors=[abs(k/expected-1) for k in couplings];linear=abs(couplings[0]/couplings[1]-1);change=G.C.relative(G.C.vector(slopes[0]),G.C.vector(slopes[1]))
    P.need(max(errors)<=D('.001') and linear<=D('.001') and change<=D('.05'),'Synthetic projection→import→consumer prediction/linearity differs')
    return dict(strict_physics_passed=True,slopes=slopes,coupling_slopes_F_per_m=list(map(str,couplings)),
        predicted_coupling_slope_F_per_m='2e-12',prediction_errors=list(map(str,errors)),consecutive_coupling_change=str(linear),
        full_matrix_ground_consecutive_change=str(change),synthetic_unit_control_only=True,model_qualified=False)


def compare_decks(baseline,candidate):
    import_grid(baseline,MODES[0]);import_grid(candidate,MODES[1])
    pattern=r'^Metal 1 DIAGUNDER 2\s*\nDIST count \d+ width \S+\s*\n(.*?)^END DIST\s*$'
    found=re.search(pattern,candidate,re.M|re.S);P.need(found is not None,'Exact candidate imported grid absent')
    body=found[1];lines=list(re.finditer(r'^([^\n]+)$',body,re.M));offset=None
    for line in lines:
        words=line[1].split()
        if words and P.number(words[0])==0:
            P.need(len(words)==4,'Exact zero row shape differs')
            offset=len(candidate[:found.start(1)+line.start(1)].split())+2
    P.need(offset is not None,'Exact candidate zero fringe token absent')
    def canonical(text):
        return [str(P.number(t).normalize()) if re.fullmatch(P.NUM,t) else t for t in text.split()]
    a,b=canonical(baseline),canonical(candidate);P.need(len(a)==len(b),'Imported scaffold token counts differ')
    differences=[i for i,(x,y) in enumerate(zip(a,b)) if x!=y]
    P.need(differences==[offset] and D(a[offset])==0 and D(b[offset])==D('1e-6'),
        'More than the source-predicted zero-distance fringe coefficient changed')
    return dict(exact_single_imported_numeric_delta=True,zero_distance_fringe_fF_per_nm=['0','0.000001'],
        model_qualified=False)
