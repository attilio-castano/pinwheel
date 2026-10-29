"""Explicit full-routing-stack geometry/role adapter, using frozen pure CSG.

This normalizes process fixtures, not yet-unobserved native pattern grammar.
The finite ground/prism truncation remains subject to unchanged boundary gates.
"""
from decimal import Decimal as D
import hashlib

import streaming_8x4_rc_layered_geometry as G
import streaming_8x4_rc_layered_plan as L
import streaming_8x4_rc_process as P
import streaming_8x4_model24_contract as K


def recipes():
    return [dict(case_id='TYP-M2-M3-centered-L20-E20-development',corner='TYP',
        kind='vertical',layers=['Metal2','Metal3'],widths_um=['.20','.20'],offset_um='0',
        length_um='20',extension_um='20',role='development_smoke',
        freshness='physical family already observed in prior campaign; never a fresh heldout'),
        dict(case_id='TYP-M2-lateral-w.30-s.315-L20-E20-heldout',corner='TYP',
        kind='lateral',layers=['Metal2','Metal2'],widths_um=['.30','.30'],gap_um='.315',
        length_um='20',extension_um='20',role='untouched_heldout',
        freshness='new declared geometry; no values may be supplied to coefficient training'),
        dict(case_id='TYP-M3-M4-offset.15-L20-E20-heldout',corner='TYP',
        kind='vertical',layers=['Metal3','Metal4'],widths_um=['.20','.20'],offset_um='.15',
        length_um='20',extension_um='20',role='untouched_heldout',
        freshness='new declared geometry; no values may be supplied to coefficient training')]


def build(text,recipe):
    P.need(recipe in recipes() and recipe['corner']=='TYP','Only exact declared TYP geometry recipe admitted')
    rows=G.parse_itf(text);model=G.stack(rows);itf=P.parse_stack(text)
    widths=list(map(D,recipe['widths_um']))
    if recipe['kind']=='vertical':centers=[D(0),D(recipe['offset_um'])]
    else:
        P.need(widths[0]==widths[1],'Lateral fixture uses two equal widths')
        distance=(D(recipe['gap_um'])+widths[0])/2;centers=[-distance,distance]
    rectangles=[];roles=[dict(ordinal=1,name='GND_SUB',role='ground',matrix_name='g1_GND_SUB',
        origin='finite grounded routing-substrate reference; pilot truncation authority')]
    for index,(layer,width,center) in enumerate(zip(recipe['layers'],widths,centers),2):
        metal=model['metals'][layer];P.need(width>=D(metal['WMIN']),'Wire below declared ITF minimum')
        name='SIGNAL_'+str(index-1)+'_'+layer.upper()
        rectangles.append(dict(name=name,bounds_um=list(map(str,[center-width/2,center+width/2,
            D(metal['bottom_um']),D(metal['top_um'])]))))
        roles.append(dict(ordinal=index,name=name,role='signal',matrix_name='g'+str(index)+'_'+name,
            origin='explicit recipe signal ordinal'+str(index-1)+' on '+layer))
    K.role_names(roles)
    case=dict(name=recipe['case_id'],rectangles=rectangles,epsilon_layers=L.materials(itf))
    files,certificate=G.from_plan(case,recipe['length_um'],recipe['extension_um'])
    P.need(list(certificate['conductors'])==[r['name'] for r in roles],
        'Actual CSG conductor order/role mapping differs')
    return dict(recipe=recipe,case=case,ordered_conductor_roles=roles,full_routing_stack=model,
        material_source_sha256=hashlib.sha256(text.encode()).hexdigest(),files=files,certificate=certificate,
        geometry_operator_sha256=P.sha(G.__file__),same_frozen_CSG_operator=True,
        full_stack_explicit=True,finite_ground_and_prism_boundary_error_still_unmeasured=True,
        native_pattern_grammar_assumed=False,model_qualified=False)
