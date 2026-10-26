"""Owned, source-defined ITF_MIN/TYP/MAX process policy; HOST preparation only.

Merged ITF geometry/ER/Rsheet is the sole process input. No draft width_delta or
scaled-gap recipe is imported. Source arithmetic is not foundry qualification.
"""
import ast
from decimal import Decimal as D
import hashlib
import json
from pathlib import Path
import sys

sys.path.insert(0,str(Path(__file__).resolve().parent))
import streaming_8x4_model24_geometry as A
import streaming_8x4_rc_process as P

G=A.G
CORNERS=('ITF_MIN','ITF_TYP','ITF_MAX')
ITF_COMMIT='7c783c7c56086511be93bb2097bee656a26148bd'
ITF_SHA={'ITF_MIN':'ad16a5ade248c7d87c7a6789887e5a99cf9431f639358c6c104643527f879e73',
 'ITF_TYP':'08d0de3413256b996b7b6c5a1816e02f8dae4151e0df12c7a8f081ccee415cea',
 'ITF_MAX':'969f391818c63d3057bf4554067626f2ec65c4949bb9a3820cc05ba74e67cb86'}
INTAKE_MANIFEST='2f9121203214d9ad6afa287e53fd51a6ca34405405971b3fdac531a5e211fd2d'
METALS=('Metal1','Metal2','Metal3','Metal4','TopMetal1')


def token(value):
    return format(D(value),'f')


def policy():
    return dict(schema='pinwheel.model24-merged-itf-process-policy.v1',corners=list(CORNERS),
        source_commit=ITF_COMMIT,sole_source='exact merged CMOS5L ITF per corner',
        geometry_policy='nominal source geometry; no draft width_delta, dielectric-gap scaling or invented correlation',
        routing_height_convention='fox+nitride+dummyOx below M1; oxN includes lower metal thickness',
        excluded_routing_height_layers=['Activ','GatPoly','Trench'],
        substrate_reference='grounded silicon-surface plane y=0; finite prism/ground extension remains empirical',
        missing_authority=['source width/height/tolerance correlation beyond merged ITF',
            'design-relevant via/contact/spreading assumptions and generated geometry',
            'actual final-route width/spacing/context/corner applicability'],
        source_arithmetic_does_not_establish_foundry_corner_qualification=True,
        full_PDK_qualified=False,model_qualified=False,qualified_timing=False)


def emit(itf_text,corner):
    P.need(corner in CORNERS,'Undeclared owned ITF corner');rows=G.parse_itf(itf_text);stack=G.stack(rows)
    conductors=[];previous=D(0);text=['# '+corner+'; owned source-defined merged-ITF policy, not foundry qualification.']
    for index,name in enumerate(METALS,1):
        m=stack['metals'][name];bottom,top=map(D,(m['bottom_um'],m['top_um']));thick=D(m['THICKNESS'])
        P.need(top-bottom==thick and bottom>previous,'Invalid source metal ordering/gap')
        fields=dict(distance=token(bottom-previous),thickness=token(thick),min_width=m['WMIN'],min_spacing=m['SMIN'],
            resistivity=token(D(m['RPSQ'])*thick))
        text += ['CONDUCTOR '+name+' {']+['    '+k+' '+v for k,v in fields.items()]+['}']
        conductors.append(dict(index=index,name=name,bottom_um=str(bottom),top_um=str(top),source_RPSQ=m['RPSQ'],fields=fields));previous=top
    # Split original source dielectric slabs at every metal surface. This keeps
    # every ER transition and exactly reconstructs each native process segment.
    boundaries={D(0),D(stack['top_um'])}
    for s in stack['slabs']:boundaries.update((D(s['lo_um']),D(s['hi_um'])))
    for m in conductors:boundaries.update((D(m['bottom_um']),D(m['top_um'])))
    axis=sorted(boundaries);dielectrics=[];counts={}
    for lo,hi in zip(axis,axis[1:]):
        center=(lo+hi)/2;source=[s for s in stack['slabs'] if D(s['lo_um'])<center<D(s['hi_um'])]
        P.need(len(source)==1,'Incomplete/overlapping merged ITF partition')
        within=[m for m in conductors if D(m['bottom_um'])<center<D(m['top_um'])]
        if within:kind='met';metal=within[0]['index'];prefix='m'+str(metal)
        else:
            above=[m for m in conductors if center<D(m['bottom_um'])]
            kind='next_met' if above else None;metal=above[0]['index'] if above else None
            prefix='m'+str(metal) if metal else 'pass'
            if lo==0:prefix='p1'
        counts[prefix]=counts.get(prefix,0)+1;name=prefix+'_'+str(counts[prefix]);er=source[0]['er']
        fields=dict(epsilon=er,thickness=token(hi-lo))
        if kind:fields[kind]=str(metal)
        text+=['DIELECTRIC '+name+' {']+['    '+k+' '+v for k,v in fields.items()]+['}']
        dielectrics.append(dict(name=name,bottom_um=str(lo),top_um=str(hi),source_layer=source[0]['name'],fields=fields))
    air=rows['air'];P.need(air['kind']=='DIELECTRIC' and D(air['ER'])==1,'Unspecified outside medium')
    text += ['DIELECTRIC air_1 {','    epsilon '+air['ER'],'    thickness '+air['THICKNESS'],'}']
    result='\n\n'.join(text)+'\n';verify_emission(result,conductors,dielectrics,air)
    return dict(corner=corner,policy=policy(),source_sha256=hashlib.sha256(itf_text.encode()).hexdigest(),
        process_text=result,process_sha256=hashlib.sha256(result.encode()).hexdigest(),
        conductors=conductors,dielectrics=dielectrics,air=dict(ER=air['ER'],THICKNESS=air['THICKNESS']),
        fullstack=stack,model_qualified=False,qualified_timing=False)


def verify_emission(text,conductors,dielectrics,air):
    actual=P.parse_stack(text);expected={}
    for row in conductors:expected['CONDUCTOR',row['name']]={k:D(v) for k,v in row['fields'].items()}
    for row in dielectrics:expected['DIELECTRIC',row['name']]={k:D(v) for k,v in row['fields'].items()}
    expected['DIELECTRIC','air_1']=dict(epsilon=D(air['ER']),thickness=D(air['THICKNESS']))
    P.need(actual==expected,'Owned emitted process differs from every source-bound numeric field')
    return True


def sources():
    pending=[Path(__file__).name];done={}
    while pending:
        name=pending.pop()
        if name in done:continue
        path=Path(__file__).with_name(name);done[name]=P.sha(path)
        for node in ast.walk(ast.parse(path.read_text())):
            imports=[n.name for n in node.names] if isinstance(node,ast.Import) else ([node.module] if isinstance(node,ast.ImportFrom) and node.module else [])
            pending += [n+'.py' for n in imports if n.startswith('streaming_') and '.' not in n]
    return dict(sorted(done.items()))


def expected_manifest(cases,intake_manifest_sha256):
    return dict(schema='pinwheel.model24-merged-itf-process-preparation.v1',policy=policy(),cases=cases,
        intake_manifest_sha256=intake_manifest_sha256,producer_sha256=sources(),
        native_process_grammar_accepted=False,native_grammar_requires_separate_source_or_observation=True,
        model_qualified=False,qualified_timing=False,native_executed=False)


def verify(output):
    path=output/'manifest.json';P.need(path.is_file() and not path.is_symlink(),'Missing/aliased owned process manifest')
    manifest=json.loads(path.read_text());cases=[];names={'manifest.json'}
    for corner in CORNERS:
        itf=output/(corner+'.itf');process=output/(corner+'.process');names.update((itf.name,process.name))
        P.need(itf.is_file() and not itf.is_symlink() and process.is_file() and not process.is_symlink(),
            'Missing/aliased complete process corner')
        text=itf.read_text();P.need(hashlib.sha256(text.encode()).hexdigest()==ITF_SHA[corner],'Copied exact merged ITF differs')
        row=emit(text,corner);P.need(process.read_bytes()==row.pop('process_text').encode(),'Owned source-defined process differs');cases.append(row)
    P.need({p.name for p in output.iterdir()}==names,'Owned process complete file membership differs')
    P.need(manifest==expected_manifest(cases,manifest['intake_manifest_sha256']),
        'Owned process manifest/source/corner/geometry/assumption/scope differs')
    P.need(manifest['intake_manifest_sha256']==INTAKE_MANIFEST,'Exact retained source-intake manifest identity differs')
    return manifest


def prepare(intake,output):
    P.need(P.sha(intake/'manifest.json')==INTAKE_MANIFEST,'Exact retained source provenance differs')
    values,manifest=P.verify_intake(intake);P.need(not output.exists(),'Preserve owned process policy evidence');output.mkdir()
    cases=[]
    for corner in CORNERS:
        text=values['itf_'+corner[4:].lower()];P.need(hashlib.sha256(text.encode()).hexdigest()==ITF_SHA[corner],'Exact official merged ITF source differs')
        row=emit(text,corner);(output/(corner+'.itf')).write_text(text);(output/(corner+'.process')).write_text(row.pop('process_text'));cases.append(row)
    report=expected_manifest(cases,P.sha(intake/'manifest.json'))
    (output/'manifest.json').write_text(json.dumps(report,indent=2)+'\n');verify(output);return report


if __name__=='__main__':
    import argparse
    q=argparse.ArgumentParser(description=__doc__);q.add_argument('--intake',type=Path,required=True);q.add_argument('--output',type=Path,required=True)
    a=q.parse_args();prepare(a.intake,a.output);print(P.sha(a.output/'manifest.json'))
