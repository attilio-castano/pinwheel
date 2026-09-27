"""Independent edge-accounting oracle for the pinned native import experiment."""
from collections import Counter
import re


def parse_snapshot(text):
    lines=[line.split('\t') for line in text.splitlines()]
    if not lines or len(lines[0])!=7 or lines[0][0]!='grid':
        raise ValueError('Missing resource grid header')
    nx,ny,nl,ox,oy,pitch=map(int,lines[0][1:])
    if nx<2 or ny<2 or nl<1 or pitch<=0:
        raise ValueError('Invalid resource grid')
    edges={};nets={}
    for row in lines[1:]:
        if row[0] in ('2','3') and len(row)==8:
            dim,d,l,x,y,cap,red,use=row
            dim,l,x,y,cap,red,use=map(int,[dim,l,x,y,cap,red,use])
            if (d not in ('H','V') or not 0<=x<nx-(d=='H')
                    or not 0<=y<ny-(d=='V') or (dim==2 and l!=0)
                    or (dim==3 and not 1<=l<=nl) or min(cap,red,use)<0):
                raise ValueError('Invalid resource edge')
            key=(dim,d,l,x,y)
            if key in edges:raise ValueError('Duplicate resource edge')
            edges[key]=(cap,red,use)
        elif row[0]=='net' and len(row)==4+nl:
            name=row[1];cost,soft,*layers=map(int,row[2:])
            if (name in nets or not re.fullmatch(r'[A-Za-z0-9_./\[\]$-]+',name)
                    or cost<1 or soft not in (0,1) or min(layers)<1):
                raise ValueError('Invalid per-net cost')
            nets[name]=dict(cost=cost,soft=bool(soft),layers=layers)
        else:raise ValueError('Invalid resource row')
    expected=((nx-1)*ny+nx*(ny-1))*(nl+1)
    if len(edges)!=expected or not nets:raise ValueError('Incomplete resource snapshot')
    return dict(grid=(nx,ny,nl,ox,oy,pitch),edges=edges,nets=nets)


def route_demand(snapshot, routes):
    """Count each unit wire edge; vias consume no planar routing resources.

    This oracle expands native segment exports independently of the C++ trees.
    Multiplicity is retained, and 2-D demand can differ from layer-specific cost.
    """
    nx,ny,nl,ox,oy,pitch=snapshot['grid'];result=Counter()
    for name,segments in routes.items():
        for a,b in segments:
            x,y,l=a;xx,yy,ll=b
            if l!=ll:continue
            if (x,y)==(xx,yy):continue
            if not re.fullmatch('Metal[1-9][0-9]*',l) or name not in snapshot['nets']:
                raise ValueError('Missing wire layer or cost')
            layer=int(l[5:]);cost=snapshot['nets'][name]
            if not 1<=layer<=nl:raise ValueError('Layer outside resource grid')
            ix,iy=(x-ox)//pitch,(y-oy)//pitch;jx,jy=(xx-ox)//pitch,(yy-oy)//pitch
            if min(ix,jx)<0 or max(ix,jx)>=nx or min(iy,jy)<0 or max(iy,jy)>=ny:
                raise ValueError('Wire outside resource grid')
            if iy==jy:
                keys=[('H',k,iy) for k in range(min(ix,jx),max(ix,jx))]
            elif ix==jx:
                keys=[('V',ix,k) for k in range(min(iy,jy),max(iy,jy))]
            else:raise ValueError('Non-Manhattan wire')
            for d,ex,ey in keys:
                result[(2,d,0,ex,ey)]+=cost['cost']
                result[(3,d,layer,ex,ey)]+=cost['layers'][layer-1]
    return result


def verify_demand(snapshot, routes):
    expected=route_demand(snapshot,routes)
    wrong=[key for key,value in snapshot['edges'].items() if value[2]!=expected[key]]
    if wrong:raise ValueError(f'Native resource demand disagrees with wires on {len(wrong)} edges; first {wrong[:4]}')
    return dict(checked_edges=len(snapshot['edges']),occupied_edges=sum(v>0 for v in expected.values()),
                demand_2d=sum(v for k,v in expected.items() if k[0]==2),
                demand_3d_by_layer={str(l):sum(v for k,v in expected.items() if k[0]==3 and k[2]==l)
                                    for l in range(1,snapshot['grid'][2]+1)})


def verify_release(before, released, routes):
    if before['grid']!=released['grid'] or before['nets']!=released['nets']:
        raise ValueError('Release changed grid or net costs')
    expected=route_demand(before,routes)
    for key,a in before['edges'].items():
        b=released['edges'][key]
        if a[:2]!=b[:2] or a[2]-b[2]!=expected[key]:
            raise ValueError('Native removal differs from wire demand: '+str(key))
    if not expected:raise ValueError('Empty removal regression')
    return dict(checked_edges=len(before['edges']),released_edges=len(expected),
                released_2d=sum(v for k,v in expected.items() if k[0]==2),
                released_3d=sum(v for k,v in expected.items() if k[0]==3))
