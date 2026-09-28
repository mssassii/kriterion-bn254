#!/usr/bin/env python3
"""Exact nine-bit chunk cost/privacy/reach certificate experiment, no production change."""
from fractions import Fraction as F
import json, math, re
from pathlib import Path
from opus_budget_model import P,R,G_GATE,E_GATE,extract,ceildiv
ROOT=Path(__file__).resolve().parents[1]
text=(ROOT/'Construction/CRT/Interface.lean').read_text()
oldmods=list(map(int,re.findall(r'\d+',re.search(r'def bn254Moduli.*?#\[(.*?)\]',text,re.S)[1])))
mods=[512 if m==256 else m for m in oldmods]
seven=[73,79,81,83,89,97,101]
rows=[];certs=[];margins=[]
for m in mods:
    if m==512:certs.append(0);continue
    ell=(29*(m-1)).bit_length();w0=7 if m in seven else 8;w1=ell-w0-1
    keep=max(w0,(m-1).bit_length())
    assert w0>=1 and w1>=1 and w0+w1+1==ell and w0<=keep<=ell<=14 and m<=2**keep
    need=max(255,m-1,2**(ell-1)-128)
    a=[(-pow(pow(512,c,m),-1,m))%m for c in range(1,28)]+[0]
    B=min(m,512)-1
    for c,digit in enumerate(a,1):
        bound=3 if c==28 else 512
        term=digit*pow(512,c,m)%m
        assert digit<bound and term<=B+1
        B+=term
    assert B==28*(m-1) and need<=B
    # Every stage/growth/fold target used by the selected two-stage table fits.
    assert 2**w0-1<=need and 2**w0*(2**w1-1)<=need
    assert all(2**n-1<=need for n in range(w0,keep))
    assert all(m<=2**n for n in range(keep,ell))
    certs.append(sum(v*512**j for j,v in enumerate(a)));margins.append(B-need)
    g0,e0=extract(w0,ell,101);g1,e1=extract(w1,ell-w0,101)
    growth=2**keep-2**w0
    rows.append(dict(m=m,ell=ell,w0=w0,w1=w1,keep=keep,
                     pins=(ell-1)+(ell-w0-1), joins=(w0-1)+(w1-1)+(keep-w0)+(ell-keep),
                     g=g0+g1+growth+(ell-keep)*m,
                     e=e0+e1+growth-(keep-w0)+(ell-keep)*(m-1)))
assert 3*512**28<P
cg=sum(extract(w,14,101)[0] for w in [9]*28+[2]);ce=sum(extract(w,14,101)[1] for w in [9]*28+[2])
g=2291;e=1783;pads=F(637*(2**384%P),2**384)
for s in (367,275):
    g+=cg+sum(r['g'] for r in rows);e+=ce+sum(r['e'] for r in rows)
    for m in mods:
        q=ceildiv(s*9,256) if m==512 else ceildiv((m**s).bit_length()+120,256)
        g+=m*q;e+=(m-1)*q
        if m!=512:pads+=F(m*m**s,2**(256*q))
M=math.prod(mods);rec=(2*M-1).bit_length();pins=29+2*83
pubjoins=sum(r['joins'] for r in rows);joins=pubjoins+254-29
blocks=29*13+sum(r['pins']+r['joins'] for r in rows)
public=762+23387+728+2*blocks*101+642*rec;pad=(-public)%8
pieces=1009+2*pubjoins+2*pins*101
smudge=F(1284*(P-1)**2+273*P,M)
C=(F(G_GATE,P)+3*pads+2*smudge+F(546+455,R-1)+F(185+1,2**128))*2**100
charge=F(1,2**101)+F(1,P-1);Q=2**100-1
vertex_margins=[q1+q2+2-C-(2*q1+q2)*charge*2**100 for q1,q2 in ((0,0),(Q,0),(0,Q))]
assert C<=F(1408,1000) and min(vertex_margins)>0
assert g<=G_GATE and e<=E_GATE
assert (ceildiv(public,8),g,e,blocks,rec)==(125261,1062388,1055556,2864,621)
report={'status':'exact model and generated reach certificates; full production proof/migration not performed',
        'source':'857e88b66f91ce0c61ab0e86ff6d8b9e9bf91790','moduli':mods,'width7_moduli':seven,'rows':rows,
        'certificates':certs,'reach_certificate_count':83,'minimum_reach_margin':min(margins),
        'chunk_bits':9,'chunk_count':29,'top_witness_bound':3,'cast_width':14,
        'bytes':ceildiv(public,8),'public_bits':public,'padding_bits':pad,'record_bits':rec,
        'garble':g,'evaluate':e,'evaluate_headroom':E_GATE-e,'conversion_labels_per_coordinate':blocks,
        'pin_count':pins,'join_count':joins,'published_joins':pubjoins,'serializer_pieces':pieces,
        'constant_units_exact':str(C),'constant_units_approx':float(C),
        'worst_vertex_margin_exact':str(min(vertex_margins)),'worst_vertex_margin_approx':float(min(vertex_margins))}
(ROOT/'evidence/chunk9-feasibility/model.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k not in ('rows','certificates','constant_units_exact','worst_vertex_margin_exact')},indent=2))
