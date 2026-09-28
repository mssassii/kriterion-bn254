#!/usr/bin/env python3
"""Counterfactual record-removal costs, NOT an implemented construction.

Keep all current public data and moduli, remove selected affine deliveries per
91 digits, then optimize the shared two-stage schedule under the query caps.
The arithmetic does not establish that the removed deliveries can be recovered,
or that correctness/privacy or the actual simulator would still hold.
"""
import json, math, re
from pathlib import Path
from check_width9 import row, ceildiv, extraction

ROOT=Path(__file__).resolve().parents[1]
interface=(ROOT/'Construction/CRT/Interface.lean').read_text()
mods=list(map(int,re.findall(r'\d+',re.search(r'def bn254Moduli.*?#\[(.*?)\]',interface,re.S)[1])))
assert len(mods)==84 and 17 not in mods
record_bits=(2*math.prod(mods)-1).bit_length()
assert record_bits==620
states={0:(0,0,[])}
for m in mods:
    if m==256:continue
    opts=[r for w in range(7,12) if (r:=row(m,w)) is not None]
    nxt={}
    for width,(e,g,rs) in states.items():
        for r in opts:
            key=width+r['w0'];value=(e+2*r['evaluate'],g+2*r['garble'],rs+[r])
            if key not in nxt or value[:2]<nxt[key][:2]:nxt[key]=value
    states=nxt
chunk_g=2*sum(extraction(w,14)[0] for w in [8]*31+[6])+2291
chunk_e=2*sum(extraction(w,14)[1] for w in [8]*31+[6])+1783
results=[]
for rx in range(4):
    for ry in range(3):
        counts=(367-91*rx,275-91*ry)
        bg=be=0
        for s in counts:
            for m in mods:
                q=ceildiv(8*s,256) if m==256 else ceildiv((m**s).bit_length()+120,256)
                bg+=m*q;be+=(m-1)*q
        feasible=[(w,v) for w,v in states.items() if v[0]+be+chunk_e<=1055879 and v[1]+bg+chunk_g<=1759967]
        if not feasible:raise AssertionError(counts)
        width,(e,g,rs)=max(feasible,key=lambda x:x[0])
        blocks=32*13+sum(r['blocks'] for r in rs)
        bits=762+23387+728+2*blocks*101+sum(counts)*record_bits
        results.append(dict(removed_x_per_digit=rx,removed_y_per_digit=ry,
                            records=sum(counts),x_count=counts[0],y_count=counts[1],
                            conversion_labels_per_coordinate=blocks,
                            bytes=ceildiv(bits,8),garble=g+bg+chunk_g,evaluate=e+be+chunk_e,
                            width_counts={str(w):sum(r['w0']==w for r in rs) for w in range(7,12)}))
base=results[0]
assert (base['bytes'],base['garble'],base['evaluate'])==(125711,1061622,1054788)
report={'status':'counterfactual arithmetic only; no removed record has a proved replacement',
        'fixed_sources':'857e88b66f91ce0c61ab0e86ff6d8b9e9bf91790',
        'scope':'same moduli and public fields, fixed symmetric extraction family; no global bound',
        'results':results}
(ROOT/'evidence/structural/record-removal-costs.json').write_text(json.dumps(report,indent=2)+'\n')
for r in sorted(results,key=lambda r:(r['removed_x_per_digit']+r['removed_y_per_digit'],r['removed_x_per_digit'])):print(r)
