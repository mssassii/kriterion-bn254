#!/usr/bin/env python3
"""Finite Eisenstein digit alphabets and optimistic byte accounting; no new construction."""
import json
from pathlib import Path
from opus_budget_model import R,ceildiv
ROOT=Path(__file__).resolve().parents[1]
def norm(z):a,b=z;return a*a-a*b+b*b
def add(z,w):return z[0]+w[0],z[1]+w[1]
def mul(z,w):a,b=z;c,d=w;return a*c-b*d,a*d+b*c-b*d
units=[(1,0),(-1,0),(0,1),(0,-1),(1,1),(-1,-1)]
assert all(norm(u)==1 for u in units)
b7=(2,-1);d7=[(0,0)]+units
radices=[(b7,d7),((4,1),[(0,0)]+units+[mul((2,0),u) for u in units]),
         ((5,2),[(0,0)]+units+[mul((2,0),u) for u in units]+[mul((1,-1),u) for u in units]),
         (mul(b7,b7),[add(d,mul(b7,e)) for d in d7 for e in d7])]
rows=[]
for radix,digits in radices:
 n=norm(radix);a,b=radix;omega=(-a*pow(b,-1,n))%n
 assert (omega*omega+omega+1)%n==0
 image=[(x+omega*y)%n for x,y in digits]
 assert len(digits)==n and set(image)==set(range(n))
 d=0
 while n**d<R:d+=1
 # Strong optimistic assumption: every larger-alphabet digit costs the same
 # seven records/265 public bits; same conversion data, no extra features.
 bits=762+d*265+2*2885*101+(7*d+5)*620
 rows.append({'norm':n,'radix':radix,'quotient_omega':omega,'alphabet_count':len(digits),
              'digit_norm_counts':{str(k):sum(norm(x)==k for x in digits) for k in sorted({norm(x) for x in digits})},
              'information_count':d,'seven_records_per_digit_hypothetical_bytes':ceildiv(bits,8),
              'hypothetical_records':7*d+5})
report={'status':'finite alphabet arithmetic only; information counts are not a bounded digit algorithm or proof',
        'assumption':'optimistically retain seven affine records and265 public bits per digit, existing conversion data; new endomorphism rows and privacy are unproved',
        'results':rows}
(ROOT/'evidence/structural/digit-radices.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
