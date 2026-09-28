#!/usr/bin/env python3
"""Exact independent arithmetic for the merged whole-public/101-bit candidate."""
from fractions import Fraction
from pathlib import Path
import json, math, re, subprocess
from check_width9 import ceildiv, metrics, row
from opus_next_ideas import queries, constant, W9

root = Path(__file__).resolve().parents[1]
base = 'e37c4db3cdbf11c741ff812ed1b0d5ae7c7b3b05'
def moduli(source):
    return list(map(int, re.findall(r'\d+', re.search(r'def bn254Moduli.*?#\[(.*?)\]', source, re.S)[1])))
original = moduli(subprocess.check_output(['git','show',base+':Construction/CRT/Interface.lean'],cwd=root,text=True))
baseline = metrics(original, [row(m,8) for m in original if m !=256])
assert [baseline[k] for k in ['ciphertext_bytes','garble_queries','evaluate_queries']] == [130122,988438,981506]
mods = moduli((root/'Construction/CRT/Interface.lean').read_text())
assert mods == original[1:] and len(mods)==84
selector = list(map(int, re.findall(r'\d+', re.search(r'def selectiveWidth0.*?\(\[(.*?)\]\s*: List Nat\)', (root/'Construction/CRT/Params.lean').read_text(), re.S)[1])))
assert set(selector)==set(W9) and len(selector)==26
assert 'abbrev labelBits : Nat := 101' in (root/'Construction/CRT/Label.lean').read_text()
# Every ring width has the same rounded cast-answer count at101 and104.
cast_counts = {w:ceildiv(ceildiv(101,128//w),2) for w in range(1,15)}
assert all(cast_counts[w] == ceildiv(ceildiv(104,128//w),2) for w in cast_counts)
old = metrics(mods,[row(m,9 if m in selector else 8) for m in mods if m !=256])
g,e,blocks = queries(label_bits=101)
assert (g,e,blocks)==(old['garble_queries'],old['evaluate_queries'],old['conversion_labels_per_coordinate'])
assert (g,e,blocks)==(1061622,1054788,2885)
M=math.prod(mods); record_bits=(2*M-1).bit_length(); assert record_bits==620
parts=dict(curve=3*254,rows=91*(254+3),exception=91*8,conversion=2*blocks*101,records=642*record_bits)
bits=sum(parts.values());pad=(-bits)%8;total=(bits+pad)//8
pins=32+2*(len(mods)-1);published_joins=blocks-(32*13+sum(row(m,9 if m in selector else 8)['ell']-1 + row(m,9 if m in selector else 8)['ell']-(9 if m in selector else 8)-1 for m in mods if m!=256))
pieces=3+2*91+2*91+642+2*(published_joins+pins*101)
assert (bits,pad,total,pins,published_joins,pieces)==(1005687,1,125711,198,1193,43391)
p=int(re.search(r'def p : Nat := (\d+)', (root/'Proof/Privacy/CRT/Glue/BudgetData.lean').read_text())[1])
charge=Fraction(1,2**101)+Fraction(1,p-1);C,_=constant();Q=2**100-1
margins=[Fraction(q1+q2+2)-C-(2*q1+q2)*charge*2**100 for q1,q2 in [(0,0),(Q,0),(0,Q)]]
assert min(margins)>0
assert charge*2**100 <= Fraction(1,2)+Fraction(1,2**152)
assert Fraction(1408,1000)+Fraction(2**101,2**152)<2
report=dict(status='independent exact arithmetic; Lean checks are separate',p1a='cc221c36a4f8e991d2c983b4ec748d40805ea064',opus101='2f7b9ca70f7a9c72ac4a24e98ddb97cb606e7ee8',components_bits=parts,public_bits=bits,padding_bits=pad,ciphertext_bytes=total,garble_queries=g,evaluate_queries=e,label_bits=101,record_bits=record_bits,pin_count=pins,published_joins=published_joins,serializer_pieces=pieces,cast_answers_by_width=cast_counts,constant_error=str(C),worst_vertex_margin=str(min(margins)))
print(json.dumps(report,indent=2))
(root/'evidence/packed-101/independent-metrics.json').write_text(json.dumps(report,indent=2)+'\n')
