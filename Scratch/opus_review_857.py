#!/usr/bin/env python3
"""Opus: read-only review helper for the integrated commit 857e88b.

1. Classify every entry Lean file and pin of 857e88b by blob: equal to P1a (76f7589 / cc221c3), equal to P1b (2f7b9ca),
   equal to both, or neither (hand-integrated).
2. Recompute the committed source manifest from committed blobs and compare with the expected digest.
"""
import hashlib
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
C, P1A, P1B = ('857e88b66f91ce0c61ab0e86ff6d8b9e9bf91790', '76f7589', '2f7b9ca70f7a9c72ac4a24e98ddb97cb606e7ee8')
MANIFEST_DIGEST = '3396d0568b3d7f061aafd9ba4a860668c115eac1e948d228c758fa4a0b9f99a9'


def git(*args, binary=False):
    return subprocess.run(['git', *args], cwd=ROOT, capture_output=True, check=True, text=not binary).stdout


def tree(sha):
    return {l.split('\t')[1]: l.split()[2] for l in git('ls-tree', '-r', sha).splitlines()}


def entry(p):
    return (p.endswith('.lean') and (p.split('/')[0] in ('Construction', 'Proof') or
                                     p in ('Construction.lean', 'Proof.lean', 'Submission.lean'))) or \
        p in ('lakefile.toml', 'lake-manifest.json', 'lean-toolchain', 'Scratch/Audit.lean', 'Scratch/ProofAudit.lean')


c, a, b = tree(C), tree(P1A), tree(P1B)
groups = {'both': [], 'P1a': [], 'P1b': [], 'neither': []}
for p in sorted(x for x in set(c) | set(a) | set(b) if entry(x)):
    ca, cb = c.get(p) == a.get(p), c.get(p) == b.get(p)
    groups['both' if ca and cb else 'P1a' if ca else 'P1b' if cb else 'neither'].append(p)
for k, v in groups.items():
    print(f'{k}: {len(v)}')
    if k in ('P1b', 'neither'):
        for p in v:
            print('   ', p, '(absent in 857e88b)' if p not in c else '')
# manifest
cands = [p for p in c if p.endswith('source-manifest.json') and 'packed-101' in p]
print('manifest candidates:', cands)
for mp in cands:
    m = json.loads(git('show', f'{C}:{mp}'))
    files = m['files']
    rec = {p: hashlib.sha256(git('show', f'{C}:{p}', binary=True)).hexdigest() for p in sorted(files)}
    dig = hashlib.sha256(json.dumps(rec, sort_keys=True, separators=(',', ':')).encode()).hexdigest()
    lean = {p for p in c if entry(p) and p.endswith('.lean') and not p.startswith('Scratch/')}
    print(f'{mp}: {len(files)} entries; per-file match {rec == files}; digest {dig == MANIFEST_DIGEST} ({dig}); '
          f'entry Lean files missing: {sorted(lean - set(files))[:5]}')
