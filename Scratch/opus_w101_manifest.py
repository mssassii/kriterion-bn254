#!/usr/bin/env python3
"""Opus P1b: source manifest and dependency-pin check for the width-101 candidate.

`write`: SHA-256 of every Lean file of the entry (Construction/, Proof/, Construction.lean, Proof.lean,
Submission.lean), the pins, and the audit/model scripts, taken from the working tree, into
evidence/width101/source-manifest.json. `check [COMMIT]`: recompute from the working tree (or from the committed
blobs of COMMIT) and require equality, and require the commit's Lean file set to equal the manifest's.
`deps`: every package of lake-manifest.json is checked out at its locked revision with a clean tree.
"""
import hashlib
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'evidence/width101/source-manifest.json'
EXTRA = ['lakefile.toml', 'lake-manifest.json', 'lean-toolchain', 'Scratch/Width101Audit.lean', 'Scratch/ProofAudit.lean',
         'Scratch/Audit.lean', 'Scratch/opus_check_w101.py', 'Scratch/opus_budget_model.py', 'Scratch/opus_next_ideas.py',
         'Scratch/opus_gen_budget.py', 'Scratch/opus_w101_manifest.py']


def lean_paths(names):
    return sorted(p for p in names if p.endswith('.lean') and (p.split('/')[0] in ('Construction', 'Proof') or
                                                               p in ('Construction.lean', 'Proof.lean', 'Submission.lean')))


def digest(files):
    return hashlib.sha256(json.dumps(files, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def from_tree():
    names = [str(p.relative_to(ROOT)) for p in ROOT.rglob('*.lean') if '.lake' not in p.parts]
    paths = lean_paths(names) + EXTRA
    return {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in sorted(paths)}


def from_commit(commit):
    names = subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', commit], cwd=ROOT, text=True).split()
    paths = lean_paths(names) + EXTRA
    files = {}
    for p in sorted(paths):
        blob = subprocess.run(['git', 'show', f'{commit}:{p}'], cwd=ROOT, capture_output=True, check=True).stdout
        files[p] = hashlib.sha256(blob).hexdigest()
    return files


def main():
    mode = sys.argv[1]
    if mode == 'write':
        files = from_tree()
        OUT.parent.mkdir(parents=True, exist_ok=True)
        OUT.write_text(json.dumps(dict(sha256=digest(files), files=files), indent=2) + '\n')
        print(f'recorded {len(files)} files: {digest(files)}')
    elif mode == 'check':
        expected = json.loads(OUT.read_text())
        files = from_commit(sys.argv[2]) if len(sys.argv) > 2 else from_tree()
        assert files == expected['files'], sorted(set(files.items()) ^ set(expected['files'].items()))[:5]
        print(f'manifest matches {len(files)} files ({"commit " + sys.argv[2] if len(sys.argv) > 2 else "tree"}): '
              f'{digest(files)}')
    elif mode == 'deps':
        manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
        for pkg in manifest['packages']:
            path = ROOT / '.lake/packages' / pkg['name'].strip('«»')
            head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=path, text=True).strip()
            dirty = subprocess.check_output(['git', 'status', '--porcelain', '--untracked-files=no'], cwd=path, text=True)
            assert head == pkg['rev'], (pkg['name'], head, pkg['rev'])
            assert not dirty.strip(), (pkg['name'], dirty)
            print(f"{pkg['name']}: {head} clean")
        print(f"all {len(manifest['packages'])} dependencies at locked revisions with clean trees")
    else:
        raise SystemExit(__doc__)


if __name__ == '__main__':
    main()
