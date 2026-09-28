#!/usr/bin/env python3
"""Write or check the exact source manifest used by the combined whole-public/101-bit audits."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / 'evidence/packed-101/source-manifest.json'


def current():
    tracked = subprocess.check_output(['git', '-C', str(ROOT), 'ls-files', '--cached', '--others', '--exclude-standard'], text=True).splitlines()
    paths = {path for path in tracked if path.endswith('.lean')}
    paths.update(['lakefile.toml', 'lake-manifest.json', 'lean-toolchain',
                  'Scratch/CombinedAudit.lean', 'Scratch/P1Audit.lean', 'Scratch/P1SourceManifest.py', 'Scratch/check_combined.py',
                  'Scratch/check_width9.py', 'Scratch/opus_gen_budget.py',
                  'Scratch/source_manifest.py', 'Scratch/PackedSourceManifest.py', 'Scratch/check_packed.py', 'Scratch/Packed101SourceManifest.py', 'Scratch/check_packed101.py', 'Scratch/opus_next_ideas.py'])
    files = {path: hashlib.sha256((ROOT / path).read_bytes()).hexdigest() for path in sorted(paths)}
    digest = hashlib.sha256(json.dumps(files, sort_keys=True, separators=(',', ':')).encode()).hexdigest()
    return dict(sha256=digest, files=files)


def main():
    actual = current()
    if sys.argv[1:] == ['write']:
        OUTPUT.write_text(json.dumps(actual, indent=2)+'\n')
        print(f"Recorded {len(actual['files'])} source/configuration/audit files: {actual['sha256']}")
    elif sys.argv[1:] == ['check']:
        expected = json.loads(OUTPUT.read_text())
        assert actual == expected, 'the source differs from the audited manifest'
        head = subprocess.check_output(['git', '-C', str(ROOT), 'rev-parse', 'HEAD'], text=True).strip()
        print(f"Source manifest matches {len(actual['files'])} files: {actual['sha256']}")
        print(f'Current HEAD: {head}')
    else:
        raise SystemExit('usage: python3 -B Scratch/Packed101SourceManifest.py write|check')


if __name__ == '__main__':
    main()
