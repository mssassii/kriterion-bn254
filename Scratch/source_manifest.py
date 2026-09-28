#!/usr/bin/env python3
"""Write or check the exact source manifest used by the combined local audits."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / 'evidence/combined-width9-h1/source-manifest.json'


def current():
    tracked = subprocess.check_output(['git', '-C', str(ROOT), 'ls-files'], text=True).splitlines()
    paths = {path for path in tracked if path.endswith('.lean')}
    paths.update(['lakefile.toml', 'lake-manifest.json', 'lean-toolchain',
                  'Scratch/CombinedAudit.lean', 'Scratch/check_combined.py',
                  'Scratch/check_width9.py', 'Scratch/opus_gen_budget.py',
                  'Scratch/source_manifest.py'])
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
        raise SystemExit('usage: python3 -B Scratch/source_manifest.py write|check')


if __name__ == '__main__':
    main()
