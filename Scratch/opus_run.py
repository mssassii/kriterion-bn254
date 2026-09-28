#!/usr/bin/env python3
"""Run one command in the repository root, tee its combined output to evidence/<name>.log, and record the exit
status, timing and HEAD in evidence/<name>.status.json.  Usage: python3 Scratch/opus_run.py <name> <command...>"""
import json
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def main():
    name, command = sys.argv[1], sys.argv[2:]
    out = ROOT / 'evidence'
    out.mkdir(exist_ok=True)
    log = out / f'{name}.log'
    head = subprocess.run(['git', 'rev-parse', 'HEAD'], cwd=ROOT, capture_output=True, text=True).stdout.strip()
    dirty = subprocess.run(['git', 'status', '--porcelain', '--untracked-files=no'], cwd=ROOT, capture_output=True,
                           text=True).stdout
    start = time.time()
    with log.open('w') as handle:
        handle.write(f'$ {" ".join(command)}\n# HEAD {head}\n# tracked changes:\n{dirty}\n')
        handle.flush()
        process = subprocess.Popen(command, cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        for line in process.stdout:
            handle.write(line)
            handle.flush()
        code = process.wait()
    status = dict(command=command, head=head, tracked_changes=dirty.splitlines(), exit=code,
                  seconds=round(time.time() - start, 1), log=str(log.relative_to(ROOT)))
    (out / f'{name}.status.json').write_text(json.dumps(status, indent=2) + '\n')
    print(json.dumps(status))
    sys.exit(code)


if __name__ == '__main__':
    main()
