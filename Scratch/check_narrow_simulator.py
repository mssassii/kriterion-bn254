#!/usr/bin/env python3
"""Build the simulator scope and audit it; run in a VM worktree with lake on PATH."""
from pathlib import Path
import re
import subprocess
import sys


def without_comments(text):
    out, depth, i = [], 0, 0
    while i < len(text):
        pair = text[i:i + 2]
        if pair == '/-':
            depth += 1
            i += 2
        elif depth and pair == '-/':
            depth -= 1
            i += 2
        elif not depth and pair == '--':
            end = text.find('\n', i)
            i = len(text) if end < 0 else end
        else:
            if not depth or text[i] == '\n':
                out.append(text[i])
            i += 1
    return ''.join(out)


files = list(Path('Construction').rglob('*.lean')) + list(Path('Proof').rglob('*.lean'))
graph = {}
for path in files:
    module = '.'.join(path.with_suffix('').parts)
    graph[module] = re.findall(r'^import\s+(\S+)', without_comments(path.read_text()), re.M)

scope = sorted('.'.join(path.with_suffix('').parts)
               for root in ('Construction/Simulator', 'Proof/Simulator')
               for path in Path(root).rglob('*.lean'))
known_failure = 'Proof.Privacy.CRT.Swap.Reading'


def depends_on_failure(module, visited=None):
    visited = set() if visited is None else visited
    if module == known_failure:
        return True
    if module in visited:
        return False
    visited.add(module)
    return any(depends_on_failure(dep, visited) for dep in graph.get(module, []))


blocked = [module for module in scope if depends_on_failure(module)]
unblocked = [module for module in scope if module not in blocked]
prefix = Path(sys.argv[1] if len(sys.argv) > 1 else '/tmp/narrow-simulator')
prefix.parent.mkdir(parents=True, exist_ok=True)
head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip()
manifest = f'HEAD {head}\nscope {len(scope)}\nunblocked {len(unblocked)}\nblocked {len(blocked)}\n'
manifest += '\n'.join(blocked) + '\n'
prefix.with_suffix('.manifest').write_text(manifest)
print(manifest, flush=True)

checks = [('all', ['lake', 'build', *scope]),
          ('unblocked', ['lake', 'build', *unblocked]),
          ('audit', ['lake', 'env', 'lean', 'Scratch/NarrowSimulatorAudit.lean']),
          ('sampler-audit', ['lake', 'env', 'lean', 'Scratch/NarrowStage1Exact.lean'])]
for suffix, command in checks:
    log = Path(f'{prefix}-{suffix}.log')
    print(f'START {suffix}: {log}', flush=True)
    with log.open('w') as output:
        result = subprocess.run(command, stdout=output, stderr=subprocess.STDOUT)
    print(f'END {suffix}: status={result.returncode} log={log}', flush=True)
    lines = log.read_text().splitlines()
    for line in lines:
        if line.startswith('error:'):
            print(line, flush=True)
    print('\n'.join(lines[-3:]), flush=True)
