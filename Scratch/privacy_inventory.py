"""List local CRT privacy targets independent of CRT simulator implementation.

Run from the repository root. Unknown/package imports are treated as leaves.
This checks import reachability, not whether a Lean theorem has compiled.
"""
from functools import lru_cache
from pathlib import Path
import re

root = Path(__file__).resolve().parents[1]
modules = {}
for top in ("Construction", "Proof", "Scratch"):
    for path in (root / top).rglob("*.lean"):
        name = ".".join(path.relative_to(root).with_suffix("").parts)
        modules[name] = re.findall(r"^import\s+(\S+)", path.read_text(), re.M)
for path in root.glob("*.lean"):
    modules[path.stem] = re.findall(r"^import\s+(\S+)", path.read_text(), re.M)


@lru_cache(None)
def simulator_path(module):
    # LawShape contains generic interface predicates, not the concrete CRT
    # implementation. Follow its imports instead of excluding its consumers.
    if module != "Proof.Simulator.CRT.LawShape" and module.startswith(
        ("Construction.Simulator.CRT", "Proof.Simulator.CRT")
    ):
        return (module,)
    for dependency in modules.get(module, []):
        path = simulator_path(dependency)
        if path:
            return (module,) + path
    return ()


privacy = sorted(m for m in modules if m.startswith("Proof.Privacy.CRT."))
independent = [m for m in privacy if not simulator_path(m)]
blocked = [m for m in privacy if simulator_path(m)]
imported = {d for m in independent for d in modules[m]}
targets = [m for m in independent if m not in imported]
print(f"Privacy CRT modules: {len(privacy)}")
print(f"Independent: {len(independent)}; simulator-dependent: {len(blocked)}")
for m in blocked:
    print(" -> ".join(simulator_path(m)))
print("Build targets:")
print(" ".join(targets))
(root / "Scratch/privacy_independent_targets.txt").write_text("\n".join(targets) + "\n")
