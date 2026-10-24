#!/bin/bash
# Incremental build in coqdep topological order with the vo-newer-than-v
# skip rule (a seeded trust cache makes every line a SKIP; a clean
# checkout compiles everything).  Mirrors vo/build.sh of the hosting
# campaign: fail-loud on the first red, log to stdout.
set -u
cd "$(dirname "$0")/.." || exit 9
export PATH="/c/Rocq-Platform~9.1~2026.01/bin:/c/Program Files/Python313:$PATH"
command -v coqdep >/dev/null || { echo NO-COQDEP; exit 7; }
command -v coqc >/dev/null || { echo NO-COQC; exit 7; }
command -v python >/dev/null || { echo NO-PYTHON; exit 7; }
FILES=$(find theories -name '*.v' | sed 's|^\./||')
ORDER=$(coqdep -Q theories pi_leibniz -Q theories/Reals/Cauchy "" $FILES 2>/dev/null | python - "$FILES" <<'PYEOF'
import sys
from collections import defaultdict
edges = defaultdict(set); nodes = set()
def norm(x):
    x = x.strip().rstrip(":")
    if x.endswith((".vo", ".vos", ".vok", ".glob")):
        x = x[: x.rfind(".")] + ".v"
    return x.replace("\\", "/")
for line in sys.stdin.read().splitlines():
    if ":" not in line: continue
    tgt, deps = line.split(":", 1)
    t = norm(tgt)
    if not t.endswith(".v"): continue
    nodes.add(t)
    for d in (norm(x) for x in deps.split()):
        if d.endswith(".v") and d != t and ("Cauchy/" in d or d == "PiLeibniz.v"):
            edges[d].add(t); nodes.add(d)
indeg = {n: 0 for n in nodes}
for ts in edges.values():
    for t in ts: indeg[t] += 1
q = sorted(n for n in nodes if indeg[n] == 0); out = []
while q:
    n = q.pop(0); out.append(n)
    for t in sorted(edges.get(n, ())):
        indeg[t] -= 1
        if indeg[t] == 0: q.append(t)
if len(out) != len(nodes): sys.exit(3)
print("\n".join(out))
PYEOF
) || { echo "coqdep order failed"; exit 8; }
fail=0
while IFS= read -r f; do
  [ -z "$f" ] && continue
  v="${f%.v}.vo"
  if [ -f "$v" ] && [ "$v" -nt "$f" ]; then
    echo "SKIP $f"
    continue
  fi
  echo "COMPILING $f"
  if ! coqc -q -Q theories pi_leibniz -Q theories/Reals/Cauchy "" "$f"; then
    echo "RED $f"
    fail=1
    break
  fi
done <<< "$ORDER"
built=$(find theories -name '*.vo' | wc -l)
srcs=$(find theories -name '*.v' | wc -l)
echo "compiled .vo: ${built} / registered .v: ${srcs}"
[ "$fail" -eq 0 ] && [ "$built" -eq "$srcs" ]
