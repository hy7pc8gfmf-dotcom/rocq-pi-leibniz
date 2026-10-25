#!/bin/bash
# Incremental build with the vo-newer-than-v skip rule (a seeded trust
# cache makes every entry a SKIP; a clean checkout compiles everything).
# Toolchain-critical binaries are asserted on PATH up front; file
# enumeration uses bash globs (the Windows system32 find.exe, which may
# precede Git's find on a runner PATH, has incompatible syntax and
# fails silently.
set -u
cd "$(dirname "$0")/.." || exit 9
export PATH="/c/Rocq-Platform~9.1~2026.01/bin:/c/Program Files/Python313:$PATH"
command -v coqdep >/dev/null || { echo NO-COQDEP; exit 7; }
command -v coqc >/dev/null || { echo NO-COQC; exit 7; }
command -v python >/dev/null || { echo NO-PYTHON; exit 7; }

FILES=$(ls theories/*.v theories/Reals/Cauchy/*.v 2>/dev/null | sed 's|^\./||')
NFILES=$(printf '%s\n' $FILES | wc -l)
echo "enumerated .v count: $NFILES"

ORDER=$(coqdep -Q theories pi_leibniz -Q theories/Reals/Cauchy "" $FILES 2>/dev/null | python -c '
import sys
from collections import defaultdict
def to_v(x):
    x = x.strip()
    return x[:-3] + ".v" if x.endswith(".vo") else None
nodes, edges = set(), defaultdict(set)
for line in sys.stdin.read().splitlines():
    if ":" not in line:
        continue
    tgt, deps = line.split(":", 1)
    parts = tgt.split()
    if not parts:
        continue
    t = to_v(parts[0])
    if not t:
        continue
    nodes.add(t)
    for d in deps.split():
        if d.endswith(".vo") and ":/" not in d and "Rocq" not in d:
            dv = to_v(d)
            if dv and dv != t:
                edges[dv].add(t)
                nodes.add(dv)
indeg = {n: 0 for n in nodes}
for ts in edges.values():
    for t in ts:
        indeg[t] += 1
q = sorted(n for n in nodes if indeg[n] == 0)
out = []
while q:
    n = q.pop(0)
    out.append(n)
    for t in sorted(edges.get(n, ())):
        indeg[t] -= 1
        if indeg[t] == 0:
            q.append(t)
if len(out) != len(nodes):
    sys.exit(3)
sys.stdout.write("\n".join(out) + "\n")
' | tr -d '\r')
NORDER=$(printf '%s\n' "$ORDER" | grep -c .)
echo "coqdep order entries: $NORDER (expect $NFILES)"
[ "$NORDER" -eq "$NFILES" ] || { echo ORDER-INCOMPLETE; exit 6; }

fail=0
while IFS= read -r f; do
  [ -z "$f" ] && continue
  case "$f" in *.v) ;; *) echo "BAD-ARG=[$f]"; exit 5 ;; esac
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
done <<EOF
$ORDER
EOF
built=$(ls theories/*.vo theories/Reals/Cauchy/*.vo 2>/dev/null | wc -l)
srcs=$(ls theories/*.v theories/Reals/Cauchy/*.v 2>/dev/null | wc -l)
echo "compiled .vo: ${built} / registered .v: ${srcs}"
[ "$fail" -eq 0 ] && [ "$built" -eq "$srcs" ]
