#!/bin/bash
# Seed the trust cache: copy pre-built .vo files from the pinned local
# clone into the CI checkout so the build step is a pure skip pass.
# The seed source is a machine-local convention; when absent the build
# simply compiles everything from source.
set -u
# Form-A (Rocq 9.3 wave 20261102): toolchain bin injectable via PI_ROCQ_BIN;
# default stays the 9.1 platform path (byte-equivalent when unset).
export PATH="${PI_ROCQ_BIN:-/c/Rocq-Platform~9.1~2026.01/bin}:/c/Program Files/Python313:$PATH"
SEED_DIR="${PI_TRUST_CACHE:-/d/ComplexAnalysis/rocq-pi-leibniz/theories}"
if [ ! -d "$SEED_DIR" ]; then
  echo "seed cache absent at $SEED_DIR — full compile from source"
  exit 0
fi
# Era guard: a seeded .vo must carry the SAME .vo generation as the running
# toolchain.  Derive the expected magic by compiling a minimal probe with the
# current coqc (works for any toolchain generation, no version table needed).
# On mismatch (e.g. 9.1-era seed against a 9.3 toolchain) skip seeding so the
# build compiles from source instead of SKIP-loading cross-generation .vo
# (bad-version rejection would kill coqchk downstream).
if ! command -v coqc >/dev/null 2>&1; then
  echo "SEED-ERA-GUARD: coqc not on PATH — skipping seed (full compile from source)"
  exit 0
fi
tmpd=$(mktemp -d) || exit 0
printf 'Definition pi_seed_probe := 1.\n' > "$tmpd/probe.v"
if ( cd "$tmpd" && coqc -q probe.v >/dev/null 2>&1 ) && [ -f "$tmpd/probe.vo" ]; then
  want=$(od -An -tx1 -N8 "$tmpd/probe.vo" | tr -d ' \n')
  first_vo=$(find "$SEED_DIR" -name '*.vo' 2>/dev/null | head -1)
  got=$(od -An -tx1 -N8 "$first_vo" 2>/dev/null | tr -d ' \n')
  if [ -z "$got" ] || [ "$got" != "$want" ]; then
    echo "SEED-ERA-GUARD: seed magic [$got] != toolchain magic [$want] — skipping seed (full compile from source)"
    rm -rf "$tmpd"
    exit 0
  fi
  echo "SEED-ERA-OK: seed magic matches toolchain ($want)"
else
  echo "SEED-ERA-GUARD: probe compile failed — skipping seed (full compile from source)"
  rm -rf "$tmpd"
  exit 0
fi
rm -rf "$tmpd"
n=0
while IFS= read -r vo; do
  rel="${vo#"$SEED_DIR"/}"
  mkdir -p "$(dirname "$rel")"
  cp -f "$vo" "$rel"
  n=$((n + 1))
done < <(find "$SEED_DIR" -name '*.vo')
echo "seeded .vo count: $n"
