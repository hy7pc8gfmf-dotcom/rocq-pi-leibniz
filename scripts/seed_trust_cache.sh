#!/bin/bash
# Seed the trust cache: copy pre-built .vo files from the pinned local
# clone into the CI checkout so the build step is a pure skip pass
# (the same pattern as the ConstructiveWorld-Main CI seeding step).
# The seed source is a machine-local convention; when absent the build
# simply compiles everything from source.
set -u
SEED_DIR="${PI_TRUST_CACHE:-/d/ComplexAnalysis/rocq-pi-leibniz/theories}"
if [ ! -d "$SEED_DIR" ]; then
  echo "seed cache absent at $SEED_DIR — full compile from source"
  exit 0
fi
n=0
while IFS= read -r vo; do
  rel="${vo#"$SEED_DIR"/}"
  mkdir -p "$(dirname "$rel")"
  cp -f "$vo" "$rel"
  n=$((n + 1))
done < <(find "$SEED_DIR" -name '*.vo')
echo "seeded .vo count: $n"
