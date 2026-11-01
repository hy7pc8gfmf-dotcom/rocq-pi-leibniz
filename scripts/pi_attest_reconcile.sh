#!/bin/bash
# pi_attest_reconcile.sh — content-addressed attestation reconcile
# (KB95 W3, v1 REPORT-ONLY, 2026-11-01).
#
# Reconciles the checked-out tree against the minted attestation archive
# scripts/coqchk_attestation.json (cw.attest/v1), one line per module:
#   * archive key = repo-relative source path ("theories/PiLeibniz.v",
#     "theories/Reals/Cauchy/<stem>.v");
#   * verdict hash = sha256 of the SOURCE bytes after CRLF normalization
#     (tr -d '\r' | sha256sum) — line-ending churn (core.autocrlf) can
#     never fake a DIRTY face;
#   * CLEAN (hash match) = certification inherited from the minting green
#     run (printed as inherited=N);
#   * DIRTY / MISSING (in archive) and ADDED (on disk, not in archive)
#     are reported only.
#
# v1 report-only semantics: EVERY outcome exits 0 and nothing is handed
# to the certification step — the coqchk step after this one still
# verifies the FULL closure (sent_to_chk=0; the skip-list mechanic is
# v2, deferred until the archive has two stable generations).  vo
# hashes/sizes carried in the archive are informational only and never
# enter the verdict.  Self-contained bash: no python/jq, coreutils only.
set -uo pipefail
export LC_ALL=C

ROOT="$(cd "$(dirname "$0")/.." && pwd)" || { echo "ATT-RECON-FATAL: cannot locate repo root"; exit 9; }
cd "$ROOT" || { echo "ATT-RECON-FATAL: cannot cd to repo root"; exit 9; }

ARCHIVE="scripts/coqchk_attestation.json"
REPORT="scripts/attest_report.json"
now=$(date -u +%Y-%m-%dT%H:%M:%SZ)
head=$(git rev-parse HEAD 2>/dev/null || echo "unknown")

mkarr() { # $@ = strings -> JSON array literal on stdout
  local out="[" first=1 x
  for x in "$@"; do
    if [ $first -eq 1 ]; then first=0; else out+=","; fi
    out+="\"$x\""
  done
  printf '%s]' "$out"
}

write_report() { # $1 = archive_present(0/1)
  {
    printf '{\n'
    printf '  "schema": "cw.recon/v1",\n'
    printf '  "mode": "report-only",\n'
    printf '  "generated_at": "%s",\n' "$now"
    printf '  "head": "%s",\n' "$head"
    printf '  "archive": "%s",\n' "$ARCHIVE"
    printf '  "archive_present": %s,\n' "$([ "$1" -eq 0 ] && echo true || echo false)"
    printf '  "hash_rule": "sha256 of CRLF-normalized source bytes (strip CR, then hash); CLEAN judged on src hash only",\n'
    printf '  "archive_modules": %d,\n' "$n_arch"
    printf '  "inherited": %d,\n' "$n_clean"
    printf '  "dirty": %s,\n' "$(mkarr ${dirty_list[@]+"${dirty_list[@]}"})"
    printf '  "missing": %s,\n' "$(mkarr ${missing_list[@]+"${missing_list[@]}"})"
    printf '  "added": %s,\n' "$(mkarr ${added_list[@]+"${added_list[@]}"})"
    printf '  "sent_to_chk": 0\n'
    printf '}\n'
  } > "$REPORT"
}

n_arch=0; n_clean=0
dirty_list=(); missing_list=(); added_list=()

if [ ! -f "$ARCHIVE" ]; then
  write_report 1
  echo "ATT-RECON-NOARCHIVE: $ARCHIVE absent — nothing to inherit (report written to $REPORT; v1 report-only, exit 0; coqchk below still runs the full closure)"
  exit 0
fi

echo "content-addressed attestation reconcile (v1 report-only) — archive: $ARCHIVE"
echo "hash rule: strip CR (tr -d '\\r'), then sha256 the source bytes"

while IFS= read -r line; do
  key=$(printf '%s\n' "$line" | sed -n 's/^ *"\([^"]*\.v\)": .*/\1/p')
  want=$(printf '%s\n' "$line" | sed -n 's/.*"src_sha256": "\([0-9a-f]\{64\}\)".*/\1/p')
  [ -n "$key" ] && [ -n "$want" ] || continue
  n_arch=$((n_arch + 1))
  if [ ! -f "$key" ]; then
    missing_list+=("$key")
    printf '  %-8s %s (in archive, not on disk)\n' "MISSING" "$key"
    continue
  fi
  got=$(tr -d '\r' < "$key" | sha256sum | cut -d' ' -f1)
  if [ "$got" = "$want" ]; then
    n_clean=$((n_clean + 1))
    printf '  %-8s %s\n' "CLEAN" "$key"
  else
    dirty_list+=("$key")
    printf '  %-8s %s (archive %s... vs tree %s...)\n' "DIRTY" "$key" "${want:0:12}" "${got:0:12}"
  fi
done < <(grep '"src_sha256"' "$ARCHIVE")

for f in $(ls theories/*.v theories/Reals/Cauchy/*.v 2>/dev/null | sort); do
  grep -qF "\"$f\": {" "$ARCHIVE" || { added_list+=("$f"); printf '  %-8s %s (on disk, not in archive)\n' "ADDED" "$f"; }
done

write_report 0

echo "reconcile summary: archive_modules=$n_arch inherited(CLEAN)=$n_clean dirty=${#dirty_list[@]} missing=${#missing_list[@]} added=${#added_list[@]}"
echo "diff report written to: $REPORT (local dry-run artifact, not committed)"
echo "ATT-RECON-OK inherited=$n_clean sent_to_chk=0 (v1 report-only: any divergence above is reported, never gating; the coqchk step below still runs the FULL closure)"
exit 0
