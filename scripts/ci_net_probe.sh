#!/bin/bash
# Pre-checkout network window probe for the self-hosted CI runner.
# Sparse github.com:443 blocking windows kill the checkout fetch before
# any later step can react; this probe holds the job until the window
# opens (or a cap is reached).  Read-only and idempotent: one log line
# per probe attempt, a 20s hard timeout per probe, and an always-exit-0
# policy so checkout's own retries still run and keep the full log.
# Grep anchors for the external watchdog:
#   NET-PROBE GREEN attempts=N red=M elapsed=Xs
#   NET-PROBE CAP-REACHED attempts=N red=M elapsed=Xs - releasing to checkout
set -u

REPO_URL="${CI_NET_PROBE_URL:-https://github.com/${GITHUB_REPOSITORY:-hy7pc8gfmf-dotcom/rocq-pi-leibniz}.git}"
INTERVAL="${CI_NET_PROBE_INTERVAL:-60}"
CAP="${CI_NET_PROBE_CAP:-600}"
HOSTS="${CI_NET_PROBE_HOSTS:-/c/Windows/System32/drivers/etc/hosts}"

echo "NET-PROBE start url=$REPO_URL interval=${INTERVAL}s cap=${CAP}s"
hg="$(grep -i 'github\.com' "$HOSTS" 2>/dev/null | tr -s ' \t' ' ' | paste -sd ';' -)"
echo "NET-PROBE hosts-github-now: ${hg:-<no github lines>}"

attempt=0
red=0
start=$(date +%s)
deadline=$((start + CAP))
while :; do
  attempt=$((attempt + 1))
  now=$(date +%s)
  timeout 20 git ls-remote "$REPO_URL" HEAD >/dev/null 2>&1
  rc=$?
  if [ "$rc" -eq 0 ]; then
    echo "NET-PROBE GREEN attempts=$attempt red=$red elapsed=$((now - start))s"
    exit 0
  fi
  red=$((red + 1))
  code="$(curl -s -o /dev/null -w '%{http_code}' --connect-timeout 10 https://github.com/ 2>/dev/null)"
  crc=$?
  echo "NET-PROBE attempt=$attempt red ls_remote_rc=$rc curl_rc=$crc curl_code=$code at $(date -u +%H:%M:%SZ)"
  if [ "$now" -ge "$deadline" ]; then
    echo "NET-PROBE CAP-REACHED attempts=$attempt red=$red elapsed=$((now - start))s - releasing to checkout (its retries own the full log)"
    exit 0
  fi
  sleep "$INTERVAL"
done
