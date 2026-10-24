#!/bin/bash
# Certification: coqchk over the whole dependency closure (all-none
# assumption summary) plus the assumption smoke check on the two main
# theorems.  The package's green criterion, one guard-wrapped invocation.
set -uo pipefail
cd "$(dirname "$0")/.." || exit 9
export PATH="/c/Rocq-Platform~9.1~2026.01/bin:/c/Program Files/Python313:$PATH"
command -v rocqchk >/dev/null || { echo NO-ROCQCHK; exit 7; }
command -v rocq >/dev/null || { echo NO-ROCQ; exit 7; }
mods=$(find theories/Reals/Cauchy -name '*.vo' | sed -e 's|.*/||' -e 's|\.vo$||' | sort)
mods="$mods pi_leibniz.PiLeibniz"
echo "coqchk modules: $(echo "$mods" | wc -l)"
rocqchk -o -Q theories pi_leibniz -Q theories/Reals/Cauchy "" $mods 2>&1 | tee coqchk.log
grep -q "Modules were successfully checked" coqchk.log || { echo "COQCHK-FAIL"; exit 1; }
dirty=$(grep "Axioms:" coqchk.log | grep -vc "<none>" || true)
echo "non-none Axioms sections: ${dirty}"
[ "${dirty}" -eq 0 ] || { echo "AXIOMS-DIRTY"; exit 1; }
cat > piu_smoke_tmp.v <<'EOF'
From Stdlib Require Import QArith.QArith.
From pi_leibniz Require Import PiLeibniz.
Print Assumptions pi_leibniz_strong_irrational.
Print Assumptions pi_leibniz_appart_all_Q.
EOF
rocq c -q -Q theories pi_leibniz -Q theories/Reals/Cauchy "" piu_smoke_tmp.v 2>&1 | tee smoke.log
n=$(grep -c "Closed under the global context" smoke.log || true)
echo "assumption-closed count: ${n} (expect 2)"
rm -f piu_smoke_tmp.v
[ "${n}" -eq 2 ] || { echo "SMOKE-FAIL"; exit 1; }
echo "COQCHK_ALL_PASS"
