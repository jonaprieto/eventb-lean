#!/bin/bash
# Compile the obligations and count how many the tactic closed. A theorem that fails is
# reported by Lean as an error at its line, so the count of distinct failing theorem
# names is the miss count.
set -u
TAC="$1"; N="${2:-200}"
python3 spike/build.py "$TAC" "$N" 2>/tmp/spike-cov.txt
TOTAL=$(grep -c '^theorem' spike/Spike/Obligations.lean)
cd spike
lake env lean Spike/Obligations.lean > /tmp/spike-out.txt 2>&1
FAILED=$(grep -oE 'Obligations\.lean:[0-9]+' /tmp/spike-out.txt | sort -u | wc -l | tr -d ' ')
echo "tactic: $TAC"
echo "attempted: $TOTAL   failed: $FAILED   closed: $((TOTAL - FAILED))"
