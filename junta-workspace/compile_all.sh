#!/bin/bash
# Compile each agent_NNN.lean against the pinned Lean/Mathlib checkout.
# Statement-only files (`:= by sorry`) — PASS = elaborates & type-checks
# (a `sorry` warning is expected and does NOT count as failure).
#
# This box has 8 GB RAM / 4 CPUs and every file does `import Mathlib`, so a
# single elaboration peaks ~4-5 GB: run STRICTLY SERIAL. Resumable — rows
# already in results.csv are skipped, so it can be re-launched after a kill.
set -u
export PATH="$HOME/.elan/bin:$PATH"
PROJ=/Users/hye-ryeonlee/prove2me_workspace
SRC=/Users/hye-ryeonlee/agent-formalization-thunderdome/junta-workspace/formalizations
OUT=/Users/hye-ryeonlee/agent-formalization-thunderdome/junta-workspace/compile
CAP=${CAP:-900}   # per-file wall-clock cap (seconds)
mkdir -p "$OUT/logs"
RESULTS="$OUT/results.csv"
[ -f "$RESULTS" ] || echo "agent,status,detail" > "$RESULTS"

compile_one() {
  local f="$1"
  local base; base=$(basename "$f" .lean)
  # resume: skip if already recorded with a terminal status
  if grep -q "^$base,\(PASS\|FAIL\)," "$RESULTS"; then
    echo "[skip] $base (already $(grep -m1 "^$base," "$RESULTS" | cut -d, -f2))"
    return
  fi
  # drop any stale (e.g. TIMEOUT) row for this agent
  grep -v "^$base," "$RESULTS" > "$RESULTS.tmp" && mv "$RESULTS.tmp" "$RESULTS"
  local log="$OUT/logs/$base.log"
  cd "$PROJ" || exit 1
  perl -e 'alarm shift; exec @ARGV or exit 127' "$CAP" lake env lean "$f" > "$log" 2>&1
  local rc=$?
  local status detail
  if [ $rc -eq 142 ] || [ $rc -eq 14 ]; then
    status=TIMEOUT; detail="exceeded ${CAP}s"
  elif [ $rc -ne 0 ]; then
    status=FAIL
    detail=$(grep -m1 -E 'error:' "$log" | tr ',;' '  ' | cut -c1-180)
    [ -z "$detail" ] && detail="exit $rc"
  else
    status=PASS
    if grep -q "declaration uses 'sorry'" "$log"; then detail="sorry (expected)"; else detail="clean"; fi
  fi
  echo "$base,$status,$detail" >> "$RESULTS"
  echo "[$status] $base  ($detail)"
}

for f in "$SRC"/agent_*.lean; do
  compile_one "$f"
done

echo "=== SUMMARY ==="
tail -n +2 "$RESULTS" | cut -d, -f2 | sort | uniq -c
