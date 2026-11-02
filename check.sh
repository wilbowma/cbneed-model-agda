#!/bin/sh
# Typecheck the Agda files in this repository.  Agda's heap is capped
# (default 4G) and each file has a time limit, because normalizing proofs
# can otherwise exhaust memory.
#
#   ./check.sh                 check every file below
#   ./check.sh File.agda ...   check the given files
#   AGDA_MEM=8G ./check.sh     raise the heap cap

set -u
MEM=${AGDA_MEM:-4G}
LIMIT=${AGDA_TIMEOUT:-600}

if [ $# -eq 0 ]; then
  set -- Stratified.agda Promises.agda LambdaPR.agda LambdaPRTests.agda \
         LambdaPRAdequacy.agda
fi

status=0
for f in "$@"; do
  [ -f "$f" ] || { echo "skip $f (missing)"; continue; }
  printf '%s ... ' "$f"
  if out=$(timeout "$LIMIT" agda +RTS -M"$MEM" -RTS -l standard-library -i . "$f" 2>&1); then
    echo ok
  else
    echo FAILED
    echo "$out" | tail -20
    status=1
  fi
done
exit $status
