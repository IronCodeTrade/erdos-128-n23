#!/bin/bash
# Exhaustive search for Erdős #128 counterexamples among maximal triangle-free graphs.
# Usage: ./run.sh N [PARTS]   (default PARTS=1). Needs ./triangleramsey (see README) and ./c128.
set -e
N=$1; P=${2:-1}
TH=$(( N*N/50 ))          # exact minimisation is run whenever the heuristic value is >= TH
gcc -O3 -march=native -o c128 c128.c
for r in $(seq 0 $((P-1))); do
  if [ "$P" -gt 1 ]; then ARGS="$N mod $r $P"; else ARGS="$N"; fi
  ( ./triangleramsey $ARGS 2>/dev/null | ./c128 $TH > res${N}_$r.txt ) &
done
wait
cat res${N}_*.txt
