#!/usr/bin/env bash
# Run the mutation matrix sequentially: each mutation in world A, then in world B, one build at a time.
# Each run edits one file, builds, queries drift, restores the exact bytes, verifies, and rebuilds (mutate.py).
set -u
B=/ryu/hyunsik/playground/independence/ieantn_qrh/agentB; D=$B/pv8_study; P=$B/tools/bin/python; M=$D/evidence/mutation_specs
for id in "$@"; do
  for w in A B; do
    spec=$M/${id}_$w.json; [ -f $spec ] || { echo "skip $id $w (no spec)"; continue; }
    echo "=== $(date -u +%T) $id world $w"
    $P $D/scripts/mutate.py $B/pv8_wt$w ${id}_$w $spec 2>&1 | tail -3
  done
done
echo MUTATIONS_DONE
