#!/usr/bin/env bash
# preview.sh <solution-dir> <node-id> <theorem> <out-prefix>
# The NODES.md L323-340 local check (upstream 466b41b): challenge type vs solution type under pp.all, and axioms.
# Run twice for the solution side: (1) exactly as documented (`lake env lean`, `import Solution`), (2) with the
# project's own build directory pinned first on LEAN_PATH, because several path dependencies also root a module
# named `Solution`. This is a local preview, not a Comparator run and not a receipt.
set -u
DIR=$1; NODE=$2; NAME=$3; OUT=$4
S=/tmp/claude-1013/-ryu-hyunsik-playground-independence-alex/75718ac3-268c-412a-8046-11dd54eef723/scratchpad
cd "$DIR" || exit 2
printf 'import IEANTN.Nodes.%s.Challenge\nset_option pp.all true\n#check @%s\n' "$NODE" "$NAME" > $S/pv_ch.lean
printf 'import Solution\nset_option pp.all true\n#check @%s\n#print axioms %s\n' "$NAME" "$NAME" > $S/pv_so.lean
lake env lean $S/pv_ch.lean > $OUT.ch.out 2>&1
lake env lean $S/pv_so.lean > $OUT.so_documented.out 2>&1
LP=$(lake env printenv LEAN_PATH)
LEAN_PATH="$DIR/.lake/build/lib/lean:$LP" lean $S/pv_so.lean > $OUT.so_pinned.out 2>&1
for v in documented pinned; do
  if grep -v "depends on axioms" $OUT.so_$v.out | diff -q $OUT.ch.out - >/dev/null; then same=identical; else same=DIFFERENT; fi
  ax=$(grep -o "depends on axioms: \[.*\]" $OUT.so_$v.out | head -1)
  err=$(grep -m1 -o "error.*" $OUT.so_$v.out | cut -c1-120)
  echo "$NAME [$v]: type $same; ${ax:-no axiom line}; ${err:-no error}"
done
