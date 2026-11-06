#!/usr/bin/env bash
# Remedy R2 test (configuration only): declare program A's and B''s C files as Lake input files of the pv-replay
# library, then repeat mutation MT10b (one literal digit of ramanujan_9401_new.c) in world A and observe whether the
# stale certificate is now caught. Everything is restored at the end and the tree is verified clean.
set -u
B=/ryu/hyunsik/playground/independence/ieantn_qrh/agentB; D=$B/pv8_study; W=$B/pv8_wtA; G=$D/scripts/guarded_build.sh
E=$D/evidence/remedy/R2_run; mkdir -p $E
SOL=$W/Solutions/PVMatchRamA.v1; LF=$W/pilots/pv-replay/lakefile.toml; C=$W/pilots/agentB-calibration/c/ramanujan_9401_new.c
cd $W; [ -z "$(git status --porcelain --untracked-files=no)" ] || { echo "tree not clean"; exit 1; }
sha_c0=$(sha256sum $C | cut -d' ' -f1); sha_l0=$(sha256sum $LF | cut -d' ' -f1)
python3 - "$LF" <<'PY'
import sys
p=sys.argv[1]; s=open(p).read()
add='''
[[input_file]]
name = "calibration_new_c"
path = "../agentB-calibration/c/calibration_new.c"
text = true

[[input_file]]
name = "ramanujan_9401_new_c"
path = "../agentB-calibration/c/ramanujan_9401_new.c"
text = true
'''
# The same pattern Table4Evolution.v1 uses (proven by MT1-MT3): a library whose roots include the module that
# reads the files, with `needs` on the input files. PVReplay.Chain holds both include_str of programs A and B'.
lib = '[[lean_lib]]\nname = "PVReplayChainSources"\nroots = ["PVReplay.Chain"]\nneeds = ["calibration_new_c", "ramanujan_9401_new_c"]\n'
s = s.rstrip("\n") + "\n" + add + "\n" + lib
open(p,"w").write(s)
PY
git diff $LF > $E/lakefile.diff
echo "step 1: declared, build"; $G $E/1_declared.log $SOL lake build | sed 's/ dir=.*//'; grep -c Built $E/1_declared.log
echo "step 2: declared + literal edit, build (MT10b repeated)"
python3 - "$C" <<'PY'
import sys
p=sys.argv[1]; s=open(p).read(); a="0.058638378906250003541611448554249363951385021209716796875"
assert s.count(a)==1; open(p,"w").write(s.replace(a,a[:-1]+"6"))
PY
$G $E/2_declared_literal.log $SOL lake build | sed 's/ dir=.*//'; grep -c Built $E/2_declared_literal.log; grep -m3 "error" $E/2_declared_literal.log | cut -c1-200
git checkout -- $C; [ "$(sha256sum $C | cut -d' ' -f1)" = "$sha_c0" ] && echo "C restored"
echo "step 3: declared, restored source, build"; $G $E/3_declared_restored.log $SOL lake build | sed 's/ dir=.*//'; grep -c Built $E/3_declared_restored.log
git checkout -- $LF; [ "$(sha256sum $LF | cut -d' ' -f1)" = "$sha_l0" ] && echo "lakefile restored"
echo "step 4: undeclared again, build"; $G $E/4_undeclared.log $SOL lake build | sed 's/ dir=.*//'; grep -c Built $E/4_undeclared.log
echo "tree: $(git status --porcelain --untracked-files=no | wc -l) changed tracked files"
