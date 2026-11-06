#!/usr/bin/env bash
# Second build round of the matched experiments, strictly one Lean build at a time.
# World A: core (+M2/M3 layout-A nodes), fingerprints, then the M2-A and M3-A solutions, cold then warm.
# World B: core (+M2 layout-B nodes), fingerprints, then M2-B provider and consumer, and the existing
#          M3-B projects (DudekPlattNumerics.v5 provider, RamanujanGap.v3 consumer), cold then warm.
set -u
B=/ryu/hyunsik/playground/independence/ieantn_qrh/agentB; D=$B/pv8_study; L=$D/evidence/builds; G=$D/scripts/guarded_build.sh; P=$B/tools/bin/python
$G $L/core_R2_A.log $B/pv8_wtA lake build
(cd $B/pv8_wtA && $P scripts/ieantn.py fingerprint > $L/fp_R2_A.log 2>&1; echo "fingerprint A rc=$?" >> $L/fp_R2_A.log)
for s in PVMatchRamA.v1 PVMatchShrR.v1 PVMatchShrD.v1; do
  $G $L/sol_${s}_cold.log $B/pv8_wtA/Solutions/$s lake build
  $G $L/sol_${s}_warm.log $B/pv8_wtA/Solutions/$s lake build
done
$G $L/core_R2_B.log $B/pv8_wtB lake build
(cd $B/pv8_wtB && $P scripts/ieantn.py fingerprint > $L/fp_R2_B.log 2>&1; echo "fingerprint B rc=$?" >> $L/fp_R2_B.log)
for s in PVMatchRamP.v1 PVMatchRamC.v1 DudekPlattNumerics.v5 RamanujanGap.v3; do
  $G $L/sol_B_${s}_cold.log $B/pv8_wtB/Solutions/$s lake build
  $G $L/sol_B_${s}_warm.log $B/pv8_wtB/Solutions/$s lake build
done
echo ROUND2_DONE
