#!/usr/bin/env bash
# Rebuild world A after fixing PVMatchShrD.v1 (its bridge also needs DudekPlatt.v3.criterion), then record fingerprints.
set -u
B=/ryu/hyunsik/playground/independence/ieantn_qrh/agentB; D=$B/pv8_study; L=$D/evidence/builds; G=$D/scripts/guarded_build.sh; P=$B/tools/bin/python
$G $L/core_R2b_A.log $B/pv8_wtA lake build
(cd $B/pv8_wtA && $P scripts/ieantn.py fingerprint > $L/fp_R2b_A.log 2>&1; echo "fingerprint A rc=$?" >> $L/fp_R2b_A.log)
$G $L/sol_PVMatchShrD.v1_fixed_cold.log $B/pv8_wtA/Solutions/PVMatchShrD.v1 lake build
$G $L/sol_PVMatchShrD.v1_fixed_warm.log $B/pv8_wtA/Solutions/PVMatchShrD.v1 lake build
echo ROUND2B_DONE
