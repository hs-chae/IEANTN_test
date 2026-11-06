#!/usr/bin/env bash
# MT7: compile the selected C programs under several compilers flags and compare the computed binary64 result.
# The Lean proofs never compile these files: they decode the literals and model the restricted C in Lean.
# Nothing in Lake, the local gate or a receipt records compiler or flags; this shows what that boundary leaves out.
set -u
N=/ryu/hyunsik/playground/independence/ieantn_qrh/agentB/network; E=$1
progs="Solutions/Table4Evolution.v1/c/qrh_trunc2.c:fks2_table4_transport Solutions/FKS2Numerics.v5/c/fks2_table4_transport.c:fks2_table4_transport Solutions/Table4Evolution.v1/c/power_network.c:fks2_power_transport pilots/agentB-calibration/c/calibration_new.c:calibration_deviation pilots/agentB-calibration/c/ramanujan_9401_new.c:ramanujan_epsilon_bound"
flagsets=("-O0" "-O2" "-O3 -march=native" "-O3 -ffast-math" "-O2 -mfpmath=387" "-O2 -mfpmath=387 -ffloat-store" "-O0 -fexcess-precision=fast -mfpmath=387")
echo "gcc: $(gcc --version | head -1)"
for pe in $progs; do p=${pe%%:*}; f=${pe##*:}; b=$(basename $p .c)
  printf '#include <stdio.h>\n#include <string.h>\ndouble %s(void);\nint main(void){ double r=%s(); unsigned long long u; memcpy(&u,&r,8); printf("%%.17g %%016llx\\n", r, u); return 0; }\n' "$f" "$f" > $E/build/drv_$b.c
  for fl in "${flagsets[@]}"; do
    out=$(gcc $fl -o $E/build/$b.bin $N/$p $E/build/drv_$b.c 2>&1 && $E/build/$b.bin)
    echo "$p [$fl] $out"
  done
done
