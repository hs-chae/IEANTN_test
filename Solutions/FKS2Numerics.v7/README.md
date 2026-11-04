# Solutions/FKS2Numerics.v7: map from statement to program

This directory proves the QRH Table 4 allowance and the `FKS2.v9` consumers. The mathematics is in
[docs/qrh/TABLE4_WALKTHROUGH.md](../../docs/qrh/TABLE4_WALKTHROUGH.md). This file only says where
each piece lives.

| You want | Look at |
|---|---|
| The public claim | `IEANTN/Nodes/FKS2Numerics/v7/Conclusions.lean`: `qrh_pi`, i.e. `Eπ(x) ≤ 5·10⁻¹⁶` for `x ≥ e^330` |
| The theorem that proves it | `FKS2PairQRH.lean`: `FKS2Numerics.v7.challenge_qrh_pi`, from `FKS2Pair.Updated.numerical_pi` |
| The analytic transport (frozen, shared with the old program) | `../FKS2Numerics.v6/FKS2Pair/GenericMath.lean`: `ValidProfile`, `Bsafe`, `whole_ray_transport` |
| The QRH profile | `../FKS2Numerics.v6/FKS2Pair/QRHGeometry.lean`: `qProfile j = Q(300+j)`, `qProfile_valid`, `qBsafe_eq` |
| The executed C and its certificate | `../FKS2Numerics.v5/c/fks2_table4_transport.c` and `../FKS2Numerics.v5/FKS2Table4/` (reused unchanged through `original_execution_at`) |
| The certified number | `FKS2PairQRH.lean`: `certified_allowance : Bsafe qProfile < 5/10^16` |
| `FKS2.v9` consumers | `FKS2PairConsumers.lean` |
| Everything assembled | `FKS2PairReplay.lean`: `FKS2Pair.assembled`, with 19 mathematical arguments |

Build: `lake update && lake build` in this directory
([REPRODUCING.md](../../docs/qrh/REPRODUCING.md) §2).

Trust:
- 8 finite `native_decide` facts;
- 13 CH2 premises and the `exp 300` anchor remain explicit;
- in the canonical build QRH is an argument of `FKS2Pair.assembled`, and the actual OpenAI proof
  is supplied only in the separate replay at Lean 4.34.1.
