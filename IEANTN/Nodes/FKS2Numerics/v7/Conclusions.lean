/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Vocabulary.ErrorTerms
namespace FKS2Numerics.v7
open Real IEANTN
/-- Original QRH30-cell allowance, now consumed through the shared generic transport.

Spelled out: `Eπ(x) = |π(x) − Li(x)| / (x / log x) ≤ 5·10⁻¹⁶` for every real `x ≥ exp 330`.
Premises: the QRH-derived `ψ` bound `QRHCH2.v5.psi_refined_bound`, which gives the θ allowances
`Q(b) = b²/283 · e^(−b/8)`, and the anchor `FKS2.v6.table4_anchor_300`. The analytic transport
(30 unit cells in `log x` from 300 to 330, plus point and tail terms) reduces the claim to one
number, `B_safe(Q)`. The C program `Solutions/FKS2Numerics.v5/c/fks2_table4_transport.c` evaluates
that number, and the source-associated RN64 execution certifies `B_safe(Q) < 5·10⁻¹⁶`. Trust:
finite `native_decide` facts, which is not official three-axiom compliance. Walkthrough:
`docs/qrh/TABLE4_WALKTHROUGH.md`. -/
def qrh_pi : Prop := HasNumericalBound Eπ ((5:ℝ)/10^16) (exp 330)
end FKS2Numerics.v7
