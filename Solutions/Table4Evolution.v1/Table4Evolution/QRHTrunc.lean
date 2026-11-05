/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Agent B (Claude)
-/
import Table4Evolution.Profiles
import Table4Evolution.Data.QRHTrunc
import IEANTN.Nodes.FKS2Numerics.v7.Conclusions

/-!
# QRH input, evolved program: two cells instead of thirty

The partition is `[300, 329] ∪ [329, 330]`: one coarse cell carrying `Q(300)` over 29 units of
`log x`, then the last unit cell. The program sums 2 literals instead of 30, with the same frozen
`sum` and the same anchor/point/tail literals as `FKS2Numerics.v5`; its scale is `2^-55` so that
both cell literals lie in `sum`'s input range `[2^-40, 1]`. It proves the registered statement
`FKS2Numerics.v7.qrh_pi` (`Eπ ≤ 5·10⁻¹⁶` on `x ≥ e^330`) from the premises of its challenge.

The coarse cell costs accuracy, not validity: the program's allowance is `4.930·10⁻¹⁶` against
`4.715·10⁻¹⁶` for thirty cells; both are below the target. One native fact: `certificate`.
-/

namespace Table4Evolution.QRHTrunc

open Real IEANTN PVCore

def program : Program :=
  ⟨"fks2_table4_transport", literals, scaleLiteral,
    [(.plus, anchorLiteral), (.plus, pointLiteral), (.plus, tailLiteral)]⟩

def source : String := include_str ".." / "c" / "qrh_trunc2.c"

theorem certificate :
    upperCheck source program (1 / 10 ^ 30) (5 / 10 ^ 16) = true ∧
    cellsOK (1 / 8) 55 qrhM bs (valuesOf program).xs = true ∧
    (valuesOf program).scale = 1 / 2 ^ 55 ∧
    (valuesOf program).ops = [(.plus, anchorQ), (.plus, pointQ), (.plus, tailQ)] ∧
    constOK (1 / 8) (qrhM 300) (qrhM 330) anchorQ pointQ tailQ = true := by
  native_decide

/-- `FKS2Numerics.v7.qrh_pi` from the two-cell program, with the premises of its challenge. -/
theorem qrh_pi (hpsi : QRHCH2.v5.psi_refined_bound) (hAnchor : FKS2.v6.table4_anchor_300) :
    FKS2Numerics.v7.qrh_pi := by
  have h := pi_bound (rest := [329, 330]) (profile_qrh hpsi) hAnchor certificate.2.1 (by decide)
    certificate.2.2.2.2 (program_bound certificate.1 certificate.2.2.1 certificate.2.2.2.1)
  show HasNumericalBound Eπ ((5 : ℝ) / 10 ^ 16) (exp 330)
  norm_num at h ⊢
  exact h

end Table4Evolution.QRHTrunc
