/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Agent B (Claude)
-/
import Table4Evolution.Profiles
import Table4Evolution.Data.QRHQuarter

/-!
# QRH input, refined program: 120 quarter cells

The other end of the accuracy/work trade-off. QRH's profile `Q(L) = L²/283·e^{-L/8}` is defined for
every real `L`, so cells can be refined anywhere; a step profile gains nothing from cells finer than
its steps. Here `[300, 330]` is cut into 120 cells of width `1/4`. The program needs more than the
64 entries of one `sum` call, so it is a `PVCore.ChunkedProgram` (chunks of 64 and 56).

Result: `Eπ ≤ 4.7146·10⁻¹⁶` on `x ≥ e^330`, against the thirty unit cells' `4.7155·10⁻¹⁶`. Four
times the work buys 0.02%: the point term `Q(330) = 4.684·10⁻¹⁶` is 99.3% of the allowance and no
partition of `[300, 330]` changes it. One native fact: `certificate`.
-/

namespace Table4Evolution.QRHQuarter

open Real IEANTN PVCore

def program : ChunkedProgram :=
  ⟨"fks2_table4_transport", [literals.take 64, literals.drop 64], scaleLiteral,
    [(.plus, anchorLiteral), (.plus, pointLiteral), (.plus, tailLiteral)]⟩

def source : String := include_str ".." / "c" / "qrh_quarter120.c"

theorem certificate :
    upperCheckChunked source program (1 / 10 ^ 30) (47146 / 10 ^ 20) = true ∧
    cellsOK (1 / 8) 61 qrhM bs ((chunkedValuesOf program).pairs.map Prod.fst).flatten = true ∧
    (chunkedValuesOf program).scale = 1 / 2 ^ 61 ∧
    (chunkedValuesOf program).ops = [(.plus, anchorQ), (.plus, pointQ), (.plus, tailQ)] ∧
    constOK (1 / 8) (qrhM 300) (qrhM 330) anchorQ pointQ tailQ = true := by
  native_decide

/-- **Refined transport.** Under the premises of `FKS2Numerics.v7.qrh_pi`, `Eπ ≤ 4.7146·10⁻¹⁶` on
`x ≥ e^330`. -/
theorem qrh_pi_refined (hpsi : QRHCH2.v5.psi_refined_bound) (hAnchor : FKS2.v6.table4_anchor_300) :
    HasNumericalBound Eπ (47146 / 10 ^ 20) (exp 330) := by
  have h := pi_bound (rest := bs.tail) (profile_qrh hpsi) hAnchor certificate.2.1 (by decide)
    certificate.2.2.2.2 (chunked_bound certificate.1 certificate.2.2.1 certificate.2.2.2.1)
  norm_num at h ⊢
  exact h

end Table4Evolution.QRHQuarter
