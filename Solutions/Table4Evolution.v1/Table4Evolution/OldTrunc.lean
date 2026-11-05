/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Agent B (Claude)
-/
import Table4Evolution.Profiles
import Table4Evolution.Data.OldTrunc
import IEANTN.Nodes.FKS2Numerics.v6.Conclusions

/-!
# QRH-free input, evolved program: three cells instead of thirty

The control cell of the ablation: the same truncation applied to the QRH-free step profile (FKS2
Table 3 allowances `1.6930, 1.6882, 1.6837, 1.6795 ·10⁻¹²` from `e^300, e^310, e^320, e^330`).
Cells `[300, 328]`, `[328, 329]`, `[329, 330]`, with the scale and constant literals of the old
program. It proves the registered `FKS2Numerics.v6.old_pi` (`Eπ ≤ 1.69·10⁻¹²` on `x ≥ e^330`)
from the five premises of its challenge.

So the cell reduction is not specific to QRH: the weight `e^{b-330}` of a cell does the work under
either input. QRH needs one cell fewer because its allowance has more slack below its target
(6% against 0.01%). One native fact: `certificate`.
-/

namespace Table4Evolution.OldTrunc

open Real IEANTN PVCore

def program : Program :=
  ⟨"fks2_table4_transport", literals, scaleLiteral,
    [(.plus, anchorLiteral), (.plus, pointLiteral), (.plus, tailLiteral)]⟩

def source : String := include_str ".." / "c" / "old_trunc3.c"

theorem certificate :
    upperCheck source program (4 / 10 ^ 27) (169 / 10 ^ 14) = true ∧
    cellsOK 0 48 stepM bs (valuesOf program).xs = true ∧
    (valuesOf program).scale = 1 / 2 ^ 48 ∧
    (valuesOf program).ops = [(.plus, anchorQ), (.plus, pointQ), (.plus, tailQ)] ∧
    constOK 0 (stepM 300) (stepM 330) anchorQ pointQ tailQ = true := by
  native_decide

/-- `FKS2Numerics.v6.old_pi` from the three-cell program, with the premises of its challenge. -/
theorem old_pi (h300 : FKS2.v8.table3_theta_300) (h310 : FKS2.v8.table3_theta_310)
    (h320 : FKS2.v8.table3_theta_320) (h330 : FKS2.v8.table3_theta_330)
    (hAnchor : FKS2.v6.table4_anchor_300) : FKS2Numerics.v6.old_pi := by
  have h := pi_bound (rest := [328, 329, 330]) (profile_step h300 h310 h320 h330) hAnchor
    certificate.2.1 (by decide) certificate.2.2.2.2
    (program_bound certificate.1 certificate.2.2.1 certificate.2.2.2.1)
  show HasNumericalBound Eπ 1.69e-12 (exp 330)
  norm_num at h ⊢
  exact h

end Table4Evolution.OldTrunc
