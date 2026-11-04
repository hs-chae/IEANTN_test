/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Agent B (Claude)
-/
import PVCore.SumAffine

/-!
# Application bridge

An application has a mathematical quantity `T` (a transport allowance, an epsilon budget, …) and
proves, by its own mathematics, that `T` is at most what the program computes in exact arithmetic:
`T ≤ scale · Σ xᵢ + Σ ±cⱼ`, with `xᵢ`, `cⱼ` the loaded literals. That inequality is the
application's whole numerical obligation. `le_bound_of_check` then turns one passing certificate
into `T ≤ bound`. The lower direction is `bound_le_of_check`.

Example: Table 4 proves `Bsafe U ≤ scale · Σ xᵢ + anchor + point + tail` from its analytic cell,
anchor and tail enclosures; the certificate gives `Bsafe U ≤ 5·10⁻¹⁶`.
-/

namespace PVCore

/-- Certificate for an upper-bound application. -/
def upperCheck (src : String) (p : Program) (eps bound : ℚ) : Bool :=
  check src p eps &&
    decide ((valuesOf p).out + forwardError (valuesOf p).scale (valuesOf p).s eps
      (valuesOf p).xs.length ≤ bound)

/-- Certificate for a lower-bound application. -/
def lowerCheck (src : String) (p : Program) (eps bound : ℚ) : Bool :=
  check src p eps &&
    decide (bound ≤ (valuesOf p).out - forwardErrorLower (valuesOf p).scale (valuesOf p).s eps
      (valuesOf p).xs.length)

/-- **Application bridge (upper).** -/
theorem le_bound_of_check {src : String} {p : Program} {eps bound : ℚ}
    (h : upperCheck src p eps bound = true) {T : ℝ}
    (hT : T ≤ ((valuesOf p).scale : ℝ) * ((valuesOf p).xs.sum : ℝ) +
      (opsConst (valuesOf p).ops : ℝ)) : T ≤ bound := by
  simp only [upperCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hc, hb⟩ := h
  obtain ⟨-, -, -, -, hup, -⟩ := certified hc
  simp only [exactValue, opsValue_eq] at hup
  have hq : (valuesOf p).scale * (valuesOf p).xs.sum + opsConst (valuesOf p).ops ≤ bound := by
    linarith
  calc T ≤ _ := hT
    _ ≤ (bound : ℝ) := by exact_mod_cast hq

/-- **Application bridge (lower).** -/
theorem bound_le_of_check {src : String} {p : Program} {eps bound : ℚ}
    (h : lowerCheck src p eps bound = true) {T : ℝ}
    (hT : ((valuesOf p).scale : ℝ) * ((valuesOf p).xs.sum : ℝ) +
      (opsConst (valuesOf p).ops : ℝ) ≤ T) : (bound : ℝ) ≤ T := by
  simp only [lowerCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hc, hb⟩ := h
  obtain ⟨-, -, -, -, -, hlo⟩ := certified hc
  simp only [exactValue, opsValue_eq] at hlo
  have hq : bound ≤ (valuesOf p).scale * (valuesOf p).xs.sum + opsConst (valuesOf p).ops := by
    linarith
  calc (bound : ℝ) ≤ _ := by exact_mod_cast hq
    _ ≤ T := hT

end PVCore
