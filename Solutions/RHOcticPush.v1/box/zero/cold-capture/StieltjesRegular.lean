import StieltjesFinite
import Mathlib.Analysis.Complex.RealDeriv

namespace RHOcticPush.StieltjesZeta
open Real Set MeasureTheory Filter Finset
open scoped Topology
set_option maxHeartbeats 0

noncomputable def realRegular (s : ℝ) : ℝ := (riemannZeta₀ (s:ℂ)).re
/-- The actual entire regular-zeta factor used by the Mellin Laurent expansion. -/
noncomputable def regularizedZeta (s : ℝ) : ℝ := (riemannZeta₀ (1+(s:ℂ))).re

lemma realRegular_one : realRegular 1 = Real.eulerMascheroniConstant := by
  simp [realRegular]
lemma regularizedZeta_zero : regularizedZeta 0 = Real.eulerMascheroniConstant := by
  simp [regularizedZeta]
lemma realRegular_differentiable : Differentiable ℝ realRegular := by
  intro s
  exact (differentiable_riemannZeta₀ (s:ℂ)).hasDerivAt.real_of_complex.differentiableAt

lemma actual_zeta_real_series {s : ℝ} (hs : 1<s) :
    riemannZeta (s:ℂ) = ((∑' n : ℕ, 1/(n+1:ℝ)^s):ℝ) := by
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by simpa using hs),Complex.ofReal_tsum]
  apply tsum_congr
  intro n
  rw [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_cpow (by positivity)]
  norm_cast

/-- Actual regular zeta equals the Euler integral series on the complete right
ray, including the endpoint1. No unidentified constant is assumed. -/
theorem realRegular_eq_termTSum {s : ℝ} (hs : 1 ≤ s) :
    realRegular s = 1-s*ZetaAsymptotics.termTSum s := by
  rcases lt_or_eq_of_le hs with hs|rfl
  · have hne : (s:ℂ) ≠ 1 := by exact_mod_cast ne_of_gt hs
    have he : riemannZeta₀ (s:ℂ) =
        (((∑' n : ℕ,1/(n+1:ℝ)^s)-1/(s-1):ℝ):ℂ) := by
      simp only [riemannZeta₀,if_neg hne,actual_zeta_real_series hs,
        Complex.ofReal_sub,Complex.ofReal_div,Complex.ofReal_one]
      simp only [one_div]
    unfold realRegular
    rw [he,Complex.ofReal_re]
    exact ZetaAsymptotics.zeta_limit_aux1 hs
  · rw [realRegular_one]
    have h := ZetaAsymptotics.term_tsum_one.tsum_eq
    change ZetaAsymptotics.termTSum 1 = 1-Real.eulerMascheroniConstant at h
    rw [h]
    ring

#print axioms realRegular_eq_termTSum
#print axioms realRegular_differentiable
end RHOcticPush.StieltjesZeta
