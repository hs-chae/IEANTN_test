import BoxGammaSecond

/-! Transport actual complex second Gamma derivatives to real derivatives. -/
namespace RHOcticPush.BoxGamma
open Filter Set
open scoped Topology

lemma gamma_real_deriv {x : ℝ} (hx : 0 < x) :
    deriv Real.Gamma x = (deriv Complex.Gamma (x : ℂ)).re := by
  have hd := (Complex.differentiableAt_Gamma (x : ℂ) (by
    intro n hn
    have h := congrArg Complex.re hn
    simp only [Complex.ofReal_re, Complex.neg_re, Complex.natCast_re] at h
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith)).hasDerivAt.real_of_complex
  have heq : (fun t : ℝ => (Complex.Gamma (t : ℂ)).re) = Real.Gamma := by
    ext t
    simp [Complex.Gamma_ofReal]
  rw [heq] at hd
  exact hd.deriv

theorem gamma_real_second_one : HasDerivAt (deriv Real.Gamma)
    (Real.eulerMascheroniConstant^2 + Real.pi^2 / 6) 1 := by
  have hd := gamma_second_one.real_of_complex
  have h := hd.congr_of_eventuallyEq (by
    filter_upwards [Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with x hx
    exact gamma_real_deriv hx)
  exact h.congr_deriv (by simp [pow_two, Complex.mul_re])

theorem gamma_real_second_two : HasDerivAt (deriv Real.Gamma)
    (Real.eulerMascheroniConstant^2 - 2 * Real.eulerMascheroniConstant +
      Real.pi^2 / 6) 2 := by
  have hd := gamma_second_two.real_of_complex
  have h := hd.congr_of_eventuallyEq (by
    filter_upwards [Ioi_mem_nhds (show (0 : ℝ) < 2 by norm_num)] with x hx
    exact gamma_real_deriv hx)
  exact h.congr_deriv (by simp [pow_two, Complex.mul_re])

#print axioms gamma_real_second_one
#print axioms gamma_real_second_two
end RHOcticPush.BoxGamma
