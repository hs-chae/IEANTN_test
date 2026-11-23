import BoxTrigamma

/-! Actual second Gamma derivatives used for the Box Mellin linear coefficient. -/
namespace RHOcticPush.BoxGamma
open Complex Filter Set
open scoped Topology

lemma gamma_deriv_eq {z : ℂ} (hz : 0 < z.re) :
    deriv Complex.Gamma z = Complex.digamma z * Complex.Gamma z := by
  have hn : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero (by
    intro n hn
    have h := congrArg Complex.re hn
    simp only [neg_re, natCast_re] at h
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith)
  rw [Complex.digamma_def, logDeriv_apply, div_mul_cancel₀ _ hn]

theorem gamma_second_one : HasDerivAt (deriv Complex.Gamma)
    ((Real.eulerMascheroniConstant : ℂ)^2 + (Real.pi : ℂ)^2 / 6) 1 := by
  have hp := (digamma_differentiable (z := (1 : ℂ)) (by norm_num)).hasDerivAt
  rw [trigamma_one] at hp
  have hd := hp.mul Complex.hasDerivAt_Gamma_one
  have h := hd.congr_of_eventuallyEq (by
    have he : ∀ᶠ z : ℂ in 𝓝 (1 : ℂ), 0 < z.re :=
      Complex.continuous_re.continuousAt.eventually (Ioi_mem_nhds (by norm_num))
    filter_upwards [he] with z hz
    exact gamma_deriv_eq hz)
  exact h.congr_deriv (by simp [Complex.Gamma_one, Complex.digamma_one]; ring)

lemma digamma_two_value : Complex.digamma 2 = 1 - (Real.eulerMascheroniConstant : ℂ) := by
  have h := Complex.digamma_nat_add_one 1
  convert h using 1 <;> norm_num [harmonic] <;> ring

theorem trigamma_two : deriv Complex.digamma 2 = (Real.pi : ℂ)^2 / 6 - 1 := by
  have h1 := (digamma_differentiable (z := (1 : ℂ)) (by norm_num)).hasDerivAt
  have h2 := (digamma_differentiable (z := (2 : ℂ)) (by norm_num)).hasDerivAt
  have h2' : HasDerivAt Complex.digamma (deriv Complex.digamma 2) ((1 : ℂ) + 1) := by
    rw [show (1 : ℂ) + 1 = 2 by norm_num]
    exact h2
  have hl := h2'.comp (h := fun z : ℂ => z + 1) 1 ((hasDerivAt_id (1 : ℂ)).add_const 1)
  have hr := h1.add ((hasDerivAt_id (1 : ℂ)).inv (by norm_num))
  have heq : (fun z : ℂ => Complex.digamma (z + 1)) =ᶠ[𝓝 (1 : ℂ)]
      (fun z => Complex.digamma z + z⁻¹) := by
    have he : ∀ᶠ z : ℂ in 𝓝 (1 : ℂ), 0 < z.re :=
      Complex.continuous_re.continuousAt.eventually (Ioi_mem_nhds (by norm_num))
    filter_upwards [he] with z hz
    apply Complex.digamma_apply_add_one
    intro n hn
    have h := congrArg Complex.re hn
    simp only [neg_re, natCast_re] at h
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have he := hl.unique (hr.congr_of_eventuallyEq heq)
  simpa [trigamma_one, sub_eq_add_neg] using he

lemma gamma_two_derivative_complex : HasDerivAt Complex.Gamma
    (1 - (Real.eulerMascheroniConstant : ℂ)) 2 := by
  convert Complex.hasDerivAt_Gamma_nat 1 using 1 <;> norm_num [harmonic] <;> ring

theorem gamma_second_two : HasDerivAt (deriv Complex.Gamma)
    ((Real.eulerMascheroniConstant : ℂ)^2 - 2 * (Real.eulerMascheroniConstant : ℂ) +
      (Real.pi : ℂ)^2 / 6) 2 := by
  have hp := (digamma_differentiable (z := (2 : ℂ)) (by norm_num)).hasDerivAt
  rw [trigamma_two] at hp
  have hd := hp.mul gamma_two_derivative_complex
  have h := hd.congr_of_eventuallyEq (by
    have he : ∀ᶠ z : ℂ in 𝓝 (2 : ℂ), 0 < z.re :=
      Complex.continuous_re.continuousAt.eventually (Ioi_mem_nhds (by norm_num))
    filter_upwards [he] with z hz
    exact gamma_deriv_eq hz)
  exact h.congr_deriv (by
    norm_num [Complex.Gamma_nat_eq_factorial, digamma_two_value]
    ring)

#print axioms gamma_second_one
#print axioms trigamma_two
#print axioms gamma_second_two
end RHOcticPush.BoxGamma
