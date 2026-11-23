import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! Derivatives of the actual digamma function from reflection and duplication. -/
namespace RHOcticPush.BoxGamma
open Complex Filter Set
open scoped Topology

lemma gamma_analytic {z : ℂ} (hz : 0 < z.re) : AnalyticAt ℂ Complex.Gamma z := by
  apply DifferentiableOn.analyticAt (s := {w : ℂ | 0 < w.re})
  · intro w hw
    apply (Complex.differentiableAt_Gamma w ?_).differentiableWithinAt
    intro n hn
    have h := congrArg Complex.re hn
    simp only [neg_re, natCast_re] at h
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    simp only [mem_setOf_eq] at hw
    linarith
  · exact (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz

lemma digamma_differentiable {z : ℂ} (hz : 0 < z.re) :
    DifferentiableAt ℂ Complex.digamma z := by
  have ha := gamma_analytic hz
  have hn : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero (by
    intro n hn
    have h := congrArg Complex.re hn
    simp only [neg_re, natCast_re] at h
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith)
  exact ha.deriv.differentiableAt.div ha.differentiableAt hn

lemma reflection_near_half :
    (fun z : ℂ => Complex.digamma (1 - z)) =ᶠ[𝓝 (1 / 2 : ℂ)]
      (fun z => Complex.digamma z + (Real.pi : ℂ) * Complex.cot (Real.pi * z)) := by
  have he : ∀ᶠ z : ℂ in 𝓝 (1 / 2 : ℂ), z.re ∈ Ioo (0 : ℝ) 1 :=
    Complex.continuous_re.continuousAt.eventually
      (Ioo_mem_nhds (by norm_num) (by norm_num))
  filter_upwards [he] with z hz
  apply Complex.digamma_one_sub
  intro n hn
  have h := congrArg Complex.re hn
  simp only [intCast_re] at h
  have h0 : (0 : ℤ) < n := by exact_mod_cast (show (0 : ℝ) < n by linarith [hz.1])
  have h1 : n < (1 : ℤ) := by exact_mod_cast (show (n : ℝ) < 1 by linarith [hz.2])
  omega

theorem trigamma_half : deriv Complex.digamma (1 / 2 : ℂ) = (Real.pi : ℂ)^2 / 2 := by
  have hd := (digamma_differentiable (z := (1 / 2 : ℂ)) (by norm_num)).hasDerivAt
  have hl0 : HasDerivAt Complex.digamma (deriv Complex.digamma (1 / 2 : ℂ))
      (1 - (1 / 2 : ℂ)) := by
    rw [show (1 - (1 / 2 : ℂ)) = 1 / 2 by norm_num]
    exact hd
  have hl := hl0.comp (1 / 2 : ℂ) ((hasDerivAt_id (1 / 2 : ℂ)).const_sub 1)
  have hs := (Complex.hasDerivAt_sin (Real.pi * (1 / 2 : ℂ))).comp
    (1 / 2 : ℂ) ((hasDerivAt_id (1 / 2 : ℂ)).const_mul (Real.pi : ℂ))
  have hc := (Complex.hasDerivAt_cos (Real.pi * (1 / 2 : ℂ))).comp
    (1 / 2 : ℂ) ((hasDerivAt_id (1 / 2 : ℂ)).const_mul (Real.pi : ℂ))
  have hn : Complex.sin (Real.pi * (1 / 2 : ℂ)) ≠ 0 := by
    norm_num [mul_one_div]
  have hr := hd.add ((hc.div hs hn).const_mul (Real.pi : ℂ))
  have he := hl.unique (hr.congr_of_eventuallyEq (by
    filter_upwards [reflection_near_half] with z hz
    change Complex.digamma (1 - z) = Complex.digamma z +
      (Real.pi : ℂ) * (Complex.cos (Real.pi * z) / Complex.sin (Real.pi * z))
    exact hz))
  norm_num [mul_one_div] at he
  linear_combination -(1 / 2 : ℂ) * he

theorem trigamma_one : deriv Complex.digamma 1 = (Real.pi : ℂ)^2 / 6 := by
  have hhalf := (digamma_differentiable (z := (1 / 2 : ℂ)) (by norm_num)).hasDerivAt
  have hone := (digamma_differentiable (z := (1 : ℂ)) (by norm_num)).hasDerivAt
  have hl0 : HasDerivAt Complex.digamma (deriv Complex.digamma 1)
      (2 * (1 / 2 : ℂ)) := by
    rw [show (2 * (1 / 2 : ℂ)) = 1 by norm_num]
    exact hone
  have hl := hl0.comp (h := fun z : ℂ => 2 * z) (1 / 2 : ℂ)
    ((hasDerivAt_id (1 / 2 : ℂ)).const_mul 2)
  have hm0 : HasDerivAt Complex.digamma (deriv Complex.digamma 1)
      ((1 / 2 : ℂ) + 1 / 2) := by
    rw [show ((1 / 2 : ℂ) + 1 / 2) = 1 by norm_num]
    exact hone
  have hm := hm0.comp (h := fun z : ℂ => z + 1 / 2) (1 / 2 : ℂ)
    ((hasDerivAt_id (1 / 2 : ℂ)).add_const (1 / 2))
  have hr := ((hhalf.add hm).const_mul (1 / 2 : ℂ)).add_const (Complex.log 2)
  have heq : (fun z : ℂ => Complex.digamma (2 * z)) =ᶠ[𝓝 (1 / 2 : ℂ)]
      (fun z => (1 / 2 : ℂ) * (Complex.digamma z + Complex.digamma (z + 1 / 2)) + Complex.log 2) := by
    have he : ∀ᶠ z : ℂ in 𝓝 (1 / 2 : ℂ), 0 < z.re :=
      Complex.continuous_re.continuousAt.eventually (Ioi_mem_nhds (by norm_num))
    filter_upwards [he] with z hz
    apply Complex.digamma_two_mul
    intro n hn
    have h := congrArg Complex.re hn
    norm_num at h
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have he := hl.unique (hr.congr_of_eventuallyEq heq)
  rw [trigamma_half] at he
  linear_combination (2 / 3 : ℂ) * he

#print axioms trigamma_half
#print axioms trigamma_one
end RHOcticPush.BoxGamma
