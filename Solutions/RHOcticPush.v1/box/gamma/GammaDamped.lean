import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Exact positive Laplace kernel, using only the existing exponential integral. -/
namespace RHOcticPush.BoxGamma
open Real Set MeasureTheory
set_option maxHeartbeats 0

lemma damped_complex {t : ℝ} (ht : 0<t) :
    IntegrableOn (fun y : ℝ => Complex.exp ((-(t:ℂ)+Complex.I)*y)) (Ioi (0:ℝ)) := by
  apply integrableOn_exp_mul_complex_Ioi
  simpa using neg_neg_of_pos ht

lemma damped_re (t y : ℝ) :
    (Complex.exp ((-(t:ℂ)+Complex.I)*y)).re = Real.exp (-t*y)*Real.cos y := by
  rw [Complex.exp_re]
  congr 1 <;> simp

lemma damped_cos_integrable {t : ℝ} (ht : 0<t) :
    IntegrableOn (fun y : ℝ => Real.exp (-t*y)*Real.cos y) (Ioi (0:ℝ)) := by
  exact (damped_complex ht).re.congr (Filter.Eventually.of_forall (damped_re t))

lemma damped_cos_integral {t : ℝ} (ht : 0<t) :
    (∫ y in Ioi (0:ℝ),Real.exp (-t*y)*Real.cos y) = t/(1+t^2) := by
  have h := integral_exp_mul_complex_Ioi (a := -(t:ℂ)+Complex.I)
    (by simpa using neg_neg_of_pos ht) 0
  calc
    _ = (∫ y in Ioi (0:ℝ),Complex.exp ((-(t:ℂ)+Complex.I)*y)).re := by
      calc
        _ = ∫ y in Ioi (0:ℝ),(Complex.exp ((-(t:ℂ)+Complex.I)*y)).re := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro y _
          exact (damped_re t y).symm
        _ = _ := integral_re (damped_complex ht)
    _ = _ := by
      rw [h]
      simp [Complex.div_re,Complex.normSq]
      ring

lemma damped_integrable {t : ℝ} (ht : 0<t) :
    IntegrableOn (fun y : ℝ => (1-Real.cos y)*Real.exp (-t*y)) (Ioi (0:ℝ)) := by
  have he := integrableOn_exp_mul_Ioi (by linarith : -t<0) 0
  exact (he.sub (damped_cos_integrable ht)).congr
    (Filter.Eventually.of_forall (fun y => by dsimp only [Pi.sub_apply];ring))

/-- Entire positive-Laplace integral; no finite truncation or numerical input. -/
theorem damped_integral {t : ℝ} (ht : 0<t) :
    (∫ y in Ioi (0:ℝ),(1-Real.cos y)*Real.exp (-t*y)) = 1/(t*(1+t^2)) := by
  have he := integrableOn_exp_mul_Ioi (by linarith : -t<0) 0
  have hc := damped_cos_integrable ht
  have heq : (fun y : ℝ => (1-Real.cos y)*Real.exp (-t*y)) =
      (fun y : ℝ => Real.exp (-t*y)-Real.exp (-t*y)*Real.cos y) := by ext y;ring
  rw [heq,integral_sub he hc,integral_exp_mul_Ioi (by linarith : -t<0) 0,
    damped_cos_integral ht]
  simp only [mul_zero,Real.exp_zero,neg_div_neg_eq]
  field_simp
  ring

#print axioms damped_cos_integral
#print axioms damped_integral
end RHOcticPush.BoxGamma
