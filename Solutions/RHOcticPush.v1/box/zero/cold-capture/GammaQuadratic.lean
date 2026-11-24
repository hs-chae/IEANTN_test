import GammaEuler

/-! Actual quadratic Euler integral on the full positive half-line. -/
namespace RHOcticPush.BoxGamma
open Real Set MeasureTheory
set_option maxHeartbeats 0

lemma quadratic_integrand (s : ℝ) {t : ℝ} (ht : 0<t) :
    (2*t^(2-1:ℝ)) * ((t^(2:ℝ))^((1-s)/2-1)/(1+t^(2:ℝ))) =
      2*(t^(-s)/(1+t^2)) := by
  norm_num only [show (2:ℝ)-1=1 by norm_num,Real.rpow_one]
  rw [←Real.rpow_mul ht.le]
  have he : 2*((1-s)/2-1)=(-s)-1 := by ring
  rw [he,Real.rpow_two]
  have hp : t*t^((-s)-1)=t^(-s) := by
    calc
      _ = t^(1:ℝ)*t^((-s)-1) := by rw [Real.rpow_one]
      _ = t^(-s) := by rw [←Real.rpow_add ht];congr 1;ring
  calc
    _ = 2*(t*t^((-s)-1))/(1+t^2) := by ring
    _ = _ := by rw [hp];ring

/-- The complete rational integral needed by the positive Laplace route. -/
theorem integral_quadratic {s : ℝ} (hs0 : 0<s) (hs1 : s<1) :
    (∫ t in Ioi (0:ℝ), t^(-s)/(1+t^2)) =
      Real.pi/(2*Real.cos (Real.pi*s/2)) := by
  have h := integral_comp_rpow_Ioi_of_pos
    (g := fun x : ℝ => x^((1-s)/2-1)/(1+x)) (by norm_num : (0:ℝ)<2)
  simp only [smul_eq_mul] at h
  rw [integral_rpow_div_one_add (by linarith : 0<(1-s)/2) (by linarith : (1-s)/2<1)] at h
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => quadratic_integrand s ht),
    integral_const_mul] at h
  have hsin : Real.sin (Real.pi*((1-s)/2)) = Real.cos (Real.pi*s/2) := by
    rw [show Real.pi*((1-s)/2)=Real.pi/2-Real.pi*s/2 by ring,Real.sin_pi_div_two_sub]
  rw [hsin] at h
  calc
    _ = (Real.pi/Real.cos (Real.pi*s/2))/2 := by linarith
    _ = _ := by rw [div_div];congr 1;ring

lemma quadratic_integrable {s : ℝ} (hs0 : 0<s) (hs1 : s<1) :
    IntegrableOn (fun t : ℝ => t^(-s)/(1+t^2)) (Ioi (0:ℝ)) := by
  by_contra hi
  have h := integral_quadratic hs0 hs1
  rw [integral_undef hi] at h
  have hc : 0<Real.cos (Real.pi*s/2) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> nlinarith [Real.pi_pos]
  have hp : 0<Real.pi/(2*Real.cos (Real.pi*s/2)) := by positivity
  linarith

#print axioms integral_quadratic
#print axioms quadratic_integrable
end RHOcticPush.BoxGamma
