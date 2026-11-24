import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Actual Euler integral by a proved rational change of variables. -/
namespace RHOcticPush.BoxGamma
open Real Set MeasureTheory
set_option maxHeartbeats 0

lemma ratio_image : (fun x : ℝ => x / (1 - x)) '' Ioo 0 1 = Ioi 0 := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact div_pos hx.1 (sub_pos.mpr hx.2)
  · intro hy
    change 0 < y at hy
    have hyden : 1+y ≠ 0 := by linarith
    refine ⟨y / (1 + y), ⟨div_pos hy (by linarith), ?_⟩, ?_⟩
    · exact (div_lt_one (by linarith : 0 < 1 + y)).mpr (by linarith)
    · have hden : 1-y/(1+y)=1/(1+y) := by field_simp;ring
      dsimp only
      rw [hden,div_div]
      field_simp

lemma ratio_inj : InjOn (fun x : ℝ => x / (1 - x)) (Ioo 0 1) := by
  intro x hx y hy he
  have h := (div_eq_div_iff (show 1-x ≠ 0 by linarith [hx.2])
    (show 1-y ≠ 0 by linarith [hy.2])).mp he
  nlinarith

lemma ratio_deriv {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun x : ℝ => x / (1 - x)) ((1 - x) ^ 2)⁻¹ x := by
  have hd := (hasDerivAt_id x).div ((hasDerivAt_id x).const_sub 1)
    (show 1-x ≠ 0 by linarith [hx.2])
  convert! hd using 1 <;> dsimp only [id_eq] <;> ring

lemma ratio_integrand (a : ℝ) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    |((1-x)^2)⁻¹| * ((x/(1-x))^(a-1)/(1+x/(1-x))) =
      x^(a-1)*(1-x)^(-a) := by
  have hb : 0 < 1-x := by linarith [hx.2]
  have hsum : 1+x/(1-x) = 1/(1-x) := by field_simp;ring
  have hp : (1-x)^(a-1)*(1-x) = (1-x)^a := by
    calc
      _ = (1-x)^(a-1)*(1-x)^(1:ℝ) := by rw [Real.rpow_one]
      _ = (1-x)^a := by rw [←Real.rpow_add hb];congr 1;ring
  rw [abs_of_pos (by positivity),hsum,Real.div_rpow hx.1.le hb.le,
    Real.rpow_neg hb.le]
  field_simp
  rw [←hp]
  ring

/-- Euler's integral on the positive half-line, proved by the actual rational
Jacobian and the pre-existing Gamma-Beta theorem; not a new source premise. -/
theorem integral_rpow_div_one_add {a : ℝ} (ha : 0<a) (ha1 : a<1) :
    (∫ x in Ioi (0:ℝ), x^(a-1)/(1+x)) = Real.pi/Real.sin (Real.pi*a) := by
  have hb := Complex.betaIntegral_convergent (u := (a:ℂ)) (v := (1-a:ℝ))
    (by simpa using ha) (by simpa using sub_pos.mpr ha1)
  have he := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
    (fun x hx => (ratio_deriv hx).hasDerivWithinAt) ratio_inj
    (fun x : ℝ => x^(a-1)/(1+x))
  rw [ratio_image] at he
  simp only [smul_eq_mul] at he
  have hbeta : (∫ x in Ioo (0:ℝ) 1,x^(a-1)*(1-x)^(-a)) =
      (Complex.betaIntegral (a:ℂ) ((1-a:ℝ):ℂ)).re := by
    rw [Complex.betaIntegral,intervalIntegral.integral_of_le zero_le_one,
      integral_Ioc_eq_integral_Ioo]
    change _ = (RCLike.re : ℂ → ℝ) _
    rw [←integral_re (hb.1.mono_set Ioo_subset_Ioc_self)]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro x hx
    dsimp only
    have hx0 : 0≤x := hx.1.le
    have hx1 : 0≤1-x := by linarith [hx.2]
    rw [show (a:ℂ)-1=((a-1:ℝ):ℂ) by push_cast;rfl,
      show ((1-a:ℝ):ℂ)-1=((-a:ℝ):ℂ) by push_cast;ring,
      show (1:ℂ)-(x:ℂ)=((1-x:ℝ):ℂ) by push_cast;rfl,
      ←Complex.ofReal_cpow hx0,←Complex.ofReal_cpow hx1]
    norm_cast
  rw [setIntegral_congr_fun measurableSet_Ioo (fun x hx => ratio_integrand a hx)] at he
  rw [hbeta] at he
  have hΓ := Complex.Gamma_mul_Gamma_eq_betaIntegral (s := (a:ℂ)) (t := ((1-a:ℝ):ℂ))
    (by simpa using ha) (by simpa using sub_pos.mpr ha1)
  have hsum : (a:ℂ)+((1-a:ℝ):ℂ)=1 := by push_cast;ring
  rw [hsum,Complex.Gamma_one,one_mul,Complex.Gamma_ofReal,Complex.Gamma_ofReal] at hΓ
  have hreal := congrArg Complex.re hΓ
  simp only [Complex.re_ofReal_mul,Complex.ofReal_re] at hreal
  rw [←hreal,Real.Gamma_mul_Gamma_one_sub] at he
  exact he

#print axioms integral_rpow_div_one_add
end RHOcticPush.BoxGamma
