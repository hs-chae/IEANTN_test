import GammaQuadratic
import GammaDamped
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-! Full positive-Laplace/Fubini evaluation of the generic cosine Mellin kernel. -/
namespace RHOcticPush.BoxGamma
open Real Set MeasureTheory
set_option maxHeartbeats 0

noncomputable def laplacePacket (s t y : ℝ) : ℝ :=
  t^(1-s)*(1-Real.cos y)*Real.exp (-t*y)

lemma laplacePacket_nonneg (s : ℝ) {t : ℝ} (ht : 0<t) (y : ℝ) :
    0≤laplacePacket s t y := by
  unfold laplacePacket
  exact mul_nonneg (mul_nonneg (Real.rpow_nonneg ht.le _) (by linarith [Real.cos_le_one y]))
    (Real.exp_pos _).le

lemma laplacePacket_integrable (s : ℝ) {t : ℝ} (ht : 0<t) :
    IntegrableOn (laplacePacket s t) (Ioi (0:ℝ)) := by
  exact (damped_integrable ht).const_mul (t^(1-s)) |>.congr
    (Filter.Eventually.of_forall (fun y => by unfold laplacePacket;ring))

lemma laplacePacket_integral_y (s : ℝ) {t : ℝ} (ht : 0<t) :
    (∫ y in Ioi (0:ℝ),laplacePacket s t y) = t^(-s)/(1+t^2) := by
  have he : laplacePacket s t =
      (fun y : ℝ => t^(1-s)*((1-Real.cos y)*Real.exp (-t*y))) := by
    ext y;unfold laplacePacket;ring
  rw [he,integral_const_mul,damped_integral ht]
  have hp : t^(1-s)=t*t^(-s) := by
    calc
      _ = t^((1:ℝ)+(-s)) := by rw [sub_eq_add_neg]
      _ = _ := by rw [Real.rpow_add ht,Real.rpow_one]
  rw [hp]
  field_simp

lemma laplacePacket_integral_t {s : ℝ} (hs : s<2) {y : ℝ} (hy : 0<y) :
    (∫ t in Ioi (0:ℝ),laplacePacket s t y) =
      Real.Gamma (2-s)*((1-Real.cos y)*y^(s-2)) := by
  have he : (fun t : ℝ => laplacePacket s t y) =
      (fun t : ℝ => (1-Real.cos y)*(t^((2-s)-1)*Real.exp (-(y*t)))) := by
    ext t;unfold laplacePacket
    rw [show (2-s)-1=1-s by ring]
    rw [show -(y*t)=-t*y by ring]
    ring
  rw [he,integral_const_mul,Real.integral_rpow_mul_exp_neg_mul_Ioi (by linarith) hy]
  have hp : (1/y)^(2-s)=y^(s-2) := by
    rw [one_div,←Real.rpow_neg_eq_inv_rpow]
    congr 1;ring
  rw [hp]
  ring

/-- All-domain product integrability is proved from the positive Laplace
integral and the actual complete rational Euler integral. -/
theorem laplacePacket_product_integrable {s : ℝ} (hs0 : 0<s) (hs1 : s<1) :
    Integrable (fun p : ℝ×ℝ => laplacePacket s p.1 p.2)
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := by
  have hm : Measurable (fun p : ℝ×ℝ => laplacePacket s p.1 p.2) := by
    unfold laplacePacket
    fun_prop
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact laplacePacket_integrable s ht
  · apply (quadratic_integrable hs0 hs1).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [←laplacePacket_integral_y s ht]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y _
    exact (Real.norm_eq_abs _).trans (abs_of_nonneg (laplacePacket_nonneg s ht y)) |>.symm

/-- The actual generic identity needed by Box Mellin reconstruction.
It has no literature/input predicate and covers every real0<s<1. -/
theorem cosine_mellin {s : ℝ} (hs0 : 0<s) (hs1 : s<1) :
    (∫ y in Ioi (0:ℝ),(1-Real.cos y)*y^(s-2)) =
      Real.pi/(2*Real.Gamma (2-s)*Real.cos (Real.pi*s/2)) := by
  have hi := laplacePacket_product_integrable hs0 hs1
  have h := integral_integral_swap (f := laplacePacket s) hi
  change (∫ t in Ioi (0:ℝ),∫ y in Ioi (0:ℝ),laplacePacket s t y) =
    (∫ y in Ioi (0:ℝ),∫ t in Ioi (0:ℝ),laplacePacket s t y) at h
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => laplacePacket_integral_y s ht),
    integral_quadratic hs0 hs1,
    setIntegral_congr_fun measurableSet_Ioi (fun y hy => laplacePacket_integral_t (by linarith) hy),
    integral_const_mul] at h
  have hΓ : Real.Gamma (2-s) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith : 0<2-s)).ne'
  calc
    _ = (Real.pi/(2*Real.cos (Real.pi*s/2)))/Real.Gamma (2-s) := by
      apply (eq_div_iff hΓ).mpr
      linarith
    _ = _ := by rw [div_div];congr 1;ring

/-- The evaluated integral is also genuinely integrable, rather than relying on
Lean's totalized integral outside its domain. -/
theorem cosine_mellin_integrable {s : ℝ} (hs0 : 0<s) (hs1 : s<1) :
    IntegrableOn (fun y : ℝ => (1-Real.cos y)*y^(s-2)) (Ioi (0:ℝ)) := by
  have h := (laplacePacket_product_integrable hs0 hs1).integral_prod_right
  have he : (fun y : ℝ => ∫ t in Ioi (0:ℝ),laplacePacket s t y) =ᵐ[volume.restrict (Ioi (0:ℝ))]
      (fun y : ℝ => Real.Gamma (2-s)*((1-Real.cos y)*y^(s-2))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact laplacePacket_integral_t (by linarith) hy
  have hΓ : Real.Gamma (2-s) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith : 0<2-s)).ne'
  have hc := (h.congr he).const_mul (Real.Gamma (2-s))⁻¹
  change Integrable (fun y : ℝ => (1-Real.cos y)*y^(s-2)) (volume.restrict (Ioi (0:ℝ)))
  convert! hc using 1 <;> simp only [←mul_assoc,inv_mul_cancel₀ hΓ,one_mul]

#print axioms cosine_mellin
#print axioms cosine_mellin_integrable
end RHOcticPush.BoxGamma
