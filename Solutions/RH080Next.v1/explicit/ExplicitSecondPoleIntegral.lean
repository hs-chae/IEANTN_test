/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitGammaSubstitution

set_option autoImplicit false
noncomputable section
open Real Set MeasureTheory
namespace RH080Next.Explicit

def secondPoleYIntegrand (nodes : List ℚ) (m : ℕ) (d L y : ℝ) : ℝ :=
  affineSpectrum nodes m ((log y-L)/d)/(sqrt y*y)

private theorem secondPole_exp_identity (nodes : List ℚ) (m : ℕ) (d L v : ℝ) (hd : d ≠ 0) :
    secondPoleYIntegrand nodes m d L (exp (L+d*v))*(d*exp (L+d*v)) =
      (d*exp (-L/2))*(affineSpectrum nodes m v*exp ((-d/2)*v)) := by
  have harg : (L+d*v-L)/d = v := by field_simp <;> ring
  have hsqrt : sqrt (exp (L+d*v)) = exp ((L+d*v)/2) := (Real.exp_half _).symm
  unfold secondPoleYIntegrand
  rw [Real.log_exp,harg,hsqrt]
  calc
    _ = d*affineSpectrum nodes m v / exp ((L+d*v)/2) := by field_simp <;> ring
    _ = d*affineSpectrum nodes m v*exp (-((L+d*v)/2)) := by rw [Real.exp_neg]; ring
    _ = _ := by rw [show -((L+d*v)/2) = -L/2+(-d/2)*v by ring,Real.exp_add]; ring

/-- The small imaginary pole equals the actual arithmetic y-integral, with
both interval integrability and the exact compact change of variables proved. -/
theorem second_pole_integral (nodes : List ℚ) (m : ℕ) (hlen : 2 ≤ nodes.length)
    (hm : 0 < m) (d L : ℝ) (hd : 0 < d) :
    IntervalIntegrable (secondPoleYIntegrand nodes m d L) volume
      (exp (L-radius nodes m*d)) (exp (L+radius nodes m*d)) ∧
    (∫ y in exp (L-radius nodes m*d)..exp (L+radius nodes m*d), secondPoleYIntegrand nodes m d L y) =
      d*exp (-L/2)*windowLaplaceIntegral nodes m (-d/2) := by
  let R := radius nodes m
  have hR : 0 ≤ R := by dsimp [R,radius]; positivity
  have hAB : -R ≤ R := by linarith
  have hc : Continuous (fun v : ℝ => exp (L+d*v)) := by fun_prop
  have hder (v : ℝ) : HasDerivAt (fun w : ℝ => exp (L+d*w)) (d*exp (L+d*v)) v := by
    have h := (((hasDerivAt_id v).const_mul d).const_add L).exp
    simpa only [id_eq,mul_one,mul_comm] using h
  have hderOn : ∀ v ∈ Ioo (min (-R) R) (max (-R) R),
      HasDerivAt (fun w : ℝ => exp (L+d*w)) (d*exp (L+d*v)) v := fun v hv => hder v
  have hnonneg : ∀ v ∈ Ioo (min (-R) R) (max (-R) R), 0 ≤ d*exp (L+d*v) := by intros; positivity
  have hiff := intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg
    (g := secondPoleYIntegrand nodes m d L) hc.continuousOn hderOn hnonneg
  have hchange := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (g := secondPoleYIntegrand nodes m d L) hc.continuousOn hderOn hnonneg
  dsimp only [Function.comp_def] at hiff hchange
  have heq : (fun v : ℝ => secondPoleYIntegrand nodes m d L (exp (L+d*v))*(d*exp (L+d*v))) =
      (fun v : ℝ => (d*exp (-L/2))*(affineSpectrum nodes m v*exp ((-d/2)*v))) :=
    funext (fun v => secondPole_exp_identity nodes m d L v hd.ne')
  rw [heq] at hiff hchange
  have hi : IntervalIntegrable (fun v : ℝ => affineSpectrum nodes m v*exp ((-d/2)*v)) volume (-R) R :=
    (by fun_prop : Continuous (fun v : ℝ => affineSpectrum nodes m v*exp ((-d/2)*v))).intervalIntegrable _ _
  have hitarget := hiff.mp (hi.const_mul (d*exp (-L/2)))
  have harg : L+d*(-R) = L-R*d := by ring
  have harg' : L+d*R = L+R*d := by ring
  rw [harg,harg'] at hitarget hchange
  refine ⟨hitarget,?_⟩
  rw [intervalIntegral.integral_const_mul] at hchange
  rw [←hchange]
  congr 1
  unfold windowLaplaceIntegral
  rw [intervalIntegral.integral_of_le hAB,←integral_Icc_eq_integral_Ioc]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro v hv
  have hw : affineSpectrum nodes m v = 0 := by
    by_contra h
    exact hv (affineSpectrum_support_subset nodes m hlen hm h)
  rw [hw,zero_mul]

#print axioms second_pole_integral
end RH080Next.Explicit
