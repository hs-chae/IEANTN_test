/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitGammaAffine
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

set_option autoImplicit false
noncomputable section
open Real Set MeasureTheory
namespace RH080Next.Explicit

def gammaYIntegrand (nodes : List ℚ) (m : ℕ) (d L y : ℝ) : ℝ :=
  affineSpectrum nodes m ((log y-L)/d)/(sqrt y*y*(1-1/y^2))

private theorem gammaY_exp_identity (nodes : List ℚ) (m : ℕ) (d L u : ℝ) (hu : 0 < u) :
    gammaYIntegrand nodes m d L (exp (u/2))*(exp (u/2)/2) =
      (1/2:ℝ)*gammaWeight nodes m d L u := by
  have hpow : exp (u/2)^2 = exp u := by rw [←Real.exp_nat_mul]; congr 1; ring
  have hsqrt : sqrt (exp (u/2)) = exp (u/4) := by
    rw [←Real.exp_half]
    congr 1
    ring
  have hinv : 1/exp (u/2)^2 = exp (-u) := by rw [hpow,Real.exp_neg]; simp only [one_div]
  have hden : 1-exp (-u) ≠ 0 := by
    have he := Real.exp_lt_one_iff.mpr (show -u<0 by linarith)
    linarith
  have hneg : exp (-u/4) = (exp (u/4))⁻¹ := by
    rw [show -u/4 = -(u/4) by ring,Real.exp_neg]
  unfold gammaYIntegrand gammaWeight digammaKernel
  rw [Real.log_exp,hsqrt,hinv,hneg]
  field_simp [hden,Real.exp_ne_zero]
  <;> ring

/-- Finite positive change of variables y=exp(u/2), with actual integrability
transport. This supplies the Gamma substitution used in the Mellin identity. -/
theorem gamma_positive_substitution (nodes : List ℚ) (m : ℕ)
    (hlen : 2 ≤ nodes.length) (hm : 0 < m) (d L : ℝ) (hd : 0 < d)
    (hpositive : radius nodes m*d < L)
    (hphi : IntegrableOn (gammaWeight nodes m d L) (Ioi (0:ℝ))) :
    IntervalIntegrable (gammaYIntegrand nodes m d L) volume
      (exp (L-radius nodes m*d)) (exp (L+radius nodes m*d)) ∧
    (∫ u in Ioi (0:ℝ), gammaWeight nodes m d L u) =
      2*(∫ y in exp (L-radius nodes m*d)..exp (L+radius nodes m*d),
        gammaYIntegrand nodes m d L y) := by
  let R := radius nodes m
  let A : ℝ := 2*(L-R*d)
  let B : ℝ := 2*(L+R*d)
  have hR : 0 ≤ R := by dsimp [R,radius]; positivity
  have hA : 0 < A := by dsimp [A,R]; linarith
  have hAB : A ≤ B := by dsimp [A,B]; nlinarith
  have hout (u : ℝ) (hu : u ∉ Icc A B) : gammaWeight nodes m d L u = 0 := by
    have hv : R ≤ |(u/2-L)/d| := by
      by_contra h
      have ha := abs_lt.mp (lt_of_not_ge h)
      have ha1 := (lt_div_iff₀ hd).mp ha.1
      have ha2 := (div_lt_iff₀ hd).mp ha.2
      apply hu
      constructor <;> dsimp [A,B] <;> linarith
    unfold gammaWeight
    rw [affineSpectrum_eq_zero_of_radius_le nodes m hlen hm _ hv,mul_zero]
  have hIoi : (∫ u in Ioi (0:ℝ), gammaWeight nodes m d L u) =
      ∫ u : ℝ, gammaWeight nodes m d L u := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro u hu
    apply hout u
    intro hmem
    have hu0 : u ≤ 0 := by simpa only [mem_Ioi,not_lt] using hu
    linarith [hmem.1]
  have hIcc : (∫ u in Icc A B, gammaWeight nodes m d L u) =
      ∫ u : ℝ, gammaWeight nodes m d L u :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hout
  have hwindow : (∫ u in Ioi (0:ℝ), gammaWeight nodes m d L u) =
      ∫ u in A..B, gammaWeight nodes m d L u := by
    rw [hIoi,←hIcc,integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le hAB]
  have hiphi : IntervalIntegrable (gammaWeight nodes m d L) volume A B := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hAB).mpr
    apply hphi.mono_set
    intro u hu
    exact lt_trans hA hu.1
  have hder (u : ℝ) : HasDerivAt (fun t : ℝ => exp (t/2)) (exp (u/2)/2) u := by
    simpa only [id_eq,div_eq_mul_inv,one_mul] using ((hasDerivAt_id u).div_const 2).exp
  have hcont : ContinuousOn (fun u : ℝ => exp (u/2)) (uIcc A B) := by fun_prop
  have hderOn : ∀ u ∈ Ioo (min A B) (max A B),
      HasDerivAt (fun t : ℝ => exp (t/2)) (exp (u/2)/2) u := fun u hu => hder u
  have hposDer : ∀ u ∈ Ioo (min A B) (max A B), 0 ≤ exp (u/2)/2 := by intros; positivity
  have hpoint : EqOn (fun u : ℝ => gammaYIntegrand nodes m d L (exp (u/2))*(exp (u/2)/2))
      (fun u : ℝ => (1/2:ℝ)*gammaWeight nodes m d L u) (uIcc A B) := by
    intro u hu
    rw [uIcc_of_le hAB] at hu
    exact gammaY_exp_identity nodes m d L u (lt_of_lt_of_le hA hu.1)
  have hcompInt : IntervalIntegrable
      (fun u : ℝ => gammaYIntegrand nodes m d L (exp (u/2))*(exp (u/2)/2)) volume A B := by
    apply (hiphi.const_mul (1/2:ℝ)).congr
    intro u hu
    exact (hpoint (uIoc_subset_uIcc hu)).symm
  have hiff := intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg
    (g := gammaYIntegrand nodes m d L) hcont hderOn hposDer
  have hchange := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (g := gammaYIntegrand nodes m d L) hcont hderOn hposDer
  have hargA : A/2 = L-R*d := by dsimp [A]; ring
  have hargB : B/2 = L+R*d := by dsimp [B]; ring
  dsimp only [Function.comp_def] at hiff hchange
  have htarget := hiff.mp hcompInt
  rw [hargA,hargB] at htarget hchange
  refine ⟨htarget,?_⟩
  rw [intervalIntegral.integral_congr hpoint,intervalIntegral.integral_const_mul] at hchange
  rw [hwindow]
  linarith

#print axioms gamma_positive_substitution
end RH080Next.Explicit
