/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic
namespace RHContinuation.DigammaIntegral
open Real Complex MeasureTheory Set

noncomputable def kernel (t:ℝ) : ℝ := 1/(1-Real.exp (-t))-1/t
noncomputable def remainder (z:ℂ) (t:ℝ) : ℂ :=
  (kernel t:ℂ)*Complex.exp (-(t:ℂ)*z)

/-- Exact original DLMF5.9.13, with actual integrability on its source domain.
This is a named standard analytic source input, not an assumed error estimate. -/
def SourceDLMF513 : Prop := ∀ z:ℂ, 0<z.re →
  IntegrableOn (remainder z) (Set.Ioi 0) ∧
  Complex.digamma z-Complex.log z = -(∫ t in Set.Ioi 0,remainder z t)

lemma kernel_bounds {t:ℝ} (ht:0<t) : 0≤kernel t ∧ kernel t≤1 := by
  have he0 : 0<Real.exp (-t) := Real.exp_pos _
  have he1 : Real.exp (-t)<1 := by rw [Real.exp_lt_one_iff]; linarith
  have hd : 0<1-Real.exp (-t) := by linarith
  have hsmall : 1-Real.exp (-t)≤t := by linarith [Real.add_one_le_exp (-t)]
  have hprod : (t+1)*Real.exp (-t)≤1 := by
    rw [Real.exp_neg]
    apply (mul_inv_le_iff₀ (Real.exp_pos t)).mpr
    simpa using Real.add_one_le_exp t
  constructor
  · unfold kernel
    exact sub_nonneg.mpr (one_div_le_one_div_of_le hd hsmall)
  · unfold kernel
    apply (sub_le_iff_le_add).mpr
    apply (div_le_iff₀ hd).mpr
    have hmul : (1+1/t)*(1-Real.exp (-t))-1 =
        (1-(t+1)*Real.exp (-t))/t := by
      field_simp [ne_of_gt ht] <;> ring
    have hnon : 0≤(1-(t+1)*Real.exp (-t))/t := by positivity
    linarith

lemma remainder_norm_le {z:ℂ} {t:ℝ} (ht:0<t) :
    ‖remainder z t‖≤Real.exp (-z.re*t) := by
  have hk := kernel_bounds ht
  unfold remainder
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hk.1,Complex.norm_exp]
  have he : (-(t:ℂ)*z).re = -z.re*t := by simp [Complex.mul_re]; ring
  rw [he]
  exact mul_le_of_le_one_left (Real.exp_pos _).le hk.2

/-- The explicit1/Re(z) remainder is derived from the integral identity; the
existential GammaAsymptotics constant is not silently made numerical. -/
theorem digamma_sub_log_bound (hsource:SourceDLMF513) {z:ℂ} (hz:0<z.re) :
    ‖Complex.digamma z-Complex.log z‖≤1/z.re := by
  have hi := integrableOn_exp_mul_Ioi (a:=-z.re) (by linarith) 0
  have he := integral_exp_mul_Ioi (a:=-z.re) (by linarith) 0
  have hn : ∀ᵐ t ∂volume.restrict (Set.Ioi (0:ℝ)),
      ‖remainder z t‖≤Real.exp (-z.re*t) := by
    apply (ae_restrict_iff' measurableSet_Ioi).mpr
    exact Filter.Eventually.of_forall (fun t ht => remainder_norm_le ht)
  have hb := norm_integral_le_of_norm_le hi hn
  rw [(hsource z hz).2,norm_neg]
  norm_num at he
  have he' : (∫ t in Set.Ioi (0:ℝ),Real.exp (-z.re*t))=1/z.re := by
    simpa only [neg_mul,one_div] using he
  exact hb.trans_eq he'

theorem digamma_real_lower (hsource:SourceDLMF513) {z:ℂ} (hz:0<z.re) :
    Real.log ‖z‖-1/z.re ≤ (Complex.digamma z).re := by
  have h := digamma_sub_log_bound hsource hz
  have hr := Complex.re_le_norm (Complex.log z-Complex.digamma z)
  rw [norm_sub_rev] at hr
  have hr' : (Complex.log z).re-(Complex.digamma z).re≤1/z.re := by
    simpa only [Complex.sub_re] using hr.trans h
  rw [Complex.log_re] at hr'
  linarith

#print axioms digamma_sub_log_bound
#print axioms digamma_real_lower
end RHContinuation.DigammaIntegral
