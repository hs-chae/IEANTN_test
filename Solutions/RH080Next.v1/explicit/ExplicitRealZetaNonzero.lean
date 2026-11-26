/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open Real Set MeasureTheory
namespace RH080Next.Explicit

/-- Real specialization of DLMF 25.5.E3, after multiplication by the
denominator. The source gives the convergent integral for Re(s)>0, s≠1.
This general analytic formula is an explicit literature input, not a
kernel proof of the zeta/eta integral representation.
Source: https://dlmf.nist.gov/25.5.E3; Erdélyi et al. (1953a),
(1.12.5), p. 32. There is no numerical zeta value in this contract. -/
def SourceDLMFRealEtaIntegral : Prop :=
  ∀ s : ℝ, 0<s → s≠1 →
    IntegrableOn (fun x : ℝ => x^(s-1)/(exp x+1)) (Ioi (0:ℝ)) ∧
      (∫ x in Ioi (0:ℝ), x^(s-1)/(exp x+1)) =
        (1-(2:ℝ)^(1-s))*Gamma s*(riemannZeta (s:ℂ)).re

theorem eta_kernel_pos (s x : ℝ) (hx : 0<x) :
    0<x^(s-1)/(exp x+1) :=
  div_pos (rpow_pos_of_pos hx _) (by positivity)

/-- The entire real critical strip is zero-free, derived from the named
general integral representation and proved positivity, not from N(10)=0
(which counts only strictly positive imaginary parts). -/
theorem real_zeta_re_neg (hD : SourceDLMFRealEtaIntegral)
    (s : ℝ) (hs : 0<s) (hs1 : s<1) : (riemannZeta (s:ℂ)).re<0 := by
  have hint := hD s hs (ne_of_lt hs1)
  have hnn : ∀ᵐ x : ℝ ∂volume.restrict (Ioi (0:ℝ)),
      0≤x^(s-1)/(exp x+1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact (eta_kernel_pos s x hx).le
  have hsupp : Function.support (fun x : ℝ => x^(s-1)/(exp x+1)) ∩ Ioi (0:ℝ) =
      Ioi (0:ℝ) := by
    ext x
    simp only [mem_inter_iff]
    exact ⟨And.right, fun hx => ⟨ne_of_gt (eta_kernel_pos s x hx),hx⟩⟩
  have hpos : 0<∫ x in Ioi (0:ℝ), x^(s-1)/(exp x+1) := by
    apply (setIntegral_pos_iff_support_of_nonneg_ae hnn hint.1).mpr
    rw [hsupp]
    simp
  rw [hint.2] at hpos
  have hp : 1<(2:ℝ)^(1-s) := one_lt_rpow (by norm_num) (by linarith)
  have hg := Gamma_pos_of_pos hs
  have hc : (1-(2:ℝ)^(1-s))*Gamma s<0 := mul_neg_of_neg_of_pos (by linarith) hg
  by_contra hh
  have h := mul_nonpos_of_nonpos_of_nonneg hc.le (le_of_not_gt hh)
  linarith

theorem real_zeta_ne_zero (hD : SourceDLMFRealEtaIntegral)
    (s : ℝ) (hs : 0<s) (hs1 : s<1) : riemannZeta (s:ℂ)≠0 := by
  intro h
  have hn := real_zeta_re_neg hD s hs hs1
  simp only [h,Complex.zero_re] at hn
  exact (lt_irrefl 0) hn

theorem zeta_one_half_ne_zero (hD : SourceDLMFRealEtaIntegral) :
    riemannZeta (1/2:ℂ)≠0 := by
  simpa using real_zeta_ne_zero hD (1/2) (by norm_num) (by norm_num)

#print axioms real_zeta_re_neg
#print axioms real_zeta_ne_zero
#print axioms zeta_one_half_ne_zero
end RH080Next.Explicit
