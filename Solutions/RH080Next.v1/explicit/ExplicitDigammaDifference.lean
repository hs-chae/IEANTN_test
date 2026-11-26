/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitGuinandWeilApplication

set_option autoImplicit false
noncomputable section
open Real Set MeasureTheory
namespace RH080Next.Explicit

def dlmfDigammaIntegrand (z : ℂ) (u : ℝ) : ℂ :=
  (((exp (-u):ℝ):ℂ)-Complex.exp (-z*(u:ℂ)))/((1-exp (-u):ℝ):ℂ)

/-- Official DLMF5.9.16, https://dlmf.nist.gov/5.9.E16, Re(z)>0.
This is the genuinely general complex integral formula; the special real
quadratic kernel below is derived in Lean, not assumed for the chosen window. -/
def SourceDLMFDigammaIntegral : Prop :=
  ∀ z : ℂ, 0 < z.re → IntegrableOn (dlmfDigammaIntegrand z) (Ioi (0:ℝ)) ∧
    Complex.digamma z+(Real.eulerMascheroniConstant:ℂ) =
      ∫ u in Ioi (0:ℝ), dlmfDigammaIntegrand z u

def digammaKernel (u : ℝ) : ℝ := exp (-u/4)/(1-exp (-u))
def digammaDifference (r : ℝ) : ℝ :=
  (Complex.digamma ((1/4:ℂ)+Complex.I*((r/2:ℝ):ℂ))).re-
    (Complex.digamma (1/4:ℂ)).re

private theorem real_dlmf_difference (r u : ℝ) :
    (dlmfDigammaIntegrand ((1/4:ℂ)+Complex.I*((r/2:ℝ):ℂ)) u-
      dlmfDigammaIntegrand (1/4:ℂ) u).re =
      digammaKernel u*(1-cos (r*u/2)) := by
  simp only [dlmfDigammaIntegrand,digammaKernel,Complex.sub_re,Complex.div_ofReal_re,
    Complex.ofReal_re,Complex.exp_re,Complex.neg_re,Complex.neg_im,Complex.mul_re,
    Complex.mul_im,Complex.add_re,Complex.add_im,Complex.ofReal_im,Complex.I_re,Complex.I_im]
  norm_num
  ring_nf

/-- Actual DLMF subtraction, real-part interchange and convergence. -/
theorem digammaDifference_integral (hsource : SourceDLMFDigammaIntegral) (r : ℝ) :
    IntegrableOn (fun u : ℝ => digammaKernel u*(1-cos (r*u/2))) (Ioi (0:ℝ)) ∧
      digammaDifference r = ∫ u in Ioi (0:ℝ), digammaKernel u*(1-cos (r*u/2)) := by
  obtain ⟨h1,e1⟩ := hsource ((1/4:ℂ)+Complex.I*((r/2:ℝ):ℂ)) (by norm_num)
  obtain ⟨h0,e0⟩ := hsource (1/4:ℂ) (by norm_num)
  have hi := h1.sub h0
  have hir := (@RCLike.reCLM ℂ _).integrable_comp hi
  have hf : (fun u : ℝ => (dlmfDigammaIntegrand ((1/4:ℂ)+Complex.I*((r/2:ℝ):ℂ)) u-
      dlmfDigammaIntegrand (1/4:ℂ) u).re) =
      (fun u : ℝ => digammaKernel u*(1-cos (r*u/2))) := funext (real_dlmf_difference r)
  have hival : (∫ u in Ioi (0:ℝ), dlmfDigammaIntegrand ((1/4:ℂ)+Complex.I*((r/2:ℝ):ℂ)) u-
      dlmfDigammaIntegrand (1/4:ℂ) u) =
      Complex.digamma ((1/4:ℂ)+Complex.I*((r/2:ℝ):ℂ))-Complex.digamma (1/4:ℂ) := by
    rw [integral_sub h1 h0,←e1,←e0]
    ring
  have he := integral_re hi
  change (∫ u in Ioi (0:ℝ), (dlmfDigammaIntegrand ((1/4:ℂ)+Complex.I*((r/2:ℝ):ℂ)) u-
    dlmfDigammaIntegrand (1/4:ℂ) u).re) =
    (∫ u in Ioi (0:ℝ), dlmfDigammaIntegrand ((1/4:ℂ)+Complex.I*((r/2:ℝ):ℂ)) u-
      dlmfDigammaIntegrand (1/4:ℂ) u).re at he
  rw [hf,hival,Complex.sub_re] at he
  constructor
  · change IntegrableOn (fun u : ℝ => digammaKernel u*(1-cos (r*u/2))) (Ioi (0:ℝ))
    change IntegrableOn (fun u : ℝ => (dlmfDigammaIntegrand ((1/4:ℂ)+Complex.I*((r/2:ℝ):ℂ)) u-
      dlmfDigammaIntegrand (1/4:ℂ) u).re) (Ioi (0:ℝ)) at hir
    rwa [hf] at hir
  · exact he.symm

theorem digammaKernel_nonneg (u : ℝ) (hu : 0 < u) : 0 ≤ digammaKernel u := by
  unfold digammaKernel
  exact div_nonneg (exp_pos _).le (by have h := Real.exp_lt_one_iff.mpr (show -u<0 by linarith); linarith)

theorem digammaDifference_nonneg (hsource : SourceDLMFDigammaIntegral) (r : ℝ) :
    0 ≤ digammaDifference r := by
  rw [(digammaDifference_integral hsource r).2]
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact mul_nonneg (digammaKernel_nonneg u hu) (by linarith [Real.cos_le_one (r*u/2)])

end RH080Next.Explicit
