/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitDigammaDifference
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
noncomputable section
open Real Set MeasureTheory
namespace RH080Next.Explicit

def gammaReal (r : ℝ) : ℝ :=
  (Complex.digamma ((1/4:ℂ)+Complex.I*((r/2:ℝ):ℂ))).re

def digammaDoubleKernel (K : ℝ → ℂ) (r u : ℝ) : ℂ :=
  K r*((digammaKernel u*(1-cos (r*u/2)):ℝ):ℂ)

private theorem integrable_norm_times_difference (hD : SourceDLMFDigammaIntegral)
    (K : ℝ → ℂ) (hKi : Integrable K)
    (hKG : Integrable (fun r : ℝ => K r*(gammaReal r:ℂ))) :
    Integrable (fun r : ℝ => ‖K r‖*digammaDifference r) := by
  have hi : Integrable (fun r : ℝ => K r*(digammaDifference r:ℂ)) := by
    apply (hKG.sub (hKi.mul_const ((Complex.digamma (1/4:ℂ)).re:ℂ))).congr
    filter_upwards with r
    simp only [Pi.sub_apply,digammaDifference,gammaReal]
    push_cast
    ring
  apply hi.norm.congr
  filter_upwards with r
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (digammaDifference_nonneg hD r)]

/-- Absolute integrability of the double kernel follows from CMS's existing
Gamma integrability and DLMF positivity. No new Stirling or window-specific
Fubini assumption is introduced. -/
theorem integrable_digamma_double_kernel (hD : SourceDLMFDigammaIntegral)
    (K : ℝ → ℂ) (hK : Continuous K) (hKi : Integrable K)
    (hKG : Integrable (fun r : ℝ => K r*(gammaReal r:ℂ))) :
    Integrable (fun p : ℝ×ℝ => digammaDoubleKernel K p.1 p.2)
      (volume.prod (volume.restrict (Ioi (0:ℝ)))) := by
  have hmeas : Measurable (fun p : ℝ×ℝ => digammaDoubleKernel K p.1 p.2) := by
    unfold digammaDoubleKernel digammaKernel
    fun_prop
  apply (integrable_prod_iff hmeas.aestronglyMeasurable).mpr
  constructor
  · filter_upwards with r
    exact ((digammaDifference_integral hD r).1.ofReal).const_mul (K r)
  · have hn := integrable_norm_times_difference hD K hKi hKG
    have heq (r : ℝ) : (∫ u in Ioi (0:ℝ), ‖digammaDoubleKernel K r u‖) =
        ‖K r‖*digammaDifference r := by
      calc
        _ = ∫ u in Ioi (0:ℝ), ‖K r‖*(digammaKernel u*(1-cos (r*u/2))) := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
          have hpos : 0 ≤ digammaKernel u*(1-cos (r*u/2)) :=
            mul_nonneg (digammaKernel_nonneg u hu) (by linarith [Real.cos_le_one (r*u/2)])
          rw [digammaDoubleKernel,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hpos]
        _ = _ := by rw [integral_const_mul,←(digammaDifference_integral hD r).2]
    simpa only [heq] using hn

/-- The full Fubini interchange needed in the Mellin Gamma elimination. -/
theorem digamma_difference_fubini (hD : SourceDLMFDigammaIntegral)
    (K : ℝ → ℂ) (hK : Continuous K) (hKi : Integrable K)
    (hKG : Integrable (fun r : ℝ => K r*(gammaReal r:ℂ))) :
    (∫ r : ℝ, K r*(digammaDifference r:ℂ)) =
      ∫ u in Ioi (0:ℝ), ∫ r : ℝ, digammaDoubleKernel K r u := by
  have hi := integrable_digamma_double_kernel hD K hK hKi hKG
  have hswap := integral_integral_swap (f := fun r u : ℝ => digammaDoubleKernel K r u)
    (μ := volume) (ν := volume.restrict (Ioi (0:ℝ))) hi
  have heq (r : ℝ) : (∫ u in Ioi (0:ℝ), digammaDoubleKernel K r u) =
      K r*(digammaDifference r:ℂ) := by
    unfold digammaDoubleKernel
    rw [integral_const_mul]
    congr 1
    calc
      _ = (((∫ u in Ioi (0:ℝ), digammaKernel u*(1-cos (r*u/2))):ℝ):ℂ) := integral_ofReal
      _ = _ := congrArg Complex.ofReal (digammaDifference_integral hD r).2.symm

  simpa only [heq] using hswap

#print axioms integrable_digamma_double_kernel
#print axioms digamma_difference_fubini
end RH080Next.Explicit
