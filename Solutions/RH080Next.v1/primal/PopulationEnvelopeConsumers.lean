/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import PopulationEnvelopeAlgebra
import PopulationActualConsumers
import FFTW4MainConsumers
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
namespace RH080Next.PopulationEnvelope
open IEANTN.CMSFunctional RH080Next.Explicit

theorem good_min {α c d : ℝ} (first : GoodCoefficient α c) (second : GoodCoefficient α d) :
    GoodCoefficient α (min c d) := by
  rcases le_total c d with h|h
  · simpa only [min_eq_left h] using first
  · simpa only [min_eq_right h] using second

section LiteralInputs
variable (hBRNorm : SourceBRFourierNormFive) (hBR : SourceBRFourierNormStrip)
    (hCMS : SourceCMSGuinandWeil) (hDigamma : SourceDLMFDigammaIntegral)
    (hCount : SourceCMSZeroCounting) (hEta : SourceDLMFRealEtaIntegral)
    (hMV : SourceMontgomeryVaughan) (hRH : RiemannHypothesis)
    (hUniform : BRFourierInput.v1.uniform_population_q1)
include hBRNorm hBR hCMS hDigamma hCount hEta hMV hRH hUniform

/-- The exact original support-seven provider and both completed16-node C
programs give an attained eventual good coefficient at every density. The
common named source propositions remain explicit; no onset is inferred. -/
theorem source_three_curve (α : ℝ) (hα : 0≤α) :
    GoodCoefficient α (min (w4 α) (min (sparse α) (flat α))) := by
  have w : GoodCoefficient α (w4 α) := by
    have line : w4 α=RH080Next.ExplicitProfiles.w4RecordedPopulationWidth α := by
      norm_num [w4,RH080Next.ExplicitProfiles.w4RecordedPopulationWidth]
    rw [line]
    exact RH080Next.FFTPV.W4Main.source_w4_population hBRNorm hBR hCMS hDigamma hCount hEta hMV hRH α hα
  have s : GoodCoefficient α (sparse α) := by
    simpa only [sparse,RHWeightedPopulation.v1.sparseLine] using
      RH080Next.PopulationCanonical.source_first_sparse_curve hBRNorm hUniform hRH α hα
  have f : GoodCoefficient α (flat α) := by
    simpa only [flat,RHWeightedPopulation.v1.flatLine] using
      RH080Next.PopulationCanonical.source_first_flat_curve hBRNorm hUniform hRH α hα
  exact good_min w (good_min s f)

/-- A genuine RH population coefficient, obtained from actual source-verified
program providers, is strictly below BOTH printed BRv2 lines at each alpha.
This does not assert superiority to Lee or any globally best-known result. -/
theorem actual_coefficient_below_both_printed_lines (α : ℝ) (hα : 0≤α) :
    ∃c : ℝ,GoodCoefficient α c ∧ c<min (paperFirst α) (paperSecond α) :=
  ⟨_,source_three_curve hBRNorm hBR hCMS hDigamma hCount hEta hMV hRH hUniform α hα,
    three_curve_lt_printed_minimum α hα⟩

end LiteralInputs
end RH080Next.PopulationEnvelope
