/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import PsiBoxExact
import IEANTN.Vocabulary.RHSmoothing

/-! The new robust GM transport beats even the stronger old written spectral
benchmark after the stronger psi provider is consumed. This proves a comparison
of whole certified functions; it neither proves the old .076 analytic branch
nor assumes that branch to establish validity of the new bound. -/
namespace RHContinuation.SpectralBenchmark
open Real

noncomputable def oldCoefficient (L : ℝ) : ℝ :=
  IEANTN.RHSmoothing.envelope (831 / 1000) (287 / 500) L + (19 / 250) / L
noncomputable def newCoefficient (L : ℝ) : ℝ :=
  IEANTN.RHSmoothing.fastBound L + (1386 / 5000) / L

theorem robust_improves_old_spectral {L : ℝ} (hL : 35 ≤ L) :
    (27 / 50 : ℝ) < oldCoefficient L - newCoefficient L := by
  have hL0 : 0 < L := by linarith
  have hbonus := PsiBoxExact.fast_improves_B5 hL
  have hsmall : (503 / 2500 : ℝ) / L ≤ (503 / 2500 : ℝ) / 35 := by
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hL
  have heq : oldCoefficient L - newCoefficient L =
      IEANTN.RHSmoothing.envelope (831 / 1000) (287 / 500) L -
      IEANTN.RHSmoothing.fastBound L - (503 / 2500) / L := by
    unfold oldCoefficient newCoefficient
    ring
  rw [heq]
  change (546 / 1000 : ℝ) <
      IEANTN.RHSmoothing.envelope (831 / 1000) (287 / 500) L -
      IEANTN.RHSmoothing.fastBound L at hbonus
  norm_num at hsmall
  linarith

#print axioms robust_improves_old_spectral
end RHContinuation.SpectralBenchmark
