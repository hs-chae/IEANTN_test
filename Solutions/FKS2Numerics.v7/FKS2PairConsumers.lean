/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Nodes.FKS2.v9.Conclusions
import IEANTN.Nodes.FKS2Numerics.v6.Conclusions
import IEANTN.Nodes.FKS2Numerics.v7.Conclusions
open Real IEANTN

namespace FKS2Pair
/-- Normalization inversion on the common positive ray, shared by both consumers. -/
theorem absolute_of_normalized {C : ℝ}
    (h : HasNumericalBound Eπ C (exp 330)) :
    ∀ x ≥ exp 330, |primeCounting x-Li x| ≤ C*(x/log x) := by
  intro x hx
  have hx0 : 0<x := (exp_pos _).trans_le hx
  have hlog : 0<log x := by
    have ht := log_le_log (exp_pos (330:ℝ)) hx
    rw [log_exp] at ht
    linarith
  exact (div_le_iff₀ (div_pos hx0 hlog)).mp (h x hx)
end FKS2Pair

theorem FKS2.v9.challenge_old_absolute_pi (h : FKS2Numerics.v6.old_pi) :
    FKS2.v9.old_absolute_pi := FKS2Pair.absolute_of_normalized h

theorem FKS2.v9.challenge_qrh_absolute_pi (h : FKS2Numerics.v7.qrh_pi) :
    FKS2.v9.qrh_absolute_pi := FKS2Pair.absolute_of_normalized h

theorem FKS2.v9.challenge_paired_absolute_pi
    (hOld : FKS2Numerics.v6.old_pi) (hQRH : FKS2Numerics.v7.qrh_pi) :
    FKS2.v9.paired_absolute_pi :=
  ⟨FKS2.v9.challenge_old_absolute_pi hOld,FKS2.v9.challenge_qrh_absolute_pi hQRH⟩

theorem FKS2.v9.challenge_strict_reconstructed_improvement :
    FKS2.v9.strict_reconstructed_improvement := by
  norm_num [FKS2.v9.strict_reconstructed_improvement]
theorem FKS2.v9.challenge_strict_historical_improvement :
    FKS2.v9.strict_historical_improvement := by
  norm_num [FKS2.v9.strict_historical_improvement]
theorem FKS2.v9.challenge_exact_allowance_ratios :
    FKS2.v9.exact_allowance_ratios := by norm_num [FKS2.v9.exact_allowance_ratios]
