/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import E1Evolved.Comparison
import DirectIntervalA.Result
import DirectIntervalA.EvolvedResult
namespace E1Evolved
open Real

theorem selected_new_budget :
    (94/100+3/100+49/2000+1/1000:ℝ)=1991/2000 ∧
    (1991/2000:ℝ)<1 := by norm_num

theorem old_truncation_budget_fails :
    (1:ℝ)<94/100+3/100+49/1000+1/1000 := by norm_num

/-- Restoring the parent's clipping parameter is invalid for the smaller width.
This rejects that construction, not all possible mathematical proofs. -/
theorem old_k_fails_clipping (L:ℝ) :
    HighAnchorIntervalB.delta L*((201/92:ℝ)*exp (HighAnchorIntervalB.eta*L))<2 := by
  have he:exp (-HighAnchorIntervalB.eta*L)*exp (HighAnchorIntervalB.eta*L)=1 := by
    rw [←exp_add]
    convert exp_zero using 1 <;> ring
  calc
    HighAnchorIntervalB.delta L*((201/92:ℝ)*exp (HighAnchorIntervalB.eta*L))=
        (HighAnchorIntervalB.c*(201/92))*(exp (-HighAnchorIntervalB.eta*L)*exp (HighAnchorIntervalB.eta*L)) := by
      unfold HighAnchorIntervalB.delta
      ring
    _ < 2 := by rw [he];norm_num [HighAnchorIntervalB.c]

/-- Reverting to raw512 preserves prime existence. E's factorization gain
concerns its quantitative allowance and cell count. -/
theorem both_C_prime_routes
    (hCHJ:DirectIntervalA.CHJII_Theorem1_3_Row40) (hFKS:FKS.v3.density_0618)
    (hRvM:ZeroCount.v1.rvm_error_bound) (hQRH:IEANTN.ZetaZeroFreeHalfPlane (7/8)) :
    (∀x:ℝ,exp 330≤x→IEANTN.HasPrimeInInterval x (x^(4/5:ℝ))) ∧
    (∀x:ℝ,exp 330≤x→IEANTN.HasPrimeInInterval x (x^(4/5:ℝ))) :=
  ⟨DirectIntervalA.prime_interval_ray hCHJ hFKS hRvM hQRH,
    DirectIntervalA.evolved_prime_interval_ray hCHJ hFKS hRvM hQRH⟩
#print axioms old_k_fails_clipping
#print axioms both_C_prime_routes
end E1Evolved
