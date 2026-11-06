/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import E1Evolved.PrimeComparison
namespace E1Evolved
open Real IEANTN

theorem matched_prime_ray
    (hs:LambdaEvolutionA.DirectCH2Inputs12)
    (h:WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH:RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH:ZetaZeroFreeHalfPlane (7/8))
    (hCHJII:DirectIntervalA.CHJII_Theorem1_3_Row40) :
    ∀x:ℝ,exp 330≤x→
      HasPrimeInInterval x ((1839254524623/100000000000000:ℝ)*x^(7/8:ℝ)) ∧
      HasPrimeInInterval x ((22/25:ℝ)*x^(79/100:ℝ)) ∧
      (22/25:ℝ)*x^(79/100:ℝ)<
        (1839254524623/100000000000000:ℝ)*x^(7/8:ℝ) := by
  intro x hx
  have hn:=E1FrozenN.prime330 (frozenInputs hs) h hRH hQRH x hx
  have hc:(201/100:ℝ)*(9150520022/1000000000000+1/10^12)=1839254524623/100000000000000 := by norm_num
  rw [hc] at hn
  exact ⟨hn,
    HighAnchorIntervalB.prime_interval_ray hCHJII h hRH hs.hrvm hQRH x hx,
    frozen_prime_width_strict hx⟩

#print axioms matched_prime_ray
end E1Evolved
