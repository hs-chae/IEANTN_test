/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Nodes.OpenAIQRH.v1.Conclusions
import IEANTN.Nodes.CH2.v6.Conclusions
import IEANTN.Nodes.CH2.v1.Conclusions
import IEANTN.Nodes.PlattTrudgian.v1.Conclusions

/-! New versions preserve the initial QRHCH2.v1 contracts. Analytic inputs remain explicit. -/
namespace QRHCH2.v2

/-- A factor 12 smaller than the initial coefficient, with the same source inputs and threshold. -/
def psi_paired_bound : Prop :=
  ∀ x : ℝ, Real.exp 128 ≤ x →
    IEANTN.Eψ x ≤ (1 / 384) * Real.log x ^ (2 : ℕ) * x ^ (-(1 : ℝ) / 8)

/-- Density-enhanced frontier. In particular `C=0.01310` above `exp 300`. -/
def psi_density_frontier : Prop :=
  ∀ L C : ℝ, (L, C) ∈ CH2.v6.densityFrontier → ∀ x : ℝ, Real.exp L ≤ x →
    IEANTN.Eψ x ≤ C * x ^ (-(1 : ℝ) / 8)

/-- Keep the original CH2 allowance whenever it is smaller. -/
def psi_density_hybrid : Prop :=
  ∀ L C : ℝ, (L, C) ∈ CH2.v6.densityFrontier → ∀ x : ℝ,
    1 ≤ x → Real.exp L ≤ x → IEANTN.Eψ x ≤
      min (Real.pi / (3 * (10 : ℝ) ^ (12 : ℕ)) + 113.67 / Real.sqrt x)
        (C * x ^ (-(1 : ℝ) / 8))

end QRHCH2.v2
