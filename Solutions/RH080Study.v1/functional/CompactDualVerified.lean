/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import CompactDualContinuum
import DualSineGridBridge

set_option autoImplicit false
noncomputable section
open Real Set MeasureTheory
open scoped FourierTransform
namespace RH080.Dual

lemma compact_numerator_model_identity : compactNumerator = RH080PV.Grid.trigNumerator := by
  funext x
  unfold compactNumerator RH080PV.Grid.trigNumerator RH080PV.Grid.coefficient
  apply Finset.sum_congr rfl
  intro j hj
  have hcoef : (jumpCoeff j : ℝ) = (RH080PV.Model.positiveJump (j+1) : ℝ) -
      (RH080PV.Model.negativeJump (j+1) : ℝ) := by
    have hj' : j < 20 := Finset.mem_range.mp hj
    interval_cases j <;> norm_num [jumpCoeff, height,
      RH080PV.Model.positiveJump, RH080PV.Model.negativeJump]
  rw [hcoef]

/-- Generic application bridge. A source-first proof supplies integer caps through
the actual source-run/max correspondence. An ordinary kernel-only model cap can
also instantiate this lemma, but is explicitly a different verification route. -/
theorem compact_grid_from_integer_caps
    (hcap : ∀ k : Fin 257, RH080PV.Model.sampleBound k.val ≤ 1221161) :
    ∀ k : ℕ, k ≤ 256 →
      |cosineTransform compactStep ((k : ℝ)/128)| ≤ (611/500 : ℝ) := by
  intro k hk
  by_cases hz : k = 0
  · subst k
    norm_num [compact_kernel_zero]
  · have hpos : 0 < (k : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hz)
    have hx : (k : ℝ)/128 ≠ 0 := by positivity
    rw [compact_kernel_sine _ hx, compact_numerator_model_identity]
    let index : Fin 257 := ⟨k, by omega⟩
    have hreal := RH080PV.Grid.true_grid_samples index hz
    have hnum := hcap index
    have hc : (RH080PV.Model.sampleBound k : ℝ) ≤ 1221161 := by exact_mod_cast hnum
    have hh : |RH080PV.Grid.trigNumerator ((k : ℝ)/128)/(π*(k : ℝ)/128)| ≤
      (RH080PV.Model.sampleBound k : ℝ)/1000000 := by simpa [index] using hreal
    rw [show π*((k : ℝ)/128) = π*(k : ℝ)/128 by ring]
    linarith

/-- Complete kernel-only numerical/analytic route, explicitly NOT source-first PV.
It is kept separate so the final C-linked proof must consume its own source cap. -/
theorem kernel_compact_global :
    ∀ x : ℝ, |cosineTransform compactStep x| ≤ (123/100 : ℝ) :=
  compact_kernel_global_of_grid
    (compact_grid_from_integer_caps RH080PV.Model.sampleBound_all)

/-- No positive-denominator L1-Fourier witness in the fixed A=36/11 functional
has coefficient at most 0.8. This is an unconditional Fourier-framework result,
not a lower bound on actual prime gaps and not a claim about other analytic methods. -/
theorem kernel_compact_obstruction
    (F G : ℝ → ℝ) (hF : Integrable F) (hG : Integrable G) (hcont : Continuous F)
    (hfourier : 𝓕 (fun x : ℝ => (F x : ℂ)) = fun v : ℝ => (G v : ℂ))
    (hden : 0 < F 0-(36/11 : ℝ)*(∫ v in exterior, max 0 (G v))) :
    (4/5 : ℝ) < (∫ x : ℝ, |F x|) /
      (F 0-(36/11 : ℝ)*(∫ v in exterior, max 0 (G v))) :=
  compact_functional_obstruction
    (compact_grid_from_integer_caps RH080PV.Model.sampleBound_all)
    F G hF hG hcont hfourier hden

#print axioms kernel_compact_global
#print axioms kernel_compact_obstruction
end RH080.Dual
