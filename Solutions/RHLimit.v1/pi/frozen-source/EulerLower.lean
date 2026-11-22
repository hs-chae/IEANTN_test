/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace EulerLower
open Real Filter Set
open scoped Topology
set_option maxHeartbeats 0
set_option Elab.async false
set_option maxRecDepth 100000

theorem log_trapezoid {x : ℝ} (hx : 1 ≤ x) : Real.log x ≤ (x - x⁻¹) / 2 := by
  let f : ℝ → ℝ := fun t => (t - t⁻¹) / 2 - Real.log t
  have der {t : ℝ} (ht : 0 < t) :
      HasDerivAt f ((1 + t⁻¹ ^ 2) / 2 - t⁻¹) t := by
    have h := (((hasDerivAt_id t).sub (hasDerivAt_inv ht.ne')).div_const 2).sub
      (Real.hasDerivAt_log ht.ne')
    convert h using 1 <;> (first | rfl | ring)
  have cont : ContinuousOn f (Ici 1) := by
    intro t ht
    exact (der (by have ht1 : 1 ≤ t := ht; linarith)).continuousAt.continuousWithinAt
  have mono : MonotoneOn f (Ici 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 1) cont
    · intro t ht
      have ht1 : 1 < t := by simpa only [interior_Ici, mem_Ioi] using ht
      exact (der (by linarith)).hasDerivWithinAt
    · intro t ht
      have ht1 : 1 < t := by simpa only [interior_Ici, mem_Ioi] using ht
      change 0 ≤ (1 + t⁻¹ ^ 2) / 2 - t⁻¹
      nlinarith [sq_nonneg (t⁻¹ - 1)]
  have h := mono (show (1 : ℝ) ∈ Ici 1 from by simp) hx hx
  dsimp [f] at h
  norm_num at h
  linarith

noncomputable def accelerated (n : ℕ) : ℝ :=
  (harmonic (n + 1) : ℝ) - Real.log (n + 1) - 1 / (2 * (n + 1))

theorem accelerated_mono : Monotone accelerated := by
  apply monotone_nat_of_le_succ
  intro n
  have h1 : (0 : ℝ) < n + 1 := by positivity
  have h2 : (0 : ℝ) < n + 2 := by positivity
  have hr : (1 : ℝ) ≤ (n + 2) / (n + 1) := by
    apply (le_div_iff₀ h1).mpr
    linarith
  have hl := log_trapezoid hr
  have logdiff : Real.log ((n + 2 : ℝ) / (n + 1)) =
      Real.log (n + 2) - Real.log (n + 1) := Real.log_div h2.ne' h1.ne'
  rw [logdiff] at hl
  have alg : accelerated (n + 1) - accelerated n =
      (((n + 2 : ℝ) / (n + 1) - (((n : ℝ) + 2) / ((n : ℝ) + 1))⁻¹) / 2) -
        (Real.log (n + 2) - Real.log (n + 1)) := by
    unfold accelerated
    rw [show n + 1 + 1 = (n + 1) + 1 by omega, harmonic_succ]
    push_cast
    field_simp
    <;> ring
  have : 0 ≤ accelerated (n + 1) - accelerated n := by rw [alg]; linarith
  linarith

theorem accelerated_tendsto : Tendsto accelerated atTop (𝓝 Real.eulerMascheroniConstant) := by
  have h := Real.tendsto_harmonic_sub_log.comp (tendsto_add_atTop_nat 1)
  have hz := (tendsto_const_div_atTop_nhds_zero_nat (1 / 2 : ℝ)).comp
    (tendsto_add_atTop_nat 1)
  convert h.sub hz using 1
  · funext n
    dsimp [accelerated, Function.comp_def]
    push_cast
    field_simp
    <;> ring
  · simp

theorem harmonic_lower (n : ℕ) :
    (harmonic (n + 1) : ℝ) - Real.log (n + 1) - 1 / (2 * (n + 1)) ≤
      Real.eulerMascheroniConstant :=
  accelerated_mono.ge_of_tendsto accelerated_tendsto n

theorem harmonic1024_lower :
    (harmonic 1024 : ℝ) - 10 * Real.log 2 - 1 / 2048 ≤ Real.eulerMascheroniConstant := by
  have h := harmonic_lower 1023
  have idlog : Real.log (1024 : ℝ) = 10 * Real.log 2 := by
    rw [show (1024 : ℝ) = 2 ^ 10 by norm_num, Real.log_pow]
    norm_num
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at h
  simpa [idlog] using h

#print axioms harmonic1024_lower
end EulerLower
