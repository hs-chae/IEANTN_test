/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import HighAnchorIntervalA.LowProgram

namespace HighAnchorIntervalA
open Real Set MeasureTheory

noncomputable def lowLog (L : ℝ) : ℝ := eta * L + log ((6000/23 : ℝ) * L)

theorem low_eq_explicit {L : ℝ} (hL : 330 ≤ L) :
    low L = 2 * k * exp (-L/25) * (lowLog L + lowLog L ^ (2 : ℕ)/2) := by
  have hLpos : 0 < L := by linarith
  have hV : V L = ((6000/23 : ℝ) * L) * exp (eta * L) := by unfold V truncHeight; ring
  unfold low lowLog
  rw [hV, Real.log_mul (by positivity) (exp_pos _).ne', Real.log_exp]
  ring

theorem lowLog_deriv {L : ℝ} (hL : 0 < L) :
    HasDerivAt lowLog (eta + 1/L) L := by
  have hd₁ := (hasDerivAt_id L).const_mul eta
  have hd₂ := ((hasDerivAt_id L).const_mul (6000/23 : ℝ)).log (by positivity)
  convert! hd₁.add hd₂ using 1 <;> dsimp [lowLog]
  all_goals field_simp
  all_goals ring

theorem low_antitoneOn : AntitoneOn low (Ici (330 : ℝ)) := by
  let f : ℝ → ℝ := fun L ↦
    2 * k * exp (-L/25) * (lowLog L + lowLog L ^ (2 : ℕ)/2)
  let d : ℝ → ℝ := fun L ↦ 2 * k * exp (-L/25) *
    ((eta + 1/L) * (1 + lowLog L) - (lowLog L + lowLog L ^ (2 : ℕ)/2)/25)
  have hder : ∀ L ∈ Ici (330 : ℝ), HasDerivAt f (d L) L := by
    intro L hL
    have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hL
    have hv := lowLog_deriv hLpos
    have he := (((hasDerivAt_id L).neg).div_const (25 : ℝ)).exp
    have hp := hv.add ((hv.pow 2).div_const (2 : ℝ))
    have hd := (he.mul hp).const_mul (2 * k)
    convert! hd using 1 <;> dsimp [f, d] <;> ring
  have hanti : AntitoneOn f (Ici (330 : ℝ)) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici (330 : ℝ))
      (fun L hL ↦ (hder L hL).continuousAt.continuousWithinAt)
      (fun L hL ↦ (hder L (interior_subset hL)).hasDerivWithinAt)
    intro L hL
    have hLL : (330 : ℝ) ≤ L := interior_subset hL
    have hLpos : 0 < L := by linarith
    have hlog : 0 ≤ log ((6000/23 : ℝ) * L) := log_nonneg (by nlinarith)
    have hv : (66 : ℝ) ≤ lowLog L := by unfold lowLog; dsimp [eta]; linarith
    have hInv : (1 : ℝ)/L ≤ 1/2 := by
      apply (div_le_iff₀ hLpos).mpr
      linarith
    have hdv : eta + 1/L ≤ 1 := by dsimp [eta]; linarith
    have hm : (eta + 1/L) * (1 + lowLog L) ≤ 1 + lowLog L := by
      nlinarith [mul_le_mul_of_nonneg_right hdv (show 0 ≤ 1 + lowLog L by linarith)]
    have hs : (eta + 1/L) * (1 + lowLog L) -
        (lowLog L + lowLog L ^ (2 : ℕ)/2)/25 ≤ 0 := by
      nlinarith [mul_nonneg (show 0 ≤ lowLog L - 66 by linarith)
        (show 0 ≤ lowLog L by linarith)]
    exact mul_nonpos_of_nonneg_of_nonpos (by dsimp [k]; positivity) hs
  intro L hL M hM hLM
  rw [low_eq_explicit hM, low_eq_explicit hL]
  exact hanti hL hM hLM

theorem low330_eq_value_real : low 330 = LowNumerical.value_real := by
  rw [low_eq_explicit (by norm_num : (330 : ℝ) ≤ 330)]
  norm_num [lowLog, eta, k, LowNumerical.value_real]

/-- The actual one-row numerical output controls the entire real ray. -/
theorem low_le {L : ℝ} (hL : 330 ≤ L) : low L ≤ (3/100 : ℝ) := by
  have hb : low 330 ≤ (3/100 : ℝ) := by
    rw [low330_eq_value_real]
    exact LowNumerical.value_real_le
  exact (low_antitoneOn (show (330 : ℝ) ∈ Ici 330 by simp) hL hL).trans hb

end HighAnchorIntervalA

#print axioms HighAnchorIntervalA.low_antitoneOn
#print axioms HighAnchorIntervalA.low_le
