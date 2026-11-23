/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitPrimePower
import SpectralGMRefined

namespace RHLimit.PurePi
open Real Set MeasureTheory IEANTN RHContinuation.Ramanujan
open RHLimit.PrimePower RHLimit.Spectral
set_option maxHeartbeats 0

noncomputable def envelope (f : ℝ → ℝ) (L : ℝ) : ℝ :=
  exp (L/2) / L * f L + 361/25 +
    (693/5000:ℝ) * exp (L/2) / (L * (L-6)) + elementaryRemainder L

lemma li_two_bounds : 0 ≤ IEANTN.li 2 ∧ IEANTN.li 2 ≤ 2 := by
  have he := li_pv_regularization (by norm_num : (1:ℝ)<2)
  norm_num [liRegularPrimitive] at he
  have hlo (t : ℝ) : 0 ≤ liRegularPositive t := by
    unfold liRegularPositive
    split_ifs with ht
    · exact (liRegular_bounds ht).1
    · norm_num
  have hup (t : ℝ) : liRegularPositive t ≤ 1 := by
    have h := liRegularPositive_norm t
    rw [Real.norm_eq_abs, abs_of_nonneg (hlo t)] at h
    exact h
  constructor
  · rw [he]
    exact intervalIntegral.integral_nonneg (by norm_num) (fun t ht => hlo t)
  · have h := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ)≤2)
      (liRegularPositive_integrable 0 2)
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1:ℝ)) volume 0 2)
      (fun t ht => hup t)
    rw [he]
    simpa using h

/-- Actual ordinary-prime counting with an elementary RHS containing no J,
pi, prime-power sum, or numerical certificate. Only the printed psi provider
and the existing named GM/Büthe source predicates are parameters. -/
theorem actual_pi_elementary (hRH : SharedRH.hypothesis) (hGM : GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi) (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (f : ℝ → ℝ) {L : ℝ} (hL : 12 ≤ L)
    (hpsi : |Chebyshev.psi (exp L) - exp L| ≤ sqrt (exp L) * f L) :
    |primeCounting (exp L) - IEANTN.li (exp L)| ≤ envelope f L := by
  have hpsi' : |Chebyshev.psi (exp L)-exp L| ≤ sqrt (exp L) * f (log (exp L)) := by
    simpa only [log_exp] using hpsi
  have h := actual_J_refined_from_psi_profile hRH hGM hP hJ f
    (exp_le_exp.mpr hL) hpsi'
  have hQ := actual_remainder_elementary (by linarith : 2 ≤ L)
  have hQ0 := actual_prime_power_nonnegative (exp_pos L)
  have he : primeCounting (exp L) - IEANTN.li (exp L) =
      (riemannPrimeCounting (exp L)-IEANTN.li (exp L)) -
        (riemannPrimeCounting (exp L)-primeCounting (exp L)) := by ring
  rw [he]
  have htri := abs_sub_le (riemannPrimeCounting (exp L)-IEANTN.li (exp L)) (0:ℝ)
    (riemannPrimeCounting (exp L)-primeCounting (exp L))
  simp only [sub_zero, zero_sub, abs_neg] at htri
  rw [abs_of_nonneg hQ0] at htri
  have hs := add_le_add h hQ
  apply htri.trans
  simpa [envelope, refinedBound, refinedLeading, log_exp, sqrt_exp_eq, add_assoc] using hs

theorem actual_pi_Li_elementary (hRH : SharedRH.hypothesis) (hGM : GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi) (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (f : ℝ → ℝ) {L : ℝ} (hL : 12 ≤ L)
    (hpsi : |Chebyshev.psi (exp L)-exp L| ≤ sqrt (exp L)*f L) :
    |primeCounting (exp L)-IEANTN.Li (exp L)| ≤ envelope f L + 2 := by
  have h := actual_pi_elementary hRH hGM hP hJ f hL hpsi
  have hoff := actual_li_Li_offset (one_lt_exp_iff.mpr (by linarith : 0 < L))
  have h2 := li_two_bounds
  have he : primeCounting (exp L)-IEANTN.Li (exp L) =
      (primeCounting (exp L)-IEANTN.li (exp L)) + IEANTN.li 2 := by linarith
  rw [he]
  exact (abs_add_le _ _).trans (by rw [abs_of_nonneg h2.1]; linarith)

#print axioms li_two_bounds
#print axioms actual_pi_elementary
#print axioms actual_pi_Li_elementary
end RHLimit.PurePi
