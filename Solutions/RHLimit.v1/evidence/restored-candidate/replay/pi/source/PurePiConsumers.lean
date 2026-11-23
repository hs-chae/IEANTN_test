/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import PurePiBounds
import NetworkConsumers
import IEANTN.Vocabulary.ErrorTerms

/-! Actual ordinary-prime bounds. All published source predicates remain visible.
The prime-power correction is proved unconditionally, not supplied as data. -/
namespace RHLimit.PurePi
open Real IEANTN RHContinuation.Ramanujan
set_option maxHeartbeats 0

/-- Normalization of the completely elementary bound; no prime-counting
function occurs on its right-hand side. -/
noncomputable def normalized (f : ℝ → ℝ) (L : ℝ) : ℝ :=
  L / exp (L/2) * (envelope f L + 2)

theorem actual_Epi_elementary
    (hRH : SharedRH.hypothesis) (hGM : GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi) (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (f : ℝ → ℝ) {L : ℝ} (hL : 12 ≤ L)
    (hpsi : |Chebyshev.psi (exp L)-exp L| ≤ sqrt (exp L)*f L) :
    Eπ (exp L) ≤ normalized f L * exp (-L/2) := by
  have hb := actual_pi_Li_elementary hRH hGM hP hJ f hL hpsi
  have hL0 : 0 < L := by linarith
  have hs : exp L = exp (L/2) * exp (L/2) := by
    rw [← exp_add]
    congr 1
    ring
  have hn : exp (-L/2) = (exp (L/2))⁻¹ := by
    rw [show -L/2 = -(L/2) by ring, exp_neg]
  unfold Eπ
  rw [log_exp]
  apply (div_le_iff₀ (div_pos (exp_pos L) hL0)).mpr
  calc
    |primeCounting (exp L)-Li (exp L)| ≤ envelope f L+2 := hb
    _ = normalized f L * exp (-L/2) * (exp L/L) := by
      unfold normalized
      rw [hs, hn]
      field_simp [hL0.ne', exp_ne_zero]

/-- The eight unchanged CH source inputs plus RH, the literal GM primitive,
and the two original Büthe anchors give a closed elementary ordinary-pi bound. -/
theorem ch_pi
    (rh : SharedRH.hypothesis)
    (hk : ZetaLogDerivValues.v1.logDeriv_laurent_alternating)
    (hn : ZetaLogDerivValues.v1.logDeriv_neg_one)
    (h2 : ZetaLogDerivValues.v1.logDeriv_two)
    (hv : ZetaLogDerivValues.v1.logDeriv_three_halves)
    (hc : CotangentSeries.v1.cot_series_zeta_values)
    (hr : ZeroCount.v1.rvm_error_bound) (hs : ZeroCount.v1.rvm_error_small)
    (hh : ZetaHadamard.v1.logDeriv_partial_fractions)
    (hGM : GM_Q_Theorem1_1) (hP : Buthe.v1.theorem_2_psi)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    {L : ℝ} (hL : 34 ≤ L) :
    |primeCounting (exp L)-IEANTN.Li (exp L)| ≤ envelope RHSmoothing.chBound L+2 := by
  have hp := RHContinuation.Network.recovered_ch_psi rh hk hn h2 hv hc hr hs hh
    (exp L) (exp_le_exp.mpr hL)
  rw [log_exp, mul_comm] at hp
  exact actual_pi_Li_elementary rh hGM hP hJ RHSmoothing.chBound (by linarith) hp

theorem ch_Epi
    (rh : SharedRH.hypothesis)
    (hk : ZetaLogDerivValues.v1.logDeriv_laurent_alternating)
    (hn : ZetaLogDerivValues.v1.logDeriv_neg_one)
    (h2 : ZetaLogDerivValues.v1.logDeriv_two)
    (hv : ZetaLogDerivValues.v1.logDeriv_three_halves)
    (hc : CotangentSeries.v1.cot_series_zeta_values)
    (hr : ZeroCount.v1.rvm_error_bound) (hs : ZeroCount.v1.rvm_error_small)
    (hh : ZetaHadamard.v1.logDeriv_partial_fractions)
    (hGM : GM_Q_Theorem1_1) (hP : Buthe.v1.theorem_2_psi)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    {L : ℝ} (hL : 34 ≤ L) :
    Eπ (exp L) ≤ normalized RHSmoothing.chBound L * exp (-L/2) := by
  have hp := RHContinuation.Network.recovered_ch_psi rh hk hn h2 hv hc hr hs hh
    (exp L) (exp_le_exp.mpr hL)
  rw [log_exp, mul_comm] at hp
  exact actual_Epi_elementary rh hGM hP hJ RHSmoothing.chBound (by linarith) hp

/-- The actual box PNT provider propagates through the same ordinary-pi proof. -/
theorem box_Epi_from_moments
    (rh : SharedRH.hypothesis)
    (hef : RHSmoothingInputs.v1.box_explicit_formula)
    (hz : RHSmoothingInputs.v1.box_zero_estimate)
    (hm : RHSmoothingInputs.v1.box_moments)
    (hGM : GM_Q_Theorem1_1) (hP : Buthe.v1.theorem_2_psi)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    {L : ℝ} (hL : 35 ≤ L) :
    Eπ (exp L) ≤ normalized RHSmoothing.fastBound L * exp (-L/2) := by
  have hp := RHContinuation.Network.box_psi rh hef hz hm (exp L) (exp_le_exp.mpr hL)
  rw [log_exp] at hp
  exact actual_Epi_elementary rh hGM hP hJ RHSmoothing.fastBound (by linarith) hp

#print axioms actual_Epi_elementary
#print axioms ch_pi
#print axioms ch_Epi
#print axioms box_Epi_from_moments
end RHLimit.PurePi
