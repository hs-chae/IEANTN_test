/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ActualGMClosed

namespace RHLimit.Spectral
open Real Set MeasureTheory IEANTN RHContinuation.Ramanujan
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option leancert.trust "kernel"

/-- Variable leading allowance from the complete four-term GM primitive.
Its limiting normalized coefficient is 3*.0462=.1386 rather than .2772. -/
noncomputable def refinedLeading (x : ℝ) : ℝ :=
  (693 / 5000 : ℝ) * sqrt x / (log x * (log x - 6))

noncomputable def refinedAntiderivative (x : ℝ) : ℝ :=
  refinedLeading x - (919 / 500 : ℝ) / log x - gmEnvelope x * gmWeight x

noncomputable def refinedBound (x : ℝ) : ℝ := 361 / 25 + refinedLeading x

lemma refinedAntiderivative_derivative {x : ℝ} (hx : 1 < x)
    (hL : (6 : ℝ) < log x) :
    HasDerivAt refinedAntiderivative
      (gmEnvelope x * gmKernel x +
        (693 / 5000 : ℝ) * (log x - 12) /
          ((log x - 6)^2 * sqrt x * (log x)^2) +
        (5097 / 10000 : ℝ) / (x^3 * (log x)^2)) x := by
  have hx0 : 0 < x := by linarith
  have hxN : x ≠ 0 := hx0.ne'
  have hsN : sqrt x ≠ 0 := (sqrt_pos.mpr hx0).ne'
  have hlN : log x ≠ 0 := by linarith
  have hdN : log x - 6 ≠ 0 := by linarith
  have hlog := hasDerivAt_log hxN
  have hlead := ((hasDerivAt_sqrt hxN).const_mul (693 / 5000 : ℝ)).div
    (hlog.mul (hlog.sub_const 6)) (mul_ne_zero hlN hdN)
  have h := (hlead.sub ((hlog.inv hlN).const_mul (919 / 500 : ℝ))).sub
    ((gmEnvelope_derivative hx0).mul (gmWeight_derivative hx))
  convert! h using 1
  simp only [gmKernel, gmWeight, gmEnvelope, id_eq, mul_one, Pi.mul_apply]
  have he := sq_sqrt hx0.le
  generalize hh : sqrt x = s at *
  generalize hl : log x = l at *
  rw [← he]
  field_simp [hsN, hlN, hdN]
  <;> ring

lemma refined_transport_upper {a b : ℝ} (ha : exp 12 ≤ a) (hab : a ≤ b) :
    gmTransport a b ≤ refinedLeading b - refinedLeading a +
      2 * gmEnvelope a * gmWeight a + (919 / 500 : ℝ) / log a := by
  have ha0 : 0 < a := (exp_pos 12).trans_le ha
  have ha1 : 1 < a := (one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 12)).trans_le ha
  have hL {t : ℝ} (ht : a ≤ t) : (12 : ℝ) ≤ log t := by
    apply exp_le_exp.mp
    simpa only [exp_log (ha0.trans_le ht)] using ha.trans ht
  have hc : ContinuousOn refinedAntiderivative (Set.Icc a b) := by
    intro t ht
    exact (refinedAntiderivative_derivative (ha1.trans_le ht.1)
      (by linarith [hL ht.1])).continuousAt.continuousWithinAt
  have hi : IntegrableOn (fun t => gmEnvelope t * gmKernel t) (Set.Icc a b) :=
    ((gmEnvelope_continuousOn ha0).mul (gmKernel_continuousOn ha1)).integrableOn_Icc
  have h := intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le hab hc
    (fun t ht => (refinedAntiderivative_derivative (ha1.trans ht.1)
      (by linarith [hL ht.1.le])).hasDerivWithinAt) hi
    (fun t ht => by
      have ht0 : 0 < t := by linarith [ht.1]
      have hl0 : 0 < log t := log_pos (ha1.trans ht.1)
      have hl12 := hL ht.1.le
      have hp : 0 ≤ (693 / 5000 : ℝ) * (log t - 12) /
          ((log t - 6)^2 * sqrt t * (log t)^2) := by positivity
      have hp2 : 0 ≤ (5097 / 10000 : ℝ) / (t^3 * (log t)^2) := by positivity
      linarith)
  rw [intervalIntegral.integral_of_le hab] at h
  have hbL : 0 < log b := log_pos (ha1.trans_le hab)
  have hp : 0 ≤ (919 / 500 : ℝ) / log b := by positivity
  unfold gmTransport refinedAntiderivative at *
  linarith

lemma refined_at_anchor :
    refinedLeading (exp 12) = (1386 / 5000 : ℝ) * gmSqrtLog (exp 12) := by
  unfold refinedLeading gmSqrtLog
  simp only [Real.log_exp]
  ring

lemma refined_anchor_allowance :
    2 * gmEnvelope (exp 12) * gmWeight (exp 12) + (919 / 500 : ℝ) / 12 ≤ 11 / 25 := by
  have he : exp (12 : ℝ) = (exp 6)^2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
  have hs : sqrt (exp (12 : ℝ)) = exp 6 := by
    rw [he, Real.sqrt_sq (exp_pos 6).le]
  unfold gmEnvelope gmWeight
  simp only [Real.log_exp, hs]
  interval_decide 80 (trust := kernel) <;> ring

/-- A sharper actual J/psi transfer from exactly the original GM/Büthe inputs.
All source allowance terms and the low anchor remain included. -/
theorem actual_J_refined_GM (hRH : SharedRH.hypothesis) (hGM : GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi) (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    {x : ℝ} (hx : exp 12 ≤ x) :
    |riemannPrimeCounting x - IEANTN.li x - (Chebyshev.psi x - x) / log x| ≤
      refinedBound x := by
  have h12 : (3 : ℝ) ≤ exp 12 := by
    interval_decide 80 (trust := kernel)
  have h812 : exp (8 : ℝ) ≤ exp 12 := Real.exp_le_exp.mpr (by norm_num)
  have h := actual_J_from_GM hRH hGM h12 hx
  have hA := actual_J_closed_GM hRH hGM hP hJ h812
  have hT := refined_transport_upper (a := exp 12) le_rfl hx
  have hB := refined_anchor_allowance
  rw [refined_at_anchor] at hT
  unfold refinedBound
  simp only [Real.log_exp] at hT
  unfold gmSqrtLog at hA hT
  simp only [div_eq_mul_inv, mul_assoc] at h hA hT hB ⊢
  linarith

theorem actual_pi_refined_GM (hRH : SharedRH.hypothesis) (hGM : GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi) (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    {x : ℝ} (hx : exp 12 ≤ x) :
    |primeCounting x - IEANTN.li x - (Chebyshev.psi x - x) / log x +
      (riemannPrimeCounting x - primeCounting x)| ≤ refinedBound x := by
  convert actual_J_refined_GM hRH hGM hP hJ hx using 1 <;> ring

lemma gmSqrtLog_mono_from_exp16 : MonotoneOn gmSqrtLog (Ici (exp 16)) := by
  have hbase : 1 < exp (16 : ℝ) := one_lt_exp_iff.mpr (by norm_num)
  have hd {t : ℝ} (ht : exp 16 ≤ t) := gmSqrtLog_derivative (hbase.trans_le ht)
  apply monotoneOn_of_deriv_nonneg (convex_Ici _)
  · intro t ht
    exact (hd ht).continuousAt.continuousWithinAt
  · intro t ht
    exact (hd (interior_subset ht)).differentiableAt.differentiableWithinAt
  · intro t ht
    have ht16 : exp (16 : ℝ) ≤ t := interior_subset ht
    rw [(hd ht16).deriv]
    have ht0 : 0 < t := (exp_pos 16).trans_le ht16
    have ht1 : 1 < t := hbase.trans_le ht16
    have hl0 : 0 < log t := log_pos ht1
    have hl16 : (16 : ℝ) ≤ log t := by
      apply exp_le_exp.mp
      simpa only [exp_log ht0] using ht16
    have hq : 2 / log t ≤ (1 / 2 : ℝ) :=
      (div_le_iff₀ hl0).mpr (by linarith)
    exact div_nonneg (by linarith) (by positivity)

lemma strict_gain_at_exp16 :
    (1 / 5 : ℝ) < (693 / 5000 : ℝ) * (2 / 5) * gmSqrtLog (exp 16) - 11 / 25 := by
  have he : exp (16 : ℝ) = (exp 8)^2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
  have hs : sqrt (exp (16 : ℝ)) = exp 8 := by
    rw [he, Real.sqrt_sq (exp_pos 8).le]
  unfold gmSqrtLog
  simp only [Real.log_exp, hs]
  interval_decide 80 (trust := kernel) <;> ring

/-- Strict whole-ray gain over the preceding robust GM bound. The new bound
is valid from exp12; strict dominance is asserted only from exp16. -/
theorem refined_strictly_improves_old {x : ℝ} (hx : exp 16 ≤ x) :
    (1 / 5 : ℝ) < (14 + (1386 / 5000 : ℝ) * gmSqrtLog x) - refinedBound x := by
  have hx0 : 0 < x := (exp_pos 16).trans_le hx
  have hL : (16 : ℝ) ≤ log x := by
    apply exp_le_exp.mp
    simpa only [exp_log hx0] using hx
  have hl0 : log x ≠ 0 := by linarith
  have hd0 : 0 < log x - 6 := by linarith
  have hr : (2 / 5 : ℝ) ≤ (log x - 12) / (log x - 6) :=
    (le_div_iff₀ hd0).mpr (by linarith)
  have hp := gmSqrtLog_mono_from_exp16 (by simp) hx hx
  have hP : 0 ≤ gmSqrtLog (exp 16) := by unfold gmSqrtLog; positivity
  have hR : 0 ≤ (log x - 12) / (log x - 6) := by positivity
  have hprod := mul_le_mul hr hp hP hR
  have hscaled := mul_le_mul_of_nonneg_left hprod (show 0 ≤ (693 / 5000 : ℝ) by norm_num)
  have he : (14 + (1386 / 5000 : ℝ) * gmSqrtLog x) - refinedBound x =
      (693 / 5000 : ℝ) * ((log x - 12) / (log x - 6)) * gmSqrtLog x - 11 / 25 := by
    unfold refinedBound refinedLeading gmSqrtLog
    field_simp [hl0, hd0.ne']
    <;> ring
  rw [he]
  have hs := strict_gain_at_exp16
  nlinarith

theorem actual_J_refined_from_psi_profile (hRH : SharedRH.hypothesis)
    (hGM : GM_Q_Theorem1_1) (hP : Buthe.v1.theorem_2_psi)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (f : ℝ → ℝ) {x : ℝ} (hx : exp 12 ≤ x)
    (hpsi : |Chebyshev.psi x - x| ≤ sqrt x * f (log x)) :
    |riemannPrimeCounting x - IEANTN.li x| ≤
      sqrt x / log x * f (log x) + refinedBound x := by
  have hx1 : 1 < x := (one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 12)).trans_le hx
  have hl : 0 < log x := log_pos hx1
  have ht := actual_J_refined_GM hRH hGM hP hJ hx
  have hD : |(Chebyshev.psi x - x) / log x| ≤ sqrt x / log x * f (log x) := by
    rw [abs_div, abs_of_pos hl]
    have h := div_le_div_of_nonneg_right hpsi hl.le
    calc _ ≤ _ := h
      _ = _ := by ring
  have htri := abs_add_le
    (riemannPrimeCounting x - IEANTN.li x - (Chebyshev.psi x - x) / log x)
    ((Chebyshev.psi x - x) / log x)
  simp only [sub_add_cancel] at htri
  linarith

theorem actual_pi_signed_refined_profile (hRH : SharedRH.hypothesis)
    (hGM : GM_Q_Theorem1_1) (hP : Buthe.v1.theorem_2_psi)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (f : ℝ → ℝ) {x : ℝ} (hx : exp 12 ≤ x)
    (hpsi : |Chebyshev.psi x - x| ≤ sqrt x * f (log x)) :
    -(sqrt x / log x * f (log x) + refinedBound x) -
      (riemannPrimeCounting x - primeCounting x) ≤ primeCounting x - IEANTN.li x ∧
    primeCounting x - IEANTN.li x ≤
      sqrt x / log x * f (log x) + refinedBound x -
        (riemannPrimeCounting x - primeCounting x) := by
  have h := actual_J_refined_from_psi_profile hRH hGM hP hJ f hx hpsi
  rw [abs_le] at h
  constructor <;> linarith [h.1, h.2]

theorem actual_pi_absolute_Li_refined_profile (hRH : SharedRH.hypothesis)
    (hGM : GM_Q_Theorem1_1) (hP : Buthe.v1.theorem_2_psi)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (f : ℝ → ℝ) {x : ℝ} (hx : exp 12 ≤ x)
    (hpsi : |Chebyshev.psi x - x| ≤ sqrt x * f (log x)) :
    |primeCounting x - IEANTN.Li x| ≤
      sqrt x / log x * f (log x) + refinedBound x +
        |IEANTN.li 2 - (riemannPrimeCounting x - primeCounting x)| := by
  have hx1 : 1 < x := (one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 12)).trans_le hx
  have h := actual_J_refined_from_psi_profile hRH hGM hP hJ f hx hpsi
  have hli := actual_li_Li_offset hx1
  have he : primeCounting x - IEANTN.Li x = (riemannPrimeCounting x - IEANTN.li x) +
      (IEANTN.li 2 - (riemannPrimeCounting x - primeCounting x)) := by linarith
  rw [he]
  exact (abs_add_le _ _).trans (by linarith)

#print axioms actual_J_refined_GM
#print axioms actual_pi_refined_GM
#print axioms refined_transport_upper
#print axioms refined_anchor_allowance
#print axioms refined_strictly_improves_old
#print axioms actual_J_refined_from_psi_profile
#print axioms actual_pi_signed_refined_profile
#print axioms actual_pi_absolute_Li_refined_profile
end RHLimit.Spectral
