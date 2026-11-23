import SpectralGMRefined

namespace RHOcticPush.GM
open Real Set MeasureTheory IEANTN RHContinuation.Ramanujan
set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable def leading (b x : ℝ) : ℝ :=
  (693 / 5000 : ℝ) * sqrt x / (log x * (log x - b))

noncomputable def antiderivative (b x : ℝ) : ℝ :=
  leading b x - (919 / 500 : ℝ) / log x - gmEnvelope x * gmWeight x

lemma derivative {b x : ℝ} (hx : 1 < x) (hL : b < log x) (hlog : 0 < log x) :
    HasDerivAt (antiderivative b)
      (gmEnvelope x * gmKernel x +
        (693 / 10000 : ℝ) * ((b - 4) * log x + 2 * b - b ^ 2) /
          ((log x - b) ^ 2 * sqrt x * (log x) ^ 2) +
        (5097 / 10000 : ℝ) / (x ^ 3 * (log x) ^ 2)) x := by
  have hx0 : 0 < x := by linarith
  have hxN : x ≠ 0 := hx0.ne'
  have hsN : sqrt x ≠ 0 := (sqrt_pos.mpr hx0).ne'
  have hlN : log x ≠ 0 := hlog.ne'
  have hdN : log x - b ≠ 0 := by linarith
  have hlog' := hasDerivAt_log hxN
  have hlead := ((hasDerivAt_sqrt hxN).const_mul (693 / 5000 : ℝ)).div
    (hlog'.mul (hlog'.sub_const b)) (mul_ne_zero hlN hdN)
  have h := (hlead.sub ((hlog'.inv hlN).const_mul (919 / 500 : ℝ))).sub
    ((gmEnvelope_derivative hx0).mul (gmWeight_derivative hx))
  convert! h using 1
  simp only [antiderivative, leading, gmKernel, gmWeight, gmEnvelope,
    id_eq, mul_one, Pi.mul_apply]
  have he := sq_sqrt hx0.le
  generalize hh : sqrt x = s at *
  generalize hl : log x = l at *
  rw [← he]
  field_simp [hsN, hlN, hdN]
  <;> ring

lemma transport_upper {b H a z : ℝ} (hb : 4 ≤ b) (hH : b < H)
    (hpoly : 0 ≤ (b - 4) * H + 2 * b - b ^ 2)
    (ha : exp H ≤ a) (haz : a ≤ z) :
    gmTransport a z ≤ leading b z - leading b a +
      2 * gmEnvelope a * gmWeight a + (919 / 500 : ℝ) / log a := by
  have hH0 : 0 < H := by linarith
  have ha0 : 0 < a := (exp_pos H).trans_le ha
  have ha1 : 1 < a := (one_lt_exp_iff.mpr hH0).trans_le ha
  have hlog {t : ℝ} (ht : a ≤ t) : H ≤ log t := by
    apply exp_le_exp.mp
    simpa only [exp_log (ha0.trans_le ht)] using ha.trans ht
  have hc : ContinuousOn (antiderivative b) (Set.Icc a z) := by
    intro t ht
    exact (derivative (ha1.trans_le ht.1) (by linarith [hlog ht.1])
      (by linarith [hlog ht.1])).continuousAt.continuousWithinAt
  have hi : IntegrableOn (fun t => gmEnvelope t * gmKernel t) (Set.Icc a z) :=
    ((gmEnvelope_continuousOn ha0).mul (gmKernel_continuousOn ha1)).integrableOn_Icc
  have h := intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le haz hc
    (fun t ht => (derivative (ha1.trans ht.1) (by linarith [hlog ht.1.le])
      (by linarith [hlog ht.1.le])).hasDerivWithinAt) hi
    (fun t ht => by
      have ht0 : 0 < t := by linarith [ht.1]
      have hl0 : 0 < log t := log_pos (ha1.trans ht.1)
      have hp : 0 ≤ (b - 4) * log t + 2 * b - b ^ 2 := by
        have hm := mul_nonneg (sub_nonneg.mpr hb)
          (sub_nonneg.mpr (hlog ht.1.le))
        nlinarith
      have hp1 : 0 ≤ (693 / 10000 : ℝ) * ((b - 4) * log t + 2 * b - b ^ 2) /
          ((log t - b) ^ 2 * sqrt t * (log t) ^ 2) := by positivity
      have hp2 : 0 ≤ (5097 / 10000 : ℝ) / (t ^ 3 * (log t) ^ 2) := by positivity
      linarith)
  rw [intervalIntegral.integral_of_le haz] at h
  have hzL : 0 < log z := log_pos (ha1.trans_le haz)
  have hp : 0 ≤ (919 / 500 : ℝ) / log z := by positivity
  unfold gmTransport antiderivative at *
  linarith

noncomputable def anchorConstant (b H : ℝ) : ℝ :=
  RHLimit.Spectral.refinedBound (exp H) - leading b (exp H) +
    2 * gmEnvelope (exp H) * gmWeight (exp H) + (919 / 500 : ℝ) / H

/-- Actual J compensation, with exactly the original RH, GM and two Büthe inputs.
The scalar b,H conditions are proved separately for every installed provider. -/
theorem actual_J_anchored (hRH : SharedRH.hypothesis) (hGM : GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi) (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    {b H x : ℝ} (hb : 4 ≤ b) (hH : b < H) (h12 : 12 ≤ H)
    (hpoly : 0 ≤ (b - 4) * H + 2 * b - b ^ 2) (hx : exp H ≤ x) :
    |riemannPrimeCounting x - IEANTN.li x - (Chebyshev.psi x - x) / log x| ≤
      anchorConstant b H + leading b x := by
  have h3 : (3 : ℝ) ≤ exp (12 : ℝ) := by interval_decide 80 (trust := kernel)
  have hbase : exp (12 : ℝ) ≤ exp H := exp_le_exp.mpr h12
  have h := actual_J_from_GM hRH hGM (h3.trans hbase) hx
  have hA := RHLimit.Spectral.actual_J_refined_GM hRH hGM hP hJ hbase
  have hT := transport_upper hb hH hpoly (a := exp H) le_rfl hx
  unfold anchorConstant
  simp only [Real.log_exp] at hT
  linarith

lemma anchor5_upper : anchorConstant 5 15 < (1551 / 100 : ℝ) := by
  unfold anchorConstant RHLimit.Spectral.refinedBound RHLimit.Spectral.refinedLeading
    leading gmEnvelope gmWeight
  simp only [Real.log_exp, ← Real.exp_half]
  interval_decide 80 (trust := kernel) <;> ring

/-- A strictly smaller leading whole function, with its actual anchor cost paid. -/
theorem actual_J_b5 (hRH : SharedRH.hypothesis) (hGM : GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi) (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    {x : ℝ} (hx : exp 15 ≤ x) :
    |riemannPrimeCounting x - IEANTN.li x - (Chebyshev.psi x - x) / log x| ≤
      (1551 / 100 : ℝ) + leading 5 x := by
  have h := actual_J_anchored hRH hGM hP hJ (b := 5) (H := 15)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hx
  linarith [anchor5_upper]

#print axioms derivative
#print axioms transport_upper
#print axioms actual_J_anchored
#print axioms actual_J_b5
end RHOcticPush.GM
