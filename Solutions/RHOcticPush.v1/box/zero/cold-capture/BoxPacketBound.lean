import BoxZeroPacket
import BoxTransportMajorant

/-! A pointwise estimate for the actual complex Box packet, for either sign of
the zero ordinate. The small-ordinate branch is handled separately by the
proved zero-order fact in the full-family pairing theorem. -/
namespace RHOcticPush.BoxZero
open Real Complex Set MeasureTheory IEANTN.RHSmoothing
set_option maxHeartbeats 0

lemma H_conjugate (e y : ℝ) :
    H e (-y) = starRingEnd ℂ (H e y) := by
  unfold H
  rw [← intervalIntegral.intervalIntegral_conj]
  apply intervalIntegral.integral_congr
  intro u _
  dsimp only
  simp only [map_mul, Complex.conj_ofReal, phase, ← Complex.exp_conj,
    map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg]
  congr 2
  ring

lemma shift_norm_abs (e y : ℝ) :
    ‖H e y - (F y : ℂ)‖ = ‖H e |y| - (F |y| : ℂ)‖ := by
  by_cases hy : 0 ≤ y
  · rw [abs_of_nonneg hy]
  · rw [abs_of_neg (lt_of_not_ge hy), H_conjugate, F_neg]
    rw [show (F y : ℂ) = starRingEnd ℂ (F y : ℂ) by simp]
    rw [← map_sub, Complex.norm_conj]
    simp only [Complex.conj_ofReal]

lemma shifted_div_bound {d t : ℝ} (hd : 0 < d) (ht : 12 < |t|) :
    ‖H (d/2) (t*d)‖ / |t| ≤ Real.exp (d/2) * transportMajorant d t := by
  have ht0 : 0 < |t| := by linarith
  have he : 1 ≤ Real.exp (d/2) := Real.one_le_exp (by positivity)
  have hf : ‖(F (t*d) : ℂ)‖ = |F (d*t)| := by
    rw [Complex.norm_real, Real.norm_eq_abs, mul_comm t d]
  have hn : ‖H (d/2) (t*d)‖ ≤
      ‖H (d/2) (t*d) - (F (t*d) : ℂ)‖ + |F (d*t)| := by
    simpa only [sub_add_cancel, hf] using
      norm_add_le (H (d/2) (t*d) - (F (t*d) : ℂ)) (F (t*d) : ℂ)
  have hk : |kernel d t| = |F (d*t)| / |t| := by rw [kernel, abs_div]
  by_cases hc : |t| ≤ 32768
  · have hs := shift_global (y := t*d) (show 0 ≤ d/2 by positivity)
    have hb : ‖H (d/2) (t*d)‖ ≤ Real.exp (d/2) *
        (|F (d*t)| + |t| * (d/48)) := by
      have hm := mul_le_mul_of_nonneg_left ht.le (by positivity : 0 ≤ d*Real.exp (d/2))
      have hh := mul_le_mul_of_nonneg_right he (abs_nonneg (F (d*t)))
      nlinarith
    apply (div_le_iff₀ ht0).mpr
    rw [transportMajorant, if_pos hc, hk]
    calc
      _ ≤ Real.exp (d/2) * (|F (d*t)| + |t| *(d/48)) := hb
      _ = _ := by field_simp <;> ring
  · have hy : 0 < |t*d| := by rw [abs_mul, abs_of_pos hd]; positivity
    have hs := shift_tail (show 0 ≤ d/2 by positivity) hy
    rw [← shift_norm_abs] at hs
    rw [abs_mul, abs_of_pos hd] at hs
    have hh : 2*(d/2)*Real.exp (d/2)/(|t| *d) = Real.exp (d/2)/|t| := by
      field_simp
      <;> ring
    rw [hh] at hs
    have hb : ‖H (d/2) (t*d)‖ ≤ Real.exp (d/2) *
        (|F (d*t)| + 1/|t|) := by
      have hh := mul_le_mul_of_nonneg_right he (abs_nonneg (F (d*t)))
      simp only [mul_add, mul_one_div]
      linarith
    apply (div_le_iff₀ ht0).mpr
    rw [transportMajorant, if_neg hc, hk]
    calc
      _ ≤ Real.exp (d/2) * (|F (d*t)| + 1/|t|) := hb
      _ = _ := by rw [← sq_abs t]; field_simp <;> ring

/-- The original packet, including its multiplicity and its complex denominator. -/
theorem actual_packet_majorant (rh : RiemannHypothesis) {s L : ℝ}
    (hd : 0 < delta L) (hs : s ≤ 1) (z : IEANTN.RHSmoothing.Zero)
    (hz : 12 < |z.val.im|) :
    ‖IEANTN.RHSmoothing.zeroPacket box s L z‖ ≤
      (Real.exp (L/2) * Real.exp (delta L)) *
        transportMajorant (delta L) z.val.im * (IEANTN.zetaOrder z.val : ℝ) := by
  have ht0 : 0 < |z.val.im| := by linarith
  have ho : (0 : ℝ) ≤ IEANTN.zetaOrder z.val := by
    exact_mod_cast RHOcticPush.Convergence.order_nonneg z
  have hnorm := Complex.abs_im_le_norm (z : ℂ)
  have hdiv := div_le_div_of_nonneg_left
    (norm_nonneg (H (delta L/2) (z.val.im*delta L))) ht0 hnorm
  have hb := hdiv.trans (shifted_div_bound hd hz)
  have he : Real.exp (s*delta L/2) ≤ Real.exp (delta L/2) :=
    Real.exp_le_exp.mpr (by nlinarith)
  rw [packet_norm_exact rh]
  calc
    _ = Real.exp (L/2) * Real.exp (s*delta L/2) *
        (‖H (delta L/2) (z.val.im*delta L)‖ / ‖(z : ℂ)‖) *
          (IEANTN.zetaOrder z.val : ℝ) := by ring
    _ ≤ Real.exp (L/2) * Real.exp (delta L/2) *
        (Real.exp (delta L/2) * transportMajorant (delta L) z.val.im) *
          (IEANTN.zetaOrder z.val : ℝ) := by
      gcongr
    _ = _ := by
      have hee : Real.exp (delta L/2)*Real.exp (delta L/2) = Real.exp (delta L) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        _ = Real.exp (L/2) * (Real.exp (delta L/2)*Real.exp (delta L/2)) *
            transportMajorant (delta L) z.val.im * (IEANTN.zetaOrder z.val : ℝ) := by ring
        _ = _ := by rw [hee]

#print axioms shifted_div_bound
#print axioms actual_packet_majorant
end RHOcticPush.BoxZero
