import SpectralWeightedSum

/-! True full infinite-zero bound after the signed second-primitive cancellation. -/
namespace RHOcticPush.Spectral076
open Real Complex Set MeasureTheory
open RHOcticPush.BoxPerron RHOcticPush.Convergence
set_option maxHeartbeats 0

noncomputable def remainderKernel (t : ℝ) : ℝ := 1/(Real.sqrt t*(Real.log t)^3)
noncomputable def squareAllowance (a b : ℝ) : ℝ :=
  Real.sqrt b/(Real.log b)^2+Real.sqrt a/(Real.log a)^2+
    2*(∫ t in a..b,remainderKernel t)

lemma boundary_norm (rh : RiemannHypothesis) {x : ℝ} (hx : 1 < x)
    (r : IEANTN.RHSmoothing.Zero) :
    ‖squareBoundary x r‖ = (Real.sqrt x/(Real.log x)^2)*weight r := by
  rw [squareBoundary,norm_div,squareWave_norm rh (by linarith : 0 < x),norm_pow,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.log_pos hx)]
  ring

lemma remainder_norm (rh : RiemannHypothesis) {x : ℝ} (hx : 1 < x)
    (r : IEANTN.RHSmoothing.Zero) :
    ‖squareRemainder x r‖ = remainderKernel x*weight r := by
  have hx0 : 0 < x := by linarith
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hl : 0 < Real.log x := Real.log_pos hx
  rw [squareRemainder,norm_div,squareWave_norm rh hx0,norm_mul,norm_pow,
    Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,
    abs_of_pos hx0,abs_of_pos hl]
  unfold remainderKernel
  field_simp
  rw [Real.sq_sqrt hx0.le]
  ring

theorem weighted_zero_norm (rh : RiemannHypothesis) {a b : ℝ}
    (ha : 1 < a) (hab : a ≤ b) (r : IEANTN.RHSmoothing.Zero) :
    ‖weightedTransport a b (fun t => zeroPrimitive t r)‖ ≤ squareAllowance a b*weight r := by
  have hb : 1 < b := ha.trans_le hab
  have hi : ‖∫ t in a..b,squareRemainder t r‖ ≤
      (∫ t in a..b,remainderKernel t)*weight r := by
    calc
      _ ≤ ∫ t in a..b,‖squareRemainder t r‖ :=
        intervalIntegral.norm_integral_le_integral_norm hab
      _ = ∫ t in a..b,remainderKernel t*weight r := by
        apply intervalIntegral.integral_congr
        intro t ht
        exact remainder_norm rh (ha.trans_le (by
          simpa only [min_eq_left hab] using ht.1)) r
      _ = _ := intervalIntegral.integral_mul_const _ _
  rw [weighted_zero_exact ha hab]
  calc
    _ ≤ ‖squareBoundary b r‖+‖squareBoundary a r‖+
        ‖(2 : ℂ)*(∫ t in a..b,squareRemainder t r)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ = (Real.sqrt b/(Real.log b)^2)*weight r+
        (Real.sqrt a/(Real.log a)^2)*weight r+
        2*‖∫ t in a..b,squareRemainder t r‖ := by
      rw [boundary_norm rh hb,boundary_norm rh ha,norm_mul]
      norm_num
    _ ≤ _ := by unfold squareAllowance; nlinarith

lemma squareAllowance_nonneg {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    0 ≤ squareAllowance a b := by
  have hi : 0 ≤ ∫ t in a..b,remainderKernel t := by
    apply intervalIntegral.integral_nonneg hab
    intro t ht
    have ht1 : 1 < t := ha.trans_le ht.1
    unfold remainderKernel
    have hl := Real.log_pos ht1
    positivity
  unfold squareAllowance
  positivity

/-- The complete signed transport of the original actual zero family is
bounded by its positive inverse-square mass, after the exact cancellation.
No finite truncation, omitted tail or desired arithmetic estimate occurs. -/
theorem full_weighted_zero_bound (rh : RiemannHypothesis)
    (hN : NicolasContinuation.SourceNicolas119) (hI : SourceIntegratedPsi)
    {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    ‖weightedTransport a b (fun t => ∑' r,zeroPrimitive t r)‖ ≤
      squareAllowance a b*NicolasContinuation.beta := by
  rw [←weighted_zero_tsum hI ha hab]
  have ht := tsum_of_norm_bounded
    ((weight_summable rh hN).mul_left (squareAllowance a b)).hasSum
    (fun r => weighted_zero_norm rh ha hab r)
  rw [tsum_mul_left] at ht
  exact ht.trans (mul_le_mul_of_nonneg_left (weight_mass_le_beta rh hN)
    (squareAllowance_nonneg ha hab))

#print axioms weighted_zero_norm
#print axioms full_weighted_zero_bound
end RHOcticPush.Spectral076
