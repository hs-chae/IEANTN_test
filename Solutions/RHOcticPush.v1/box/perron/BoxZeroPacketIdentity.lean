import BoxZeroPrimitiveDerivative

/-! The actual logarithmic derivative packet is precisely the original Box
packet, with its original complex power, denominator and multiplicity. -/
namespace RHOcticPush.BoxPerron
open Real Complex Set MeasureTheory IEANTN.RHSmoothing
set_option maxHeartbeats 0

lemma cpow_exp_eq (L : ℝ) (r : IEANTN.RHSmoothing.Zero) :
    (Real.exp L : ℂ) ^ (r : ℂ) = Complex.exp ((r : ℂ)*(L : ℂ)) := by
  have hn : (Real.exp L : ℂ) ≠ 0 := by exact_mod_cast Real.exp_ne_zero L
  rw [Complex.cpow_def_of_ne_zero hn, ← Complex.ofReal_log (Real.exp_pos L).le,
    Real.log_exp]
  congr 1
  ring

theorem zero_packet_identity (r : IEANTN.RHSmoothing.Zero) (L s : ℝ) :
    (∫ u in (-1 : ℝ)..1, (1/2 : ℂ) *
      (Complex.exp ((r : ℂ) *
        (Real.log (Real.exp L * Real.exp ((s+u)*delta L)) : ℂ)) *
          (IEANTN.zetaOrder r : ℂ) / (r : ℂ))) =
      IEANTN.RHSmoothing.zeroPacket box s L r := by
  unfold IEANTN.RHSmoothing.zeroPacket
  calc
    _ = ∫ u in (-1 : ℝ)..1, ((Real.exp L : ℂ) ^ (r : ℂ) / (r : ℂ)) *
        ((box u : ℂ) * Complex.exp ((r : ℂ)*(((s+u)*delta L : ℝ) : ℂ))) *
          (IEANTN.zetaOrder r : ℂ) := by
      apply intervalIntegral.integral_congr
      intro u _
      dsimp only
      rw [Real.log_mul (Real.exp_ne_zero L) (Real.exp_ne_zero _),
        Real.log_exp, Real.log_exp, cpow_exp_eq]
      push_cast
      rw [mul_add, Complex.exp_add]
      unfold box
      push_cast
      ring
    _ = _ := by
      rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul]

#print axioms zero_packet_identity
end RHOcticPush.BoxPerron
