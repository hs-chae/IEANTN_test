import BoxZeroShift
import OcticConvergence

/-! Correspondence of the original Box zero packet with its actual shifted kernel. -/
namespace RHOcticPush.BoxZero
open Real Complex Set MeasureTheory IEANTN.RHSmoothing
set_option maxHeartbeats 0

theorem box_complex_factor (z : ℂ) (d s : ℝ) :
    (∫ u in (-1 : ℝ)..1, (box u : ℂ) *
        Complex.exp (z * (((s+u)*d : ℝ) : ℂ))) =
      Complex.exp (z * ((s*d : ℝ) : ℂ)) * H (z.re*d) (z.im*d) := by
  unfold H
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro u _
  dsimp only
  have hz : z = (z.re : ℂ) + (z.im : ℂ)*Complex.I := (Complex.re_add_im z).symm
  have ha : z * (((s+u)*d : ℝ) : ℂ) =
      z * ((s*d : ℝ) : ℂ) + (((z.re*d)*u : ℝ) : ℂ) +
        (((z.im*d : ℝ) : ℂ)*Complex.I)*(u : ℂ) := by
    conv_lhs => rw [hz]
    conv_rhs => lhs; lhs; rw [hz]
    push_cast
    ring
  rw [ha, Complex.exp_add, Complex.exp_add, ← Complex.ofReal_exp]
  unfold box phase
  push_cast
  ring

lemma packet_zero_re (rh : RiemannHypothesis) (z : IEANTN.RHSmoothing.Zero) :
    z.val.re = 1/2 := RHLimit.NicolasMass.zero_re rh (RHOcticPush.Convergence.zeroEquiv z)

lemma cpow_exp_norm (rh : RiemannHypothesis) (L : ℝ) (z : IEANTN.RHSmoothing.Zero) :
    ‖(Real.exp L : ℂ) ^ (z : ℂ)‖ = Real.exp (L/2) := by
  have hn : (Real.exp L : ℂ) ≠ 0 := by exact_mod_cast Real.exp_ne_zero L
  rw [Complex.cpow_def_of_ne_zero hn, ← Complex.ofReal_log (Real.exp_pos L).le,
    Real.log_exp, Complex.norm_exp]
  have hr := packet_zero_re rh z
  congr 1
  simp [Complex.mul_re, hr]
  ring

lemma shifted_phase_norm (rh : RiemannHypothesis) (s d : ℝ)
    (z : IEANTN.RHSmoothing.Zero) :
    ‖Complex.exp ((z : ℂ) * ((s*d : ℝ) : ℂ))‖ = Real.exp (s*d/2) := by
  rw [Complex.norm_exp]
  have hr := packet_zero_re rh z
  congr 1
  simp [Complex.mul_re, hr]
  ring

/-- Exact normalization, including the original multiplicity and denominator. -/
theorem packet_norm_exact (rh : RiemannHypothesis) (s L : ℝ)
    (z : IEANTN.RHSmoothing.Zero) :
    ‖IEANTN.RHSmoothing.zeroPacket box s L z‖ =
      Real.exp (L/2) * Real.exp (s * delta L / 2) *
        ‖H (delta L/2) (z.val.im * delta L)‖ / ‖(z : ℂ)‖ *
          (IEANTN.zetaOrder z.val : ℝ) := by
  have ho : (0 : ℝ) ≤ IEANTN.zetaOrder z.val := by
    exact_mod_cast RHOcticPush.Convergence.order_nonneg z
  unfold IEANTN.RHSmoothing.zeroPacket
  rw [box_complex_factor, norm_mul, norm_mul, norm_div, cpow_exp_norm rh,
    norm_mul, shifted_phase_norm rh]
  have hc : (IEANTN.zetaOrder z.val : ℂ) = ((IEANTN.zetaOrder z.val : ℝ) : ℂ) := by norm_cast
  rw [hc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ho, packet_zero_re rh z]
  rw [show (1/2 : ℝ)*delta L = delta L/2 by ring]
  ring

#print axioms box_complex_factor
#print axioms packet_norm_exact
end RHOcticPush.BoxZero
