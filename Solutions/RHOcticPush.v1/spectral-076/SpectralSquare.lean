import BoxZeroPrimitiveDerivative
import OcticConvergence
import ActualGMTransfer

/-! Signed second primitive of the actual zero family. The cancellation of the
factor rho+1 is proved before norms; no desired J-error bound is an input. -/
namespace RHOcticPush.Spectral076
open Real Complex Set MeasureTheory
open RHOcticPush.BoxPerron RHOcticPush.Convergence
set_option maxHeartbeats 0

noncomputable def squareCoefficient (r : IEANTN.RHSmoothing.Zero) : ℂ :=
  (IEANTN.zetaOrder r : ℂ)/(r : ℂ)^2

noncomputable def squareWave (x : ℝ) (r : IEANTN.RHSmoothing.Zero) : ℂ :=
  Complex.exp ((r : ℂ)*(Real.log x : ℂ))*squareCoefficient r

noncomputable def squareBoundary (x : ℝ) (r : IEANTN.RHSmoothing.Zero) : ℂ :=
  squareWave x r/(Real.log x : ℂ)^2

noncomputable def squareRemainder (x : ℝ) (r : IEANTN.RHSmoothing.Zero) : ℂ :=
  squareWave x r/((x : ℂ)*(Real.log x : ℂ)^3)

lemma squareCoefficient_norm (r : IEANTN.RHSmoothing.Zero) :
    ‖squareCoefficient r‖ = weight r := by
  have hm : (NicolasContinuation.multiplicity (zeroEquiv r) : ℝ) =
      (IEANTN.zetaOrder r : ℝ) := by exact_mod_cast multiplicity_eq r
  have ho : (0 : ℝ) ≤ IEANTN.zetaOrder r := by exact_mod_cast order_nonneg r
  unfold squareCoefficient weight RHLimit.NicolasMass.weight
  rw [norm_div, norm_pow, show (IEANTN.zetaOrder r : ℂ) =
    ((IEANTN.zetaOrder r : ℝ) : ℂ) by norm_cast, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg ho, hm]
  rfl

lemma squareWave_norm (rh : RiemannHypothesis) {x : ℝ} (hx : 0 < x)
    (r : IEANTN.RHSmoothing.Zero) : ‖squareWave x r‖ = Real.sqrt x*weight r := by
  have hr := RHLimit.NicolasMass.zero_re rh (zeroEquiv r)
  change (r : ℂ).re = 1/2 at hr
  unfold squareWave
  rw [norm_mul, squareCoefficient_norm, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rw [hr, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx]
  congr 1
  ring

lemma squareBoundary_hasDerivAt {x : ℝ} (hx : 1 < x)
    (r : IEANTN.RHSmoothing.Zero) :
    HasDerivAt (fun t => squareBoundary t r)
      ((Complex.exp ((r : ℂ)*(Real.log x : ℂ))*(IEANTN.zetaOrder r : ℂ)/
          (r : ℂ)) * (RHContinuation.Ramanujan.gmWeight x : ℂ) -
        2*squareRemainder x r) x := by
  have hx0 : x ≠ 0 := by linarith
  have hl : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  have he := ((((Real.hasDerivAt_log hx0).ofReal_comp.const_mul (r : ℂ)).cexp).mul_const
    (squareCoefficient r))
  have hd := he.div (((Real.hasDerivAt_log hx0).ofReal_comp).pow 2)
    (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hl))
  apply hd.congr_deriv
  simp only [squareRemainder, squareWave, squareCoefficient,
    RHContinuation.Ramanujan.gmWeight, Pi.pow_apply, Nat.cast_ofNat,
    Nat.reduceSub, pow_one]
  push_cast
  field_simp [zero_ne r, hx0, hl]
  <;> ring

#print axioms squareCoefficient_norm
#print axioms squareWave_norm
#print axioms squareBoundary_hasDerivAt
end RHOcticPush.Spectral076
