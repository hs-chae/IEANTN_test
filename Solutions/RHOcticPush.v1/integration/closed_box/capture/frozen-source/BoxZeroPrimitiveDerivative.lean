import BoxZeroUniform
import Mathlib.Analysis.Complex.RealDeriv

/-! Exact derivative of the actual integrated-Perron zero primitive.
Only the open critical strip is used; neither RH nor a source identity is assumed. -/
namespace RHOcticPush.BoxPerron
open Real Complex Set
set_option maxHeartbeats 0

lemma zero_ne (r : IEANTN.RHSmoothing.Zero) : (r : ℂ) ≠ 0 := by
  intro h
  have hh := (zero_re_bounds r).1
  rw [h] at hh
  norm_num at hh

lemma zero_add_one_ne (r : IEANTN.RHSmoothing.Zero) : (r : ℂ)+1 ≠ 0 := by
  intro h
  have hr := congrArg Complex.re h
  simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at hr
  linarith [(zero_re_bounds r).1]

lemma zero_exp_factor {x : ℝ} (hx : 0 < x) (r : IEANTN.RHSmoothing.Zero) :
    Complex.exp (((r : ℂ)+1)*(Real.log x : ℂ)) =
      Complex.exp ((r : ℂ)*(Real.log x : ℂ)) * (x : ℂ) := by
  rw [add_mul, one_mul, Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hx]

theorem zeroPrimitive_hasDerivAt {x : ℝ} (hx : 0 < x)
    (r : IEANTN.RHSmoothing.Zero) :
    HasDerivAt (fun y : ℝ => zeroPrimitive y r)
      (Complex.exp ((r : ℂ)*(Real.log x : ℂ)) * (IEANTN.zetaOrder r : ℂ) / (r : ℂ)) x := by
  have hd :=
    (((Real.hasDerivAt_log hx.ne').ofReal_comp.const_mul ((r : ℂ)+1)).cexp).mul_const
      (zeroCoefficient r)
  apply hd.congr_deriv
  rw [zero_exp_factor hx]
  unfold zeroCoefficient
  push_cast
  field_simp [zero_ne r, zero_add_one_ne r, hx.ne']
  <;> ring

#print axioms zeroPrimitive_hasDerivAt
end RHOcticPush.BoxPerron
