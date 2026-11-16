import Mathlib
namespace SynergyAnalytic
open Real Set MeasureTheory
set_option maxHeartbeats 0

theorem young_square (a b eps : ℝ) (he : 0 < eps) :
    (a+b)^2 ≤ (1+eps)*a^2+(1+1/eps)*b^2 := by
  have hn := div_nonneg (sq_nonneg (eps*a-b)) he.le
  have hi : (a+b)^2+(eps*a-b)^2/eps = (1+eps)*a^2+(1+1/eps)*b^2 := by
    field_simp
    <;> ring
  linarith

theorem norm_sub_one_young (z : ℂ) {eps : ℝ} (he : 0 < eps) :
    ‖z-1‖^2 ≤ (1+eps)*‖z‖^2+(1+1/eps) := by
  have hn : ‖z-1‖ ≤ ‖z‖+1 := by simpa using norm_sub_le z (1:ℂ)
  have hs := pow_le_pow_left₀ (norm_nonneg (z-1)) hn 2
  have hy := young_square ‖z‖ 1 eps he
  norm_num only [one_pow,mul_one] at hy
  exact hs.trans hy

theorem product_error_young
    {z v : ℂ} {amp shape r eps eta : ℝ}
    (ha : 0 ≤ amp) (hs : 0 ≤ shape) (hr : 0 ≤ r)
    (he : 0 < eps) (ht : 0 < eta) (hz : ‖z‖ ≤ amp*(shape+r)) :
    ‖z*v-1‖^2 ≤ (1+eps)*amp^2*((1+eta)*shape^2+(1+1/eta)*r^2)*‖v‖^2+(1+1/eps) := by
  have hn : ‖z*v‖^2 ≤ amp^2*(shape+r)^2*‖v‖^2 := by
    rw [norm_mul,← mul_pow,← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    gcongr
  have hh := norm_sub_one_young (z*v) he
  have h1 : 0 ≤ 1+eps := by positivity
  have h2 := mul_le_mul_of_nonneg_left hn h1
  have hy := young_square shape r eta ht
  have h3 := mul_le_mul_of_nonneg_left hy
    (show 0 ≤ (1+eps)*amp^2*‖v‖^2 by positivity)
  nlinarith

/-- The unit-error and low-zeta allowances are integrated against the Gaussian
itself, rather than against the arbitrary cutoff length. -/
theorem weighted_error_of_two_moments
    {z v : ℝ → ℂ} {w shape f : ℝ → ℝ}
    {T amp r eps eta b C G A : ℝ}
    (hT : 0 ≤ T) (ha : 0 ≤ amp) (hr : 0 ≤ r) (he : 0 < eps) (ht : 0 < eta)
    (hb : 0 ≤ b) (hz : Continuous z) (hv : Continuous v)
    (hwi : IntervalIntegrable w volume 0 b)
    (hfi : IntervalIntegrable (fun x => w x*f x) volume 0 b)
    (hsi : IntervalIntegrable (fun x => w x*shape x^2*f x) volume 0 b)
    (hwp : ∀ x ∈ Ioo 0 b, 0 ≤ w x)
    (hsp : ∀ x ∈ Ioo 0 b, 0 ≤ shape x)
    (hfd : ∀ x, f x = T*‖v x‖^2)
    (hZ : ∀ x ∈ Ioo 0 b, ‖z x‖ ≤ amp*(shape x+r))
    (hC : (∫ x in (0:ℝ)..b, w x*shape x^2*f x) ≤ C)
    (hG : (∫ x in (0:ℝ)..b, w x*f x) ≤ G)
    (hA : (∫ x in (0:ℝ)..b, w x) ≤ A) :
    (∫ x in (0:ℝ)..b, T*w x*‖z x*v x-1‖^2) ≤
      (1+eps)*amp^2*((1+eta)*C+(1+1/eta)*r^2*G)+(1+1/eps)*T*A := by
  let a : ℝ := (1+eps)*amp^2*(1+eta)
  let c : ℝ := (1+eps)*amp^2*(1+1/eta)*r^2
  let d : ℝ := (1+1/eps)*T
  have hap : 0 ≤ a := by dsimp [a];positivity
  have hcp : 0 ≤ c := by dsimp [c];positivity
  have hdp : 0 ≤ d := by dsimp [d];positivity
  have hleft : IntervalIntegrable (fun x => T*w x*‖z x*v x-1‖^2) volume 0 b :=
    (hwi.const_mul T).mul_continuousOn ((((hz.mul hv).sub continuous_const).norm.pow 2).continuousOn)
  have hright : IntervalIntegrable (fun x => a*(w x*shape x^2*f x)+c*(w x*f x)+d*w x) volume 0 b :=
    ((hsi.const_mul a).add (hfi.const_mul c)).add (hwi.const_mul d)
  have hi : (∫ x in (0:ℝ)..b, T*w x*‖z x*v x-1‖^2) ≤
      ∫ x in (0:ℝ)..b, a*(w x*shape x^2*f x)+c*(w x*f x)+d*w x := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo hb hleft hright
    intro x hx
    have hh := mul_le_mul_of_nonneg_left (product_error_young (v:=v x) ha (hsp x hx) hr he ht (hZ x hx))
      (mul_nonneg hT (hwp x hx))
    rw [hfd]
    dsimp [a,c,d]
    convert hh using 1 <;> first | rfl | ring
  rw [intervalIntegral.integral_add ((hsi.const_mul a).add (hfi.const_mul c)) (hwi.const_mul d),
    intervalIntegral.integral_add (hsi.const_mul a) (hfi.const_mul c),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hi
  have hi' := add_le_add (add_le_add (mul_le_mul_of_nonneg_left hC hap)
    (mul_le_mul_of_nonneg_left hG hcp)) (mul_le_mul_of_nonneg_left hA hdp)
  have hh := hi.trans hi'
  convert hh using 1 <;> first | rfl | (dsimp [a,c,d];ring)

#print axioms weighted_error_of_two_moments
end SynergyAnalytic
