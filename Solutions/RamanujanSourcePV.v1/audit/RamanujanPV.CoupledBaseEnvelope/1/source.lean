/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.AnalyticTransition
import RamanujanPV.CoupledUniformBounds

/-! Monotonicity and exact Taylor endpoint for the 1.25T coupled strip.
The li series and derivative identities remain the original explicit inputs.
The Axler li lower bound is needed over this expanded strip and is displayed
as such; the former [1.49T,1e19] type is not silently reused outside its range. -/
namespace RamanujanPV.CoupledBaseEnvelope
open Real Set RamanujanPV.AnalyticTransition
set_option maxHeartbeats 0
set_option maxRecDepth 10000

noncomputable def R (li : ℝ → ℝ) (x : ℝ) : ℝ :=
  li (x/Real.exp 1)-(389/200:ℝ)*Real.sqrt (x/Real.exp 1)/(Real.log x-1)-
    (li x)^2*Real.log x/(Real.exp 1*x)
noncomputable def Rderiv (li : ℝ → ℝ) (x : ℝ) : ℝ :=
  (li x*(Real.log x-1)-x)^2/(Real.exp 1*x^2*(Real.log x-1))-
    (389/400:ℝ)*(Real.log x-3)/(Real.exp 1*(Real.log x-1)^2*Real.sqrt (x/Real.exp 1))

lemma R_hasDerivAt {li : ℝ → ℝ} (hderiv : LogIntegralDerivative li)
    {x : ℝ} (hx : 6 < x) (hL : 1 < Real.log x) :
    HasDerivAt (R li) (Rderiv li x) x := by
  have hx0 : 0 < x := by linarith
  have hE := Real.exp_pos 1
  have hxe : 2 < x/Real.exp 1 := by
    apply (lt_div_iff₀ hE).mpr
    linarith [Real.exp_one_lt_d9]
  have hln : Real.log x ≠ 0 := by linarith
  have hm : Real.log x-1 ≠ 0 := by linarith
  have hroot : 0 < Real.sqrt (x/Real.exp 1) := Real.sqrt_pos.mpr (by positivity)
  have hlogxe : Real.log (x/Real.exp 1) = Real.log x-1 := by
    rw [Real.log_div hx0.ne' hE.ne',Real.log_exp]
  have hs := ((hasDerivAt_id x).div_const (Real.exp 1)).sqrt (show x/Real.exp 1 ≠ 0 by positivity)
  have ha := (hderiv (x/Real.exp 1) hxe).comp x ((hasDerivAt_id x).div_const (Real.exp 1))
  have ht := ((hs.const_mul (389/200:ℝ)).div ((Real.hasDerivAt_log hx0.ne').sub_const 1) hm)
  have hu := (((hderiv x (by linarith)).pow 2).mul (Real.hasDerivAt_log hx0.ne')).div
    ((hasDerivAt_id x).const_mul (Real.exp 1)) (by positivity)
  have hd := (ha.sub ht).sub hu
  have hsq : Real.exp 1*(Real.sqrt (x/Real.exp 1))^2 = x := by
    rw [Real.sq_sqrt (by positivity)]
    field_simp
  convert! hd using 1
  dsimp [Rderiv]
  rw [hlogxe]
  norm_num only [Nat.cast_ofNat,Nat.reduceSub,pow_one]
  generalize hAv : li x = A
  generalize hLv : Real.log x = L
  generalize hSv : Real.sqrt (x/Real.exp 1) = s
  rw [hSv] at hsq hroot
  rw [hLv] at hL
  rw [← hsq]
  field_simp [show L ≠ 0 by linarith,show L-1 ≠ 0 by linarith]
  <;> ring

theorem strip_height {x : ℝ} (hx : x ∈ Icc (1250000000000:ℝ) 1490000000000) :
    (1061/1000:ℝ)*(Real.log x)^4 ≤ Real.sqrt (x/Real.exp 1) := by
  have hx0 : 0 < x := by linarith [hx.1]
  have hL := CoupledUniformBounds.log_lower hx.1
  have hLhi : Real.log x ≤ (281/10:ℝ) := by
    have h := Real.log_le_log hx0 hx.2
    linarith [log_endpoint_bounds.2]
  have hroot : (677000:ℝ) ≤ Real.sqrt (x/Real.exp 1) := by
    apply Real.le_sqrt_of_sq_le
    apply (le_div_iff₀ (Real.exp_pos 1)).2
    have h := mul_le_mul_of_nonneg_left CoupledUniformBounds.exp_one_upper
      (sq_nonneg (677000:ℝ))
    nlinarith [hx.1]
  have hp := pow_le_pow_left₀ (by linarith : 0 ≤ Real.log x) hLhi 4
  have hm := mul_le_mul_of_nonneg_left hp (by norm_num : (0:ℝ)≤1061/1000)
  have hn : (1061/1000:ℝ)*(281/10)^4 ≤ 677000 := by norm_num
  exact (hm.trans hn).trans hroot

theorem derivative_nonneg {li : ℝ → ℝ}
    (hAxler : ∀ x ∈ Icc (1250000000000:ℝ) 1490000000000,
      x/(Real.log x-1-1/Real.log x) < li x)
    {x : ℝ} (hx : x ∈ Icc (1250000000000:ℝ) 1490000000000) :
    0 ≤ Rderiv li x := by
  have hx0 : 0 < x := by linarith [hx.1]
  have hL := CoupledUniformBounds.log_lower hx.1
  have hs : 0 < Real.sqrt (x/Real.exp 1) := Real.sqrt_pos.2 (by positivity)
  have hold := base_derivative_nonneg hx0 (Real.exp_pos 1)
    (by linarith : 4 ≤ Real.log x) hs (hAxler x hx) (strip_height hx)
  have hratio : 0 ≤ (Real.log x-3) /
      (Real.exp 1*(Real.log x-1)^2*Real.sqrt (x/Real.exp 1)) := by positivity
  have hcoef := mul_le_mul_of_nonneg_right
    (by norm_num : (389/400:ℝ)≤1061/1000) hratio
  unfold Rderiv
  rw [mul_div_assoc] at hold ⊢
  linarith

theorem monotone_strip {li : ℝ → ℝ} (hderiv : LogIntegralDerivative li)
    (hAxler : ∀ x ∈ Icc (1250000000000:ℝ) 1490000000000,
      x/(Real.log x-1-1/Real.log x) < li x) :
    MonotoneOn (R li) (Icc (1250000000000:ℝ) 1490000000000) := by
  have hd : ∀ x ∈ Icc (1250000000000:ℝ) 1490000000000,
      HasDerivAt (R li) (Rderiv li x) x := by
    intro x hx
    exact R_hasDerivAt hderiv (by linarith [hx.1])
      (by linarith [CoupledUniformBounds.log_lower hx.1])
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
  · intro x hx
    exact (hd x hx).continuousAt.continuousWithinAt
  · intro x hx
    exact (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [(hd x (interior_subset hx)).deriv]
    exact derivative_nonneg hAxler (interior_subset hx)

#print axioms R_hasDerivAt
#print axioms strip_height
#print axioms derivative_nonneg
#print axioms monotone_strip
end RamanujanPV.CoupledBaseEnvelope
