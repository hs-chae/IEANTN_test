import SynergyAnalytic.LogAtanh
namespace SynergyAnalytic
open Real Set MeasureTheory Finset
set_option maxHeartbeats 0

/-- A uniform analytic bound for the exact 80-term source series. The source
adds one128-bit quantum to the upper endpoint; arithmetic rounding remains
in the separately verified directed operations. -/
theorem log_atanh80_error {r : ℝ} (hr : 0 ≤ r) (hr2 : r ≤ 1/2) :
    0 ≤ logAtanhError 80 r ∧ logAtanhError 80 r ≤ 1/(2:ℝ)^128 := by
  let f : ℝ → ℝ := fun x => 2*x^160/(1-x^2)
  have hden : ∀ x ∈ Icc (0:ℝ) r, 0 < 1-x^2 := by
    intro x hx
    nlinarith [hx.1,hx.2]
  have hc : ContinuousOn f (Icc 0 r) := by
    unfold f
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro x hx
    exact (hden x hx).ne'
  have hi : IntervalIntegrable f volume 0 r := hc.intervalIntegrable_of_Icc hr
  have hd : ∀ x ∈ uIcc (0:ℝ) r, HasDerivAt (logAtanhError 80) (f x) x := by
    intro x hx
    rw [uIcc_of_le hr] at hx
    simpa [f] using logAtanhError_deriv (by linarith [hx.1]) (by linarith [hx.2]) 80
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  have hz : logAtanhError 80 0 = 0 := by simp [logAtanhError,logAtanhPoly]
  rw [hz,sub_zero] at he
  have hf0 : ∀ x ∈ Icc (0:ℝ) r, 0 ≤ f x := by
    intro x hx
    exact div_nonneg (by positivity) (hden x hx).le
  have hfu : ∀ x ∈ Icc (0:ℝ) r, f x ≤ 1/(2:ℝ)^128 := by
    intro x hx
    have hx0 : 0 ≤ x := hx.1
    have hx2 : x ≤ (1/2:ℝ) := hx.2.trans hr2
    have hp : x^160 ≤ (1/2:ℝ)^160 := pow_le_pow_left₀ hx0 hx2 160
    have hq : (3/4:ℝ) ≤ 1-x^2 := by nlinarith
    have hb : f x ≤ 2*(1/2:ℝ)^160/(3/4:ℝ) := by
      unfold f
      exact div_le_div₀ (by positivity) (by nlinarith) (by norm_num) hq
    exact hb.trans (by norm_num)
  have hlo := intervalIntegral.integral_nonneg (μ:=volume) hr hf0
  have hup := intervalIntegral.integral_mono_on hr hi (intervalIntegrable_const)
    hfu
  rw [he] at hlo hup
  simp only [intervalIntegral.integral_const,sub_zero,smul_eq_mul] at hup
  refine ⟨hlo,?_⟩
  have hq : 0 < 1/(2:ℝ)^128 := by positivity
  nlinarith

theorem log_atanh80_bounds {r lo hi : ℝ} (hr : 0 ≤ r) (hr2 : r ≤ 1/2)
    (hl : lo ≤ logAtanhPoly 80 r) (hu : logAtanhPoly 80 r ≤ hi) :
    lo ≤ Real.log ((1+r)/(1-r)) ∧
      Real.log ((1+r)/(1-r)) ≤ hi+1/(2:ℝ)^128 := by
  have he := log_atanh80_error hr hr2
  have hp : (1:ℝ)+r ≠ 0 := by linarith
  have hm : (1:ℝ)-r ≠ 0 := by linarith
  rw [Real.log_div hp hm]
  unfold logAtanhError at he
  constructor <;> linarith

#print axioms log_atanh80_error
#print axioms log_atanh80_bounds
end SynergyAnalytic
