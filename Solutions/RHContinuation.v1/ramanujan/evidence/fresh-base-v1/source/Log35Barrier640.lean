import AnalyticBarrier640

namespace Ramanujan640.AnalyticBarrier
open Real Set Finset RamanujanPV.AnalyticTransition
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem monotoneIcc {f f' : ℝ → ℝ} {a b : ℝ}
    (hd : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hn : ∀ t ∈ Icc a b, 0 ≤ f' t) : MonotoneOn f (Icc a b) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
  · intro t ht
    exact (hd t ht).continuousAt.continuousWithinAt
  · intro t ht
    exact (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [(hd t (interior_subset ht)).deriv]
    exact hn t (interior_subset ht)

/-- Exact35-term atanh tail, proved by the derivative of a polynomial
majorant. This keeps the frozen evaluator's35 terms and denominator71. -/
theorem log35_error {r : ℝ} (hr : 0 ≤ r) (hr3 : r ≤ 1/3) :
    0 ≤ logAtanhError 35 r ∧
    logAtanhError 35 r ≤ 2*r^71/(71*(1-r^2)) := by
  have hden : ∀ t ∈ Icc (0:ℝ) r, 0 < 1-t^2 := by
    intro t ht
    nlinarith [ht.1,ht.2]
  have hdenr : 0 < 1-r^2 := hden r ⟨hr,le_refl _⟩
  have hd : ∀ t ∈ Icc (0:ℝ) r,
      HasDerivAt (logAtanhError 35) (2*t^70/(1-t^2)) t := by
    intro t ht
    simpa using logAtanhError_deriv (by linarith [ht.1]) (by linarith [ht.2]) 35
  have hm := monotoneIcc hd (by
    intro t ht
    exact div_nonneg (by positivity) (hden t ht).le)
  have hz : logAtanhError 35 0 = 0 := by simp [logAtanhError,logAtanhPoly]
  have hlo := hm (show (0:ℝ) ∈ Icc 0 r by simp [hr])
    (show r ∈ Icc 0 r by simp [hr]) hr
  rw [hz] at hlo
  let U : ℝ → ℝ := fun t => 2*t^71/(71*(1-r^2))
  have hdU : ∀ t : ℝ, HasDerivAt U (2*t^70/(1-r^2)) t := by
    intro t
    convert! (((hasDerivAt_id t).pow 71).const_mul 2).div_const (71*(1-r^2)) using 1 <;>
      first | rfl | (norm_num <;> field_simp <;> ring)
  have hdg : ∀ t ∈ Icc (0:ℝ) r,
      HasDerivAt (fun t => U t-logAtanhError 35 t)
        (2*t^70/(1-r^2)-2*t^70/(1-t^2)) t :=
    fun t ht => (hdU t).sub (hd t ht)
  have hmg := monotoneIcc hdg (by
    intro t ht
    have hsq : t^2 ≤ r^2 := by nlinarith [ht.1,ht.2]
    have hq : 2*t^70/(1-t^2) ≤ 2*t^70/(1-r^2) :=
      div_le_div_of_nonneg_left (by positivity) hdenr (by linarith)
    exact sub_nonneg.mpr hq)
  have hup := hmg (show (0:ℝ) ∈ Icc 0 r by simp [hr])
    (show r ∈ Icc 0 r by simp [hr]) hr
  dsimp [U] at hup
  rw [hz] at hup
  simp only [ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow,mul_zero,zero_div,
    sub_zero,zero_sub] at hup
  exact ⟨hlo, by linarith⟩

/-- The source uses this uniform upper tail after reduction to1≤x≤2. -/
theorem log35_error_uniform {r : ℝ} (hr : 0 ≤ r) (hr3 : r ≤ 1/3) :
    0 ≤ logAtanhError 35 r ∧
    logAtanhError 35 r ≤ 2*(1/3:ℝ)^71/(71*(1-(1/3:ℝ)^2)) := by
  have h := log35_error hr hr3
  have hp := pow_le_pow_left₀ hr hr3 71
  have hd : (8/9:ℝ) ≤ 1-r^2 := by nlinarith
  constructor
  · exact h.1
  · apply h.2.trans
    apply div_le_div₀ (by positivity) (by nlinarith [hp])
      (by norm_num) (by nlinarith [hd])

theorem log35_bounds {r : ℝ} (hr : 0 ≤ r) (hr3 : r ≤ 1/3) :
    logAtanhPoly 35 r ≤ Real.log ((1+r)/(1-r)) ∧
    Real.log ((1+r)/(1-r)) ≤
      logAtanhPoly 35 r+2*(1/3:ℝ)^71/(71*(1-(1/3:ℝ)^2)) := by
  have h := log35_error_uniform hr hr3
  have hp : (1:ℝ)+r ≠ 0 := by linarith
  have hm : (1:ℝ)-r ≠ 0 := by linarith
  rw [Real.log_div hp hm]
  unfold logAtanhError at h
  constructor <;> linarith

#print axioms log35_error
#print axioms log35_error_uniform
#print axioms log35_bounds
end Ramanujan640.AnalyticBarrier
