import SynergyAnalytic.UpperRectangles
import DensityPartialSum
namespace SynergyAnalytic
open Real Set MeasureTheory Finset
set_option maxHeartbeats 0

/-- Exact reciprocal area of a positive cell, rather than a sampled or
left-rectangle estimate for the reciprocal kernel. -/
theorem reciprocal_cell_integral {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    (∫ x in a..b, 1/x^2) = 1/a-1/b := by
  have hd : ∀ x∈uIcc a b, HasDerivAt (fun u:ℝ => -(1/u)) (1/x^2) x := by
    intro x hx
    rw [uIcc_of_le hab] at hx
    have hx0 : x ≠ 0 := (ha.trans_le hx.1).ne'
    convert (hasDerivAt_inv hx0).neg using 1 <;> first | rfl | (simp only [neg_neg,one_div] <;> first | rfl | (funext u;rfl))
  have hc : ContinuousOn (fun x:ℝ => 1/x^2) (uIcc a b) := by
    intro x hx
    rw [uIcc_of_le hab] at hx
    have hx0 : x ≠ 0 := (ha.trans_le hx.1).ne'
    exact (by fun_prop (disch:=exact pow_ne_zero 2 hx0) : ContinuousAt (fun x:ℝ=>1/x^2) x).continuousWithinAt
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable
  linarith

/-- Kernel-weighted quadrature for an arbitrary integrable cumulative count.
Each cap bounds EVERY real height inside the cell. -/
theorem reciprocal_integral_cells {F : ℝ→ℝ} {a caps : ℕ→ℝ} {n : ℕ}
    (ha : Monotone a) (h0 : 0<a 0)
    (hi : IntervalIntegrable (fun u=>F u/u^2) volume (a 0) (a n))
    (hcaps : ∀i<n,∀u∈Icc (a i) (a (i+1)),F u≤caps i) :
    (∫u in a 0..a n,F u/u^2) ≤
      ∑i∈range n,caps i*(1/a i-1/a (i+1)) := by
  have his : ∀i<n,IntervalIntegrable (fun u=>F u/u^2) volume (a i) (a (i+1)) := by
    intro i hin
    apply hi.mono_set
    rw [uIcc_of_le (ha (Nat.le_succ i)),uIcc_of_le (ha (Nat.zero_le n))]
    exact Icc_subset_Icc (ha (Nat.zero_le i)) (ha hin)
  rw [←intervalIntegral.sum_integral_adjacent_intervals his]
  apply Finset.sum_le_sum
  intro i hin
  have hi' := mem_range.mp hin
  have hip : 0<a i := h0.trans_le (ha (Nat.zero_le i))
  have hrec : IntervalIntegrable (fun u:ℝ => 1/u^2) volume (a i) (a (i+1)) := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [uIcc_of_le (ha (Nat.le_succ i))] at hx
    have hx0 : x≠0 := (hip.trans_le hx.1).ne'
    exact (by fun_prop (disch:=exact pow_ne_zero 2 hx0) : ContinuousAt (fun u:ℝ=>1/u^2) x).continuousWithinAt
  have hm := intervalIntegral.integral_mono_on (ha (Nat.le_succ i)) (his i hi')
    (hrec.const_mul (caps i)) (fun u hu =>
      show F u/u^2 ≤ caps i*(1/u^2) by
        simpa only [mul_one_div] using div_le_div_of_nonneg_right (hcaps i hi' u hu) (sq_nonneg u))
  rw [intervalIntegral.integral_const_mul,reciprocal_cell_integral hip (ha (Nat.le_succ i))] at hm
  exact hm

/-- Finite-height reciprocal sum from a whole-cell cumulative count envelope.
No monotonicity of the numerical caps and no desired reciprocal premise. -/
theorem finite_reciprocal_cells {α : Type*} (S : Finset α) (gamma w : α→ℝ)
    {a caps : ℕ→ℝ} {n : ℕ} {lastCap : ℝ}
    (ha : Monotone a) (h0 : 0<a 0)
    (hg : ∀z∈S,a 0<gamma z ∧gamma z≤a n)
    (hend : (∑z∈S,w z)≤lastCap)
    (hcaps : ∀i<n,∀u∈Icc (a i) (a (i+1)),
      (∑z∈S,if gamma z≤u then w z else 0)≤caps i) :
    (∑z∈S,w z/gamma z)≤lastCap/a n+
      ∑i∈range n,caps i*(1/a i-1/a (i+1)) := by
  obtain ⟨he,hi⟩ := CH2QRH.finite_reciprocal_partial_sum S gamma w h0 (ha (Nat.zero_le n)) hg
  rw [he]
  exact add_le_add (div_le_div_of_nonneg_right hend (h0.trans_le (ha (Nat.zero_le n))).le)
    (reciprocal_integral_cells ha h0 hi hcaps)

#print axioms reciprocal_integral_cells
#print axioms finite_reciprocal_cells
end SynergyAnalytic
