import Mathlib
namespace SynergyAnalytic
open Real Set MeasureTheory Finset
set_option maxHeartbeats 0

/-- A closed upper-rectangle reduction on the ACTUAL full cells.  This theorem
does not infer a cell bound from a sampled endpoint. -/
theorem integral_le_upper_rectangles
    {f : ℝ → ℝ} {a : ℕ → ℝ} {caps : ℕ → ℝ} {n : ℕ}
    (ha : Monotone a) (hf : ContinuousOn f (Icc (a 0) (a n)))
    (hcaps : ∀ i < n, ∀ x ∈ Icc (a i) (a (i+1)), f x ≤ caps i) :
    (∫ x in a 0..a n, f x) ≤ ∑ i ∈ range n, (a (i+1)-a i)*caps i := by
  have hi : ∀ i < n, IntervalIntegrable f volume (a i) (a (i+1)) := by
    intro i hin
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (ha (Nat.le_succ i))]
    exact hf.mono (Icc_subset_Icc (ha (Nat.zero_le i)) (ha hin))
  rw [← intervalIntegral.sum_integral_adjacent_intervals hi]
  apply Finset.sum_le_sum
  intro i hin
  have hi' := mem_range.mp hin
  have hm := intervalIntegral.integral_mono_on (ha (Nat.le_succ i)) (hi i hi')
    (intervalIntegrable_const (c:=caps i)) (hcaps i hi')
  simpa only [intervalIntegral.integral_const,smul_eq_mul] using hm

noncomputable def uniformEdge (a b : ℝ) (n i : ℕ) : ℝ := a+(b-a)*(i:ℝ)/n

theorem uniformEdge_monotone {a b : ℝ} (hab : a ≤ b) (n : ℕ) : Monotone (uniformEdge a b n) := by
  intro i j hij
  unfold uniformEdge
  gcongr

theorem uniform_upper_rectangles
    {f : ℝ → ℝ} {a b : ℝ} {n : ℕ} (hab : a ≤ b) (hn : 0 < n)
    (caps : ℕ → ℝ) (hf : ContinuousOn f (Icc a b))
    (hcaps : ∀ i < n, ∀ x ∈ Icc (uniformEdge a b n i) (uniformEdge a b n (i+1)), f x ≤ caps i) :
    (∫ x in a..b, f x) ≤ ((b-a)/(n:ℝ))*∑ i ∈ range n, caps i := by
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have he0 : uniformEdge a b n 0 = a := by simp [uniformEdge]
  have hen : uniformEdge a b n n = b := by simp [uniformEdge,hn0]
  have hi := integral_le_upper_rectangles (uniformEdge_monotone hab n)
    (by simpa only [he0,hen] using hf) hcaps
  rw [he0,hen] at hi
  have he : ∀ i : ℕ, uniformEdge a b n (i+1)-uniformEdge a b n i = (b-a)/(n:ℝ) := by
    intro i
    unfold uniformEdge
    push_cast
    ring
  simp_rw [he] at hi
  simpa only [Finset.mul_sum] using hi

#print axioms integral_le_upper_rectangles
#print axioms uniform_upper_rectangles
end SynergyAnalytic
