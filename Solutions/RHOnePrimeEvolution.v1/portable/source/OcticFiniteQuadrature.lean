import OcticLocalQuadrature
import OcticTailIntegrals
namespace RHOcticPush.Moments
open Real Set MeasureTheory Finset
set_option maxHeartbeats 0

noncomputable def cellCurvature (a : ℝ) : ℝ :=
  if 10 ≤ a then 40 / a^2 else 16/33
noncomputable def cellBudget (a b pa pb : ℝ) : ℝ :=
  (b-a)/2*(pa+pb)+cellCurvature a*(b-a)^3/12

lemma octic_cell {a b pa pb : ℝ} (hab : a < b)
    (ha : |EvenKernel.transform 4 a| ≤ pa) (hb : |EvenKernel.transform 4 b| ≤ pb) :
    (∫ y in a..b, |EvenKernel.transform 4 y|) ≤ cellBudget a b pa pb := by
  have hc : (∫ y in a..b, |EvenKernel.transform 4 y|) ≤
      (b-a)/2*(|EvenKernel.transform 4 a|+|EvenKernel.transform 4 b|)+
      cellCurvature a*(b-a)^3/12 := by
    by_cases h : 10 ≤ a
    · simpa only [cellCurvature, if_pos h] using
        octic_abs_trapezoid_decay (by linarith : 0 < a) hab
    · simpa only [cellCurvature, if_neg h] using octic_abs_trapezoid hab
  have hpoint := mul_le_mul_of_nonneg_left (add_le_add ha hb)
    (show 0 ≤ (b-a)/2 by linarith)
  unfold cellBudget
  linarith

/-- Sound numerical interface for an arbitrary strictly increasing finite mesh.
Every numerical endpoint and every intervening real argument are covered. -/
theorem octic_finite_quad {N : ℕ} {a p : ℕ → ℝ}
    (hstep : ∀ i < N, a i < a (i+1))
    (hvalue : ∀ i ≤ N, |EvenKernel.transform 4 (a i)| ≤ p i) :
    (∫ y in a 0..a N, |EvenKernel.transform 4 y|) ≤
      ∑ i ∈ range N, cellBudget (a i) (a (i+1)) (p i) (p (i+1)) := by
  rw [← intervalIntegral.sum_integral_adjacent_intervals
    (fun i _ => transform_abs_continuous.intervalIntegrable (a i) (a (i+1)))]
  apply sum_le_sum
  intro i hi
  have hiN := Finset.mem_range.mp hi
  exact octic_cell (hstep i hiN) (hvalue i hiN.le) (hvalue (i+1) (by omega))

lemma octic_log_cell {a b pa pb lb : ℝ} (ha1 : 1 ≤ a) (hab : a < b)
    (ha : |EvenKernel.transform 4 a| ≤ pa) (hb : |EvenKernel.transform 4 b| ≤ pb)
    (hl : log b ≤ lb) :
    (∫ y in a..b, |EvenKernel.transform 4 y| * log y) ≤ cellBudget a b pa pb * lb := by
  have hlog : ContinuousOn log (Icc a b) := by
    intro y hy
    exact (continuousAt_log (by linarith [hy.1] : y ≠ 0)).continuousWithinAt
  have hprod : IntervalIntegrable (fun y => |EvenKernel.transform 4 y| * log y) volume a b := (transform_abs_continuous.continuousOn.mul hlog).intervalIntegrable_of_Icc
    hab.le
  have hhi : log b ≤ lb := hl
  have hl0 : 0 ≤ lb := (log_nonneg (by linarith : 1 ≤ b)).trans hl
  calc
    _ ≤ ∫ y in a..b, |EvenKernel.transform 4 y| * lb := by
      apply intervalIntegral.integral_mono_on hab.le hprod
        ((transform_abs_continuous.mul_const lb).intervalIntegrable _ _)
      intro y hy
      have hy0 : 0 < y := by linarith [hy.1]
      exact mul_le_mul_of_nonneg_left
        ((log_le_log hy0 hy.2).trans hl) (abs_nonneg _)
    _ = (∫ y in a..b, |EvenKernel.transform 4 y|) * lb :=
      intervalIntegral.integral_mul_const _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right (octic_cell hab ha hb) hl0

lemma octic_log_integrableOn {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun y => |EvenKernel.transform 4 y| * log y) volume a b := by
  have hlog : ContinuousOn log (Icc a b) := by
    intro y hy
    exact (continuousAt_log (by linarith [hy.1] : y ≠ 0)).continuousWithinAt
  exact (transform_abs_continuous.continuousOn.mul hlog).intervalIntegrable_of_Icc hab

theorem octic_finite_log_quad {m N : ℕ} (hmN : m ≤ N) {a p l : ℕ → ℝ}
    (ha1 : ∀ i ∈ Finset.Ico m N, 1 ≤ a i)
    (hstep : ∀ i ∈ Finset.Ico m N, a i < a (i+1))
    (hvalue : ∀ i ≤ N, |EvenKernel.transform 4 (a i)| ≤ p i)
    (hlog : ∀ i ≤ N, log (a i) ≤ l i) :
    (∫ y in a m..a N, |EvenKernel.transform 4 y| * log y) ≤
      ∑ i ∈ Finset.Ico m N, cellBudget (a i) (a (i+1)) (p i) (p (i+1)) * l (i+1) := by
  rw [← intervalIntegral.sum_integral_adjacent_intervals_Ico hmN
    (fun i hi => octic_log_integrableOn (ha1 i (Finset.mem_Ico.mpr hi))
      (hstep i (Finset.mem_Ico.mpr hi)).le)]
  apply sum_le_sum
  intro i hi
  exact octic_log_cell (ha1 i hi) (hstep i hi) (hvalue i (by
    have h := (Finset.mem_Ico.mp hi).2; omega))
    (hvalue (i+1) (by have h := (Finset.mem_Ico.mp hi).2; omega))
    (hlog (i+1) (by have h := (Finset.mem_Ico.mp hi).2; omega))
#print axioms octic_finite_quad
#print axioms octic_finite_log_quad
end RHOcticPush.Moments
