import BoxIntegratedDefs
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Unconditional compact domination of the full multiplicity-weighted zero
family in the actual integrated Perron source. No RH or zero-density estimate
is used: the open critical strip and summability at one physical height suffice. -/
namespace RHOcticPush.BoxPerron
open Real Set MeasureTheory
set_option maxHeartbeats 0

lemma zero_re_bounds (ρ : IEANTN.RHSmoothing.Zero) :
    0 < (ρ : ℂ).re ∧ (ρ : ℂ).re < 1 := ρ.property.1

lemma norm_zeroPrimitive (x : ℝ) (ρ : IEANTN.RHSmoothing.Zero) :
    ‖zeroPrimitive x ρ‖ =
      Real.exp (((ρ : ℂ).re + 1) * Real.log x) * ‖zeroCoefficient ρ‖ := by
  simp [zeroPrimitive, norm_mul, Complex.norm_exp, Complex.mul_re]

/-- Absolute convergence at the single ordinary point2 already supplies a
summable coefficient family for every later compact transport interval. -/
theorem zeroCoefficient_summable (h : SourceIntegratedPsi) :
    Summable zeroCoefficient := by
  obtain ⟨C, hC⟩ := h
  apply (hC 2 (by norm_num)).1.norm.of_norm_bounded
  intro ρ
  rw [norm_zeroPrimitive]
  have he : 1 ≤ Real.exp (((ρ : ℂ).re + 1) * Real.log 2) := by
    apply Real.one_le_exp
    exact mul_nonneg (by linarith [(zero_re_bounds ρ).1]) (Real.log_nonneg (by norm_num))
  exact le_mul_of_one_le_left (norm_nonneg _) he

/-- Uniform domination on EVERY compact positive physical interval; this is
what licenses all-zero integration without an RH-only shortcut. -/
theorem zeroPrimitive_uniform {a b : ℝ} (ha : 1 < a) (hab : a ≤ b)
    (x : ℝ) (hx : x ∈ Icc a b) (ρ : IEANTN.RHSmoothing.Zero) :
    ‖zeroPrimitive x ρ‖ ≤ Real.exp (2 * Real.log b) * ‖zeroCoefficient ρ‖ := by
  rw [norm_zeroPrimitive]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  have hx1 : 1 ≤ x := ha.le.trans hx.1
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hx1
  have hb0 : 0 < b := hx0.trans_le hx.2
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hlog : Real.log x ≤ Real.log b := Real.log_le_log hx0 hx.2
  calc
    ((ρ : ℂ).re + 1) * Real.log x ≤ 2 * Real.log x :=
      mul_le_mul_of_nonneg_right (by linarith [(zero_re_bounds ρ).2]) hlogx
    _ ≤ 2 * Real.log b := by linarith

theorem zeroPrimitive_summable {a b : ℝ} (h : SourceIntegratedPsi)
    (ha : 1 < a) (hab : a ≤ b) {x : ℝ} (hx : x ∈ Icc a b) :
    Summable (zeroPrimitive x) :=
  ((zeroCoefficient_summable h).norm.mul_left (Real.exp (2 * Real.log b))).of_norm_bounded
    (zeroPrimitive_uniform ha hab x hx)

#print axioms zeroCoefficient_summable
#print axioms zeroPrimitive_uniform
#print axioms zeroPrimitive_summable
end RHOcticPush.BoxPerron
