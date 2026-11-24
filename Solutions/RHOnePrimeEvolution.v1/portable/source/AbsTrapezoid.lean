import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! Absolute-value quadrature without assuming that abs(f) is twice differentiable.
The convex quadratic perturbations follow from a genuine bound on f'', and are
proved separately for each actual integrand. This file supplies no numeric cap. -/
namespace RHOcticPush.Moments
open Real Set MeasureTheory
set_option maxHeartbeats 0

lemma abs_chord {f : ℝ → ℝ} {M a b t : ℝ} (hab : a < b) (ht : t ∈ Icc a b)
    (hp : ConvexOn ℝ univ (fun x => f x + M / 2 * x ^ 2))
    (hm : ConvexOn ℝ univ (fun x => -f x + M / 2 * x ^ 2)) :
    |f t| ≤ (b - t) / (b - a) * |f a| + (t - a) / (b - a) * |f b| +
      M / 2 * (t - a) * (b - t) := by
  let α := (b - t) / (b - a)
  let β := (t - a) / (b - a)
  have h0 : 0 < b - a := sub_pos.mpr hab
  have ha : 0 ≤ α := div_nonneg (sub_nonneg.mpr ht.2) h0.le
  have hb : 0 ≤ β := div_nonneg (sub_nonneg.mpr ht.1) h0.le
  have hs : α + β = 1 := by dsimp [α, β]; field_simp; ring
  have hx : α * a + β * b = t := by dsimp [α, β]; field_simp; ring
  have hq : M / 2 * (α * a ^ 2 + β * b ^ 2 - t ^ 2) =
      M / 2 * (t - a) * (b - t) := by
    dsimp [α, β]
    field_simp
    ring
  have hplus := hp.2 (mem_univ a) (mem_univ b) ha hb hs
  have hminus := hm.2 (mem_univ a) (mem_univ b) ha hb hs
  simp only [smul_eq_mul] at hplus hminus
  rw [hx] at hplus hminus
  have hpa := mul_le_mul_of_nonneg_left (le_abs_self (f a)) ha
  have hpb := mul_le_mul_of_nonneg_left (le_abs_self (f b)) hb
  have hma := mul_le_mul_of_nonneg_left (neg_le_abs (f a)) ha
  have hmb := mul_le_mul_of_nonneg_left (neg_le_abs (f b)) hb
  apply abs_le.mpr
  constructor <;> change _ ≤ _
  · nlinarith
  · nlinarith

noncomputable def chordMajorant (f : ℝ → ℝ) (M a b t : ℝ) : ℝ :=
  (b - t) / (b - a) * |f a| + (t - a) / (b - a) * |f b| +
    M / 2 * (t - a) * (b - t)

noncomputable def chordPrimitive (f : ℝ → ℝ) (M a b t : ℝ) : ℝ :=
  |f a| / (b - a) * (b * t - t ^ 2 / 2) +
    |f b| / (b - a) * (t ^ 2 / 2 - a * t) +
    M / 2 * ((a + b) * t ^ 2 / 2 - t ^ 3 / 3 - a * b * t)

lemma chordPrimitive_derivative (f : ℝ → ℝ) (M a b t : ℝ) :
    HasDerivAt (chordPrimitive f M a b) (chordMajorant f M a b t) t := by
  have hi := hasDerivAt_id t
  have h2 := hi.pow 2
  have h3 := hi.pow 3
  have hA := ((hi.const_mul b).sub (h2.div_const 2)).const_mul (|f a| / (b - a))
  have hB := ((h2.div_const 2).sub (hi.const_mul a)).const_mul (|f b| / (b - a))
  have hM := ((((h2.const_mul (a + b)).div_const 2).sub
    (h3.div_const 3)).sub (hi.const_mul (a * b))).const_mul (M / 2)
  apply ((hA.add hB).add hM).congr_deriv
  dsimp [chordMajorant]
  norm_num
  ring

lemma chord_integral (f : ℝ → ℝ) {M a b : ℝ} (hab : a < b) :
    (∫ t in a..b, chordMajorant f M a b t) =
      (b - a) / 2 * (|f a| + |f b|) + M * (b - a) ^ 3 / 12 := by
  have hc : Continuous (chordMajorant f M a b) := by
    unfold chordMajorant
    fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => chordPrimitive_derivative f M a b t) (hc.intervalIntegrable a b)
  rw [h]
  unfold chordPrimitive
  field_simp [show b - a ≠ 0 from (sub_pos.mpr hab).ne']
  ring

/-- A sound endpoint trapezoid upper bound for the actual absolute integrand,
including cells crossing a zero of f. No derivative of abs(f) occurs. -/
theorem abs_trapezoid {f : ℝ → ℝ} {M a b : ℝ} (hab : a < b) (hc : Continuous f)
    (hp : ConvexOn ℝ univ (fun x => f x + M / 2 * x ^ 2))
    (hm : ConvexOn ℝ univ (fun x => -f x + M / 2 * x ^ 2)) :
    (∫ t in a..b, |f t|) ≤
      (b - a) / 2 * (|f a| + |f b|) + M * (b - a) ^ 3 / 12 := by
  have hmajor : Continuous (chordMajorant f M a b) := by
    unfold chordMajorant
    fun_prop
  calc
    _ ≤ ∫ t in a..b, chordMajorant f M a b t :=
      intervalIntegral.integral_mono_on hab.le (hc.abs.intervalIntegrable a b)
        (hmajor.intervalIntegrable a b) (fun t ht => abs_chord hab ht hp hm)
    _ = _ := chord_integral f hab

#print axioms abs_chord
#print axioms abs_trapezoid
end RHOcticPush.Moments
