import AbsTrapezoid
import OcticDerivativeBounds
namespace RHOcticPush.Moments
open Real Set MeasureTheory
set_option maxHeartbeats 0

lemma quadratic_convex {f f' f'' : ℝ → ℝ} {M : ℝ}
    (h1 : ∀ x, HasDerivAt f (f' x) x) (h2 : ∀ x, HasDerivAt f' (f'' x) x)
    (hM : ∀ x, -M ≤ f'' x) :
    ConvexOn ℝ univ (fun x => f x + M / 2 * x ^ 2) := by
  have hq1 (x : ℝ) : HasDerivAt (fun x => f x + M / 2 * x ^ 2)
      (f' x + M * x) x := by
    apply ((h1 x).add ((hasDerivAt_id x).pow 2 |>.const_mul (M / 2))).congr_deriv
    dsimp
    ring
  have hq2 (x : ℝ) : HasDerivAt (fun x => f' x + M * x) (f'' x + M) x := by
    apply ((h2 x).add ((hasDerivAt_id x).const_mul M)).congr_deriv
    ring
  exact convexOn_of_hasDerivWithinAt2_nonneg convex_univ
    (fun x _ => (hq1 x).continuousAt.continuousWithinAt)
    (fun x _ => (hq1 x).hasDerivWithinAt)
    (fun x _ => (hq2 x).hasDerivWithinAt)
    (fun x _ => by linarith [hM x])

theorem octic_abs_trapezoid {a b : ℝ} (hab : a < b) :
    (∫ y in a..b, |EvenKernel.transform 4 y|) ≤
      (b-a)/2 * (|EvenKernel.transform 4 a|+|EvenKernel.transform 4 b|) +
      (16/33)*(b-a)^3/12 := by
  have hp := quadratic_convex DerivativeBounds.transform_hasDerivAt
    DerivativeBounds.first_hasDerivAt
    (fun x => (abs_le.mp (DerivativeBounds.second_abs_le x)).1)
  have hm := quadratic_convex (M := (16/33 : ℝ)) (fun x => (DerivativeBounds.transform_hasDerivAt x).neg)
    (fun x => (DerivativeBounds.first_hasDerivAt x).neg)
    (fun x => by linarith [(abs_le.mp (DerivativeBounds.second_abs_le x)).2])
  exact abs_trapezoid hab
    (continuous_iff_continuousAt.mpr fun x =>
      (DerivativeBounds.transform_hasDerivAt x).continuousAt) hp hm

#print axioms octic_abs_trapezoid
end RHOcticPush.Moments
